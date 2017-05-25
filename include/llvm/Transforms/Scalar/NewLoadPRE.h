enum OccType {
  OccReal,
  OccPhi,
  OccExit,
};

struct Occurrence {
  DomTreeNode *Node;
  unsigned LocalNum;
  OccType Type;

  BasicBlock &getBlock() const { return *Node->getBlock(); }

  unsigned in() const { return Node->getDFSNumIn(); }

  unsigned out() const { return Node->getDFSNumOut(); }
};

struct RealOcc final : public Occurrence {
  Occurrence *Def = nullptr;
  PointerUnion<Instruction *, StoreInst *> I;

  RealOcc(DomTreeNode &N, unsigned LocalNum, Instruction &I_)
      : Occurrence{&N, LocalNum, OccReal} {
    if (auto *SI = dyn_cast<StoreInst>(&I))
      I = SI;
    else
      I = I_;
  }

  static bool classof(const Occurrence &Occ) { return Occ.Type == OccReal; }
};

struct PhiOcc final : public Occurrence {
  struct PhiUse {
    PhiOcc *P;
    size_t OpIdx;
  };

  struct Operand {
    Occurrence *Occ;
    BasicBlock *Pred;
  };

  std::vector<Operand> Defs;
  std::vector<BasicBlock *> Unavail;
  std::vector<RealOcc *> Uses;
  std::vector<PhiUse> PhiUses;

  // LocalNum is set to 0 to ensure that when sorted in DPO, phi occurrences
  // precede all other occurrences in the same block.
  PhiOcc(DomTreeNode &N, Occurrence &FirstOperand, BasicBlock &OpBlock)
      : Occurrence{&N, 0, OccPhi}, Defs(1) {
    addOperand(FirstOperand, OpBlock);
  }

  void addOperand(Occurrence &Occ, BasicBlock &Block) {
    Defs.emplace_back(&Occ, &Block);
    // Add ourselves to Occ's uses if it's a PhiOcc.
    if (auto *P = dyn_cast<PhiOcc>(&Occ))
      P->addUse(*this, Defs.size() - 1);
  }

  void addUse(PhiOcc &P, unsigned OpIdx) { PhiUse.emplace_back(&P, OpIdx); }

  static bool classof(const Occurrence &Occ) { return Occ.Type == OccPhi; }
};

struct ExitOcc final : public Occurrence {
  // Exit occs live at the bottom of their (exit) blocks; set LocalNum
  // accordingly.
  ExitOcc(DomTreeNode &N) : Occurrence{&N, -1u, OccExit} {}
};

// PiggyBank from Sreedhar and Gao 1994. This structure fulfills the same
// purpose as the priority_queue in IDFCalculator but does so with amortized
// constant time per insertion and deletion.
struct PiggyBank {
  using Node = Occurrence *;

  std::vector<Node> Banks;
  unsigned CurrentLevel;

  PiggyBank(unsigned TreeHeight) : Banks(TreeHeight) {}

  std::pair<const Node &, unsigned> top() const {
    assert(!Banks[CurrentLevel].empty() &&
           "CurrentLevel should point to endmost non-empty bank.");
    return {Banks[CurrentLevel].back(), CurrentLevel};
  }

  bool empty() const { return CurrentLevel == 0 && Banks[0].empty(); }

  void pop() {
    assert(!Banks[CurrentLevel].empty() &&
           "CurrentLevel should point to endmost non-empty bank.");
    Banks[CurrentLevel].pop_back();
    setCurrentLevel(false);
  }

  Node &push(Occurrence &Occ, unsigned Level) {
    Banks[Level].push_back(&Occ);
    return Banks[Level].back();
  }

private:
  void setCurrentLevel(bool Init = true) {
    for (CurrentLevel = Init ? Banks.size() : CurrentLevel;
         CurrentLevel > 0 && Banks[CurrentLevel].empty();)
      CurrentLevel -= 1;
  }
};

// This is essentially ForwardIDFCalculator, with additional functionality that
// pushes operands into phis as they are placed. Doing this obviates the need
// for a full DPO walk during renaming.
struct PlaceAndFill {
  PiggyBank DefQ;
  // ^ Imposes an order on defs so that phis are inserted from highest- to
  // lowest-ranked, thus preventing dom sub-tree re-traversals.
  DenseMap<DomTreeNode *, unsigned> Levels;
  // ^ Maps eeach basic block to its depth in the dom tree.
  DenseMap<const BasicBlock *, PiggyBank::Node *> Defs;
  DenseSet<const DomTreeNode *> Visited;
  std::vector<DomTreeNode *> SubtreeStack;
  // ^ Stack for visiting def node subtrees in pre-order.

  PlaceAndFill(const DominatorTree &DT, unsigned NumBlocks) : Defs(0) {
    // Prevent re-allocs.
    Levels.reserve(NumBlocks);
    Defs.reserve(NumBlocks);
    Visited.reserve(NumBlocks);
    SubtreeStack.reserve(NumBlocks);

    unsigned Height = 0;
    for (auto DFI = df_begin(DT.getRootNode()); DFI != df_end(DT.getRootNode());
         ++DFI) {
      DomLevels[*DFI] = DFI.getPathLength();
      Height = std::max(Height, DFI.getPathLength());
    }

    DefQ = PiggyBank(Height);
  }

  void addDef(RealOcc &Occ) {
    // If there are multiple definitions in a block, keepy only the latest
    // because that is the one exposed to phis on the block's DF.
    auto InsPair = Defs.insert({Occ.getBlock(), nullptr});
    if (InsPair.second)
      // First encounter with this block. Push it into the PiggyBank.
      *InsPair.first = DefQ.push(Occ, *Levels.find(Occ.getBlock()));
    else if ((*InsPair.first)->LocalNum < Occ.LocalNum)
      // Occ is later in the block than the previously inserted def.
      *InsPair.first = &Occ;
  }

  using PhiMap = DenseMap<const BasicBlock *, PhiOcc>;

  PhiMap calculate() {
    PhiMap Phis;
    while (!DefQ.empty()) {
      visitSubtree(DefQ.top().first, DefQ.top().second, Phis);
      DefQ.pop();
    }
    return Phis;
  }

  void clear() {
    assert(DefQ.empty() &&
           "All defs should have been popped after calculate().");
    Defs.clear(NumBlocks);
    Visited.clear(NumBlocks);
  }

private:
  // Search CurDef's dom subtree for J-edges. CurDef's DF is exactly the set of
  // targets of all J-edges whose shadow contains CurDef.
  void visitSubtree(const PiggyBank::Node &CurDef, unsigned CurDefLevel,
                    PhiMap &Phis) {
    assert(SubtreeStack.empty());
    SubtreeStack.push_back(&CurDef);
    Visited.insert(&CurDef);

    while (!SubtreeStack.empty()) {
      DomTreeNode &SubNode = *SubtreeStack.back();
      for (BasicBlock *Succ : successors(SubNode.getBlock())) {
        DomTreeNode &SuccNode = DT.getNode(Succ);
        unsigned SuccLevel;

        // Skip if it's a dom tree edge (not a J-edge).
        if (SuccNode->getIDom() == SubNode &&
            (SuccLevel = *Levels.find(SuccNode)) > CurDefLevel)
          continue;

        // SuccNode belongs in CurDef's DF. Check if a phi has been placed.
        PhiOcc NewPhi(*SuccNode, CurDef, CurDef->getBlock());
        auto InsPair = Phis.insert({Succ, std::move(NewPhi)});
        if (InsPair.second)
          // New phi was inserted, meaning that this is the first encounter
          // of this DF member. Recurse on its DF.
          DefQ.push(*InsPair.first, SuccLevel);
        else
          // Already inserted a phi into this block, which means that its DF+
          // has already been visited.
          InsPair.first->addOperand(CurDef, CurDef->getBlock());
      }

      // Continue dom subtree DFS.
      for (DomTreeNode *Child : SubNode)
        if (Visited.insert(Child).second)
          SubtreeStack.push_back(Child);
    }
  }
};

// Enaures that PlaceAndFill is cleared between successive scalarPRE calls.
struct ClearGuard {
  PlaceAndFill Inner;

  ~ClearGuard() { Inner.clear(); }
  void addDef(RealOcc &Occ) { return Inner.addDef(Occ); }
  void calculate() { return Inner.calculate(); }
};

bool NewGVN::scalarPRE(Function &F, CongruenceClass &Cong, ClearGuard IDFCalc) {
  std::vector<RealOcc> RealOccs;
  RealOccs.reserve(Cong.size());
  std::vector<Occurrence *> DPOSorted;
  DPOSorted.reserve(Cong.size());

  // Add a real occurrence for each cong member, an exit occurrence for every
  // exit block, and phi occurrences at IDFs of each real occurrence. Sort them
  // together into dominator pre-order and visit each one, keeping a stack of
  // current dominating occurrence.

  // TODO: This only needs to be done once for all cong classes.
  std::vector<ExitOcc> ExitOccs;
  for (BasicBlock &BB : F)
    if (isa<ReturnInst>(BB.getTerminator()) ||
        isa<UnreachableInst>(BB.getTerminator())) {
      ExitOccs.emplace_back(*DT.getBlock(&BB));
      DPOSorted.push_back(&ExitOccs.back());
    }

  // TODO: Not all cong members should be pushed.
  for (Instruction *I : Cong) {
    RealOccs.emplace_back(*DT.getNode(I->getParent()), *I);
    DPOSorted.push_back(&RealOccs.back());
    IDFCalc.addDef(RealOccs.back());
  }

  DenseMap<const BasicBlock *, PhiOcc> Phis = IDFCalc.calculate();
  DPOSorted.reserve(DPOSorted.size() + Phis.size());
  for (auto &P : Phis)
    DPOSorted.push_back(&P.second);

  std::sorted(DPOSorted.begin(), DPOSorted.end(),
              [](const Occurrence *A, const Occurrence *B) {
                return std::tie(A->in(), B->out(), A->LocalNum) <
                       std::tie(B->in(), A->out(), B->LocalNum);
              });

  // Link up uses to defs and eliminate full redundanciea where ;ossible.
  DPOStack Stack;
  for (Occurrence *Occ : DPOSorted) {
    Stack.popUntilDFSScope(*Occ->Node);

    // TODO: Re-order this from most to least liekly.
    if (auto *Ex = dyn_cast<ExitOcc>(Occ)) {
      // Exit occs are never pushed because they dominate nothing.
      if (auto *P = dyn_cast_or_null<PhiOcc>(Stack.top()))
        P->setUpUnsafe();
    } else if (!Stack.top()) {
      Stack.push(*Occ);
    } else if (auto *R = dyn_cast<RealOcc>(Occ)) {
      if (!Stack.top()) {
        Stack.push if (auto *RDom = dyn_cast<RealOcc>(Stack.top())) {
          // R's cong member is fully dommed by RDom's and thus fully redundant.
          // Don't bother pushing.
          Reds.insert({R, RDom});
        }
        else if (auto *P = dyn_cast<PhiOcc>(Stack.top())) {
        }
      }
      if (Stack.empty())
    }
  }
}
