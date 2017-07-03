#define PROFILE_POINT __attribute__((noinline))

namespace {
enum OccType {
  OccReal,
  OccPhi,
  OccExit,
};

struct Occurrence {
  DomTreeNode *Node;
  unsigned LocalNum;
  const OccType Type;

  Occurrence(DomTreeNode *Node, unsigned LocalNum, OccType Type)
      : Node(Node), LocalNum(LocalNum), Type(Type) {}

  BasicBlock &getBlock() const { return *Node->getBlock(); }

  unsigned in() const { return Node->getDFSNumIn(); }

  unsigned out() const { return Node->getDFSNumOut(); }

  bool dominates(const Occurrence &Other) const {
    return in() <= Other.in() && Other.out() <= out();
  }
};

struct RealOcc;

struct PhiOcc final : public Occurrence {
  struct PhiUse {
    PhiOcc *User;
    size_t OpIdx;
  };

  struct Operand {
    Occurrence *Occ;
    BasicBlock *Pred;
  };

  PHINode *P = nullptr;
  std::vector<Operand> Defs;
  std::vector<BasicBlock *> Unavail;
  std::vector<PhiUse> PhiUses;
  bool DownSafe = true;
  bool CanBeAvail = true;
  bool FullyAvail = true;

  // LocalNum is set to 0 to ensure that when sorted in DPO, phi occurrences
  // precede all other occurrences in the same block.
  PhiOcc(DomTreeNode &N, Occurrence &FirstOperand, BasicBlock &OpBlock)
      : Occurrence{&N, 0, OccPhi} {
    addOperand(FirstOperand, OpBlock);
  }

  PhiOcc(PHINode &P, const DominatorTree &DT)
      : Occurrence{*DT.getNode(P.getParent()), 0, OccPhi}, P(&P) {}

  void addOperand(Occurrence &Occ, BasicBlock &Block) {
    Defs.push_back({&Occ, &Block});
    // Add ourselves to Occ's uses if it's a PhiOcc.
    if (auto *P = dyn_cast<PhiOcc>(&Occ))
      P->addUse(*this, Defs.size() - 1);
  }

  void addUse(PhiOcc &P, unsigned OpIdx) { PhiUses.push_back({&P, OpIdx}); }

  void addUse(RealOcc &R) { Uses.emplace_back(&R); }

  void verify(const DominatorTree &DT) const;

  raw_ostream &print(raw_ostream &Out) const {
    Out << "PhiOcc @ " << getBlock().getName();
    return Out;
  }

  static bool classof(Occurrence *Occ) { return Occ->Type == OccPhi; }
  static bool classof(const Occurrence *Occ) { return Occ->Type == OccPhi; }
};

struct RealOcc final : public Occurrence {
  PointerIntPair<Occurrence *, 1, bool> Def;
  PointerUnion<Instruction *, StoreInst *> I;
  unsigned UseCount = 0;

  RealOcc(DomTreeNode &N, unsigned LocalNum, Instruction &I_, bool NewVers)
      : Occurrence{&N, LocalNum, OccReal}, Def(nullptr, NewVers) {
    if (auto *SI = dyn_cast<StoreInst>(&I_))
      I = SI;
    else
      I = &I_;
  }

  void setDef(Occurrence &Occ) {
    Def.setPointer(&Occ);
    if (auto *P = dyn_cast<PhiOcc>(&Occ))
      P->addUse(*this);
  }

  Occurrence *getDef() const { return Def.getPointer(); }

  bool isNewVersion() const { return Def.getInt(); }

  PointerUnion<Instruction *, StoreInst *> &getInst() { return I; }

  raw_ostream &print(raw_ostream &Out) const {
    if (auto *II = I.dyn_cast<Instruction *>())
      Out << "RealOcc @ "
          << ": " << *II;
    else if (auto *II = I.dyn_cast<StoreInst *>())
      Out << "RealOcc @ "
          << ": " << *II;
    return Out;
  }

  static bool classof(Occurrence *Occ) { return Occ->Type == OccReal; }
  static bool classof(const Occurrence *Occ) { return Occ->Type == OccReal; }
};

// Exit occurrences live at bottom of exit blocks. A phi is down-unsafe if it
// has a CFG path to an ExitOcc that doesn't cross a real Occurrence.
struct ExitOcc final : public Occurrence {
  // Exit occs live at the bottom of their (exit) blocks; set LocalNum
  // accordingly.
  ExitOcc(DomTreeNode &N) : Occurrence{&N, -1u, OccExit} {}

  raw_ostream &print(raw_ostream &Out) const {
    Out << "ExitOcc @ bottom of " << getBlock().getName();
    return Out;
  }

  static bool classof(Occurrence *Occ) { return Occ->Type == OccExit; }
  static bool classof(const Occurrence *Occ) { return Occ->Type == OccExit; }
};

// PiggyBank from Sreedhar and Gao 1994. This structure fulfills the same
// purpose as the priority_queue in IDFCalculator but does so with amortized
// constant time per insertion and deletion.
struct PiggyBank {
  using Node = Occurrence *;
  // Indexes into Banks.
  using NodeRef = std::pair<unsigned, unsigned>;

  // Defs, sorted by dom tree depth, for which phis will be placed.
  std::vector<std::vector<Node>> Banks;
  unsigned CurrentLevel;

  PiggyBank(unsigned TreeHeight)
      : Banks(TreeHeight), CurrentLevel(TreeHeight - 1) {}

  bool empty() {
    for (; CurrentLevel > 0; CurrentLevel -= 1)
      if (!Banks[CurrentLevel].empty())
        return false;
    return Banks[0].empty();
  }

  Node pop() {
    assert(!Banks[CurrentLevel].empty() &&
           "CurrentLevel should point to endmost non-empty bank.");
    Node N = Banks[CurrentLevel].back();
    Banks[CurrentLevel].pop_back();
    return N;
  }

  NodeRef push(Occurrence &Occ, unsigned Level) {
    Banks[Level].push_back(&Occ);
    return {Level, Banks[Level].size() - 1};
  }

  Node &operator[](NodeRef Ref) { return Banks[Ref.first][Ref.second]; }
};

// This is essentially ForwardIDFCalculator, with additional functionality that
// pushes operands into phis as they are placed. Doing this obviates the need
// for a full DPO walk during renaming.
struct PlaceAndFill {
  const DominatorTree &DT;
  PiggyBank DefQ;
  // ^ Imposes an order on defs so that phis are inserted from highest- to
  // lowest-ranked, thus preventing dom sub-tree re-traversals.
  DenseMap<const DomTreeNode *, unsigned> Levels;
  // ^ Maps eeach basic block to its depth in the dom tree.
  DenseMap<const BasicBlock *, PiggyBank::NodeRef> Defs;
  DenseSet<const DomTreeNode *> Visited;
  std::vector<DomTreeNode *> SubtreeStack;
  // ^ Stack for visiting def node subtrees in pre-order.

  PlaceAndFill(const DominatorTree &DT, unsigned NumBlocks) : DT(DT), DefQ(0) {
    // Prevent re-allocs.
    Levels.reserve(NumBlocks);
    Defs.reserve(NumBlocks);
    Visited.reserve(NumBlocks);
    SubtreeStack.reserve(NumBlocks);

    unsigned Height = 0;
    for (auto DFI = df_begin(DT.getRootNode()); DFI != df_end(DT.getRootNode());
         ++DFI) {
      Levels[*DFI] = DFI.getPathLength() - 1;
      Height = std::max(Height, DFI.getPathLength());
    }

    DefQ = PiggyBank(Height);
  }

  void addDef(Occurrence &Occ) {
    // If there are multiple definitions in a block, keep only the latest
    // because that is the one exposed to phis on the block's DF.
    auto InsPair = Defs.insert({&Occ.getBlock(), {0, 0}});
    if (InsPair.second)
      // First def of this block. Push it into the PiggyBank.
      InsPair.first->second = DefQ.push(Occ, Levels.find(Occ.Node)->second);
    else if (DefQ[InsPair.first->second]->LocalNum < Occ.LocalNum)
      // Occ is later in the block than the previously inserted def.
      DefQ[InsPair.first->second] = &Occ;
  }

  using PhiMap = DenseMap<const BasicBlock *, PhiOcc>;

  void calculate(PhiMap &Phis) {
    while (!DefQ.empty())
      visitSubtree(DefQ.pop(), DefQ.CurrentLevel, Phis);
  }

  void clear() {
    assert(DefQ.empty() &&
           "All defs should have been popped after calculate().");
    Defs.clear();
    Visited.clear();
  }

private:
  // Search CurDef's dom subtree for J-edges. CurDef's DF is exactly the set of
  // targets of all J-edges whose shadow contains CurDef.
  void visitSubtree(PiggyBank::Node CurDef, unsigned CurDefLevel,
                    PhiMap &Phis) {
    assert(SubtreeStack.empty());
    SubtreeStack.push_back(CurDef->Node);
    Visited.insert(CurDef->Node);

    while (!SubtreeStack.empty()) {
      DomTreeNode &SubNode = *SubtreeStack.back();
      for (BasicBlock *Succ : successors(SubNode.getBlock())) {
        DomTreeNode &SuccNode = *DT.getNode(Succ);
        unsigned SuccLevel;

        // Skip if it's a dom tree edge (not a J-edge).
        if (SuccNode.getIDom() == &SubNode ||
            (SuccLevel = Levels.find(&SuccNode)->second) > CurDefLevel)
          continue;

        // SuccNode belongs in CurDef's DF. Check if a phi has been placed.
        PhiOcc NewPhi(SuccNode, *CurDef, CurDef->getBlock());
        auto InsPair = Phis.insert({Succ, std::move(NewPhi)});
        if (!InsPair.second)
          // Already inserted a phi into this block, which means that its DF+
          // has already been visited.
          InsPair.first->second.addOperand(*CurDef, CurDef->getBlock());
        else if (!Defs.count(Succ))
          // New phi was inserted, meaning that this is the first encounter of
          // this DF member. Recurse on its DF.
          DefQ.push(InsPair.first->second, SuccLevel);
      }

      // Continue dom subtree DFS.
      for (DomTreeNode *Child : SubNode)
        if (Visited.insert(Child).second)
          SubtreeStack.push_back(Child);

      SubtreeStack.pop_back();
    }
  }
};

// RAII wrapper that ensures its PlaceAndFill is cleared.
struct ClearGuard {
  PlaceAndFill &Inner;

  ClearGuard(PlaceAndFill &Inner) : Inner(Inner) {}
  ~ClearGuard() { Inner.clear(); }
  auto addDef(RealOcc &Occ) -> decltype(Inner.addDef(Occ)) {
    return Inner.addDef(Occ);
  }
  auto calculate(PlaceAndFill::PhiMap &Phis) -> decltype(Inner.calculate()) {
    return Inner.calculate(Phis);
  }
};

template <typename Entry, size_t N> struct DPOStack {
  SmallVector<Entry *, N> Inner;
  void popUntilDFSScope(Entry &E) {
    while (!Inner.empty() && !Inner.back()->dominates(E))
      Inner.pop_back();
  }
  void push(Entry &E) { Inner.push_back(&E); }
  Entry *top() { return Inner.empty() ? nullptr : Inner.back(); }
};

raw_ostream &operator<<(raw_ostream &O, const Occurrence &Occ) {
  if (auto *R = dyn_cast<RealOcc>(&Occ))
    return R->print(O);
  else if (auto *P = dyn_cast<PhiOcc>(&Occ))
    return P->print(O);
  else if (auto *E = dyn_cast<ExitOcc>(&Occ))
    return E->print(O);
  else
    llvm_unreachable("Invalid occurrence type.");
}

void PhiOcc::verify(const DominatorTree &DT) const {
  DEBUG(dbgs() << "Verifying " << *this << "\n");
  for (const PhiOcc::Operand &Op : Defs) {
    assert(Op.Pred);
    assert(Op.Occ && "Expected an operand.");
    assert(DT.dominates(Op.Occ->Node, DT.getNode(Op.Pred)));
    assert(Op.Occ->Node == Node || !DT.dominates(Op.Occ->Node, Node));
  }
}

// A PhiOcc is fully avail iff each of its operands are dominated by a cong
// class member (a RealOcc) or a fully avail PhiOcc. The inverse of this is that
// at least one operand is un-dominated by either of those (a _|_ operand in
// SSAPRE parlance), or dominated by a phi that is known to be non-fully avail.
void computeFullyAvail(DenseMap<const BasicBlock *, PhiOcc> &Phis) {
  SmallVector<PhiOcc *, 32> Stack;
  auto pushUses = [&](PhiOcc &Phi) {
    Phi.FullyAvail = false;
    for (PhiOcc::PhiUse &Use : Phi.PhiUses)
      if (Use.User->FullyAvail)
        Stack.push_back(Use.User);
  };

  for (auto Pair : Phis) {
    const BasicBlock *BB = Pair.first;
    PhiOcc &Phi = Pair.second;
    // Will at least one of Phi's operands be _|_?
    if (Phi.FullyAvail &&
        std::distance(pred_begin(BB), pred_end(BB)) < Phi.Defs.size()) {
      // Yes, so this phi and its direct users will themselves be non-fully
      // avail. Propagate false by DFS.
      pushUses(Phi);
      while (!Stack.empty())
        pushUses(*Stack.pop_back_val());
    }
  }
}

// This will find and insert phis at all fully available sites of Cong, which
// are join points where each predecessor is dominated by a Cong member.
bool NewGVN::insertFullyAvailPhis(CongruenceClass &Cong,
                                  ClearGuard IDFCalc) PROFILE_POINT {
  if (Cong.size() <= 1 || !isa<BasicExpression>(Cong.getDefiningExpr()))
    // No possible fully redundant sites in singleton classes.
    return false;

  // Place possible phi markers at DF+ of all Cong members. As they are placed,
  // each marker will be filled phi operands.
  std::vector<RealOcc> RealOccs;
  RealOccs.reserve(Cong.size());
  DenseMap<const BasicBlock *, PhiOcc> Phis;

  for (Value *V : Cong) {
    if (auto *PN = dyn_cast<PHINode>(V)) {
      // PN is an existing phi node in the congruence class. Wrap it in a PhiOcc
      // and toss it in with the other phis. PlaceAndFill will fill this PhiOcc
      // with Occurrence operands that correspond to the PHINode's.
      auto InsPair = Phis.insert({PN->getParent(), PhiOcc(*PN, *DT)});
      IDFCalc.addDef(InsPair->second);
    } else {
      Instruction *I = cast<Instruction>(V);
      RealOccs.emplace_back(*DT->getNode(I->getParent()), InstrToDFSNum(I), *I,
                            I == Cong.getLeader());
      IDFCalc.addDef(RealOccs.back());
    }
  }

  for (auto &P : Phis)
    // Verify that PlaceAndFill did its job correctly.
    P.second.verify(*DT);
  computeFullyAvail(Phis);

  // Materialize fully available PhiOccs into PHINodes and add into the
  // congruence class.
  for (auto &P : Phis) {
    PhiOcc &Phi = P.second;
    if (Phi.FullyAvail)
      if (!Phi.P)
        Cong.insert(Phi.P = IRBuilder<>(getBlock(), getBlock()->begin())
                                .CreatePHI(T, Phi.Defs.size()));
  }

  // Set incoming values of newly inserted PHINodes.
  for (auto &P : Phis) {
    PhiOcc &Phi = P.second;
    // Could be a phi already existing in Cong. Those would already have
    // incoming values. Skip.
    if (Phi.FullyAvail && Phi.P->getNumIncomingValues == 0) {
      for (const PhiOcc::Operand &Op : Phi.Defs) {
        if (RealOcc *R = dyn_cast<RealOcc>(Op.Occ)) {
          if (StoreInst *SI = R->getInst().dyn_cast<StoreInst *>())
            Phi.P->addIncoming(SI->getValueOperand());
          else
            Phi.P->addIncoming(R->getInst().dyn_cast<Instruction *>());
        } else
          Phi.P->addIncoming(cast<PhiOcc>(Op.Occ.P));
      }
    }
  }
  return true;
}
