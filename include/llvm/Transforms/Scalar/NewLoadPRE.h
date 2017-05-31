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

  std::vector<Operand> Defs;
  std::vector<BasicBlock *> Unavail;
  std::vector<RealOcc *> Uses;
  std::vector<PhiUse> PhiUses;
  bool DownSafe = true;
  bool CanBeAvail = true;

  // LocalNum is set to 0 to ensure that when sorted in DPO, phi occurrences
  // precede all other occurrences in the same block.
  PhiOcc(DomTreeNode &N, Occurrence &FirstOperand, BasicBlock &OpBlock)
      : Occurrence{&N, 0, OccPhi} {
    addOperand(FirstOperand, OpBlock);
  }

  void addOperand(Occurrence &Occ, BasicBlock &Block) {
    Defs.push_back({&Occ, &Block});
    // Add ourselves to Occ's uses if it's a PhiOcc.
    if (auto *P = dyn_cast<PhiOcc>(&Occ))
      P->addUse(*this, Defs.size() - 1);
  }

  void addUse(PhiOcc &P, unsigned OpIdx) { PhiUses.push_back({&P, OpIdx}); }

  void addUse(RealOcc &R) { Uses.emplace_back(&R); }

  void resetDownSafe() { DownSafe = false; }

  void resetCanBeAvail() { CanBeAvail = false; }

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
  // ^ Points to the dominating occurrence that makes this RealOcc fully
  // redundant. nullptr means that this isn't redundant to anything. The bool is
  // true iff the instruction that this RealOcc wraps is leader of its cong
  // class.
  PointerUnion<Instruction *, StoreInst *> I;

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
  using NodeRef = std::pair<unsigned, unsigned>;

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

  void addDef(RealOcc &Occ) {
    // If there are multiple definitions in a block, keepy only the latest
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

  PhiMap calculate() {
    PhiMap Phis;
    while (!DefQ.empty())
      visitSubtree(DefQ.pop(), DefQ.CurrentLevel, Phis);
    return Phis;
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

// Enaures that PlaceAndFill is cleared between successive scalarPRE calls.
struct ClearGuard {
  PlaceAndFill &Inner;

  ClearGuard(PlaceAndFill &Inner) : Inner(Inner) {}
  ~ClearGuard() { Inner.clear(); }
  auto addDef(RealOcc &Occ) -> decltype(Inner.addDef(Occ)) {
    return Inner.addDef(Occ);
  }
  auto calculate() -> decltype(Inner.calculate()) { return Inner.calculate(); }
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

// Depth-first propagation of false DownSafe from phi occs to their phi defs.
void propagateDownUnsafe(std::vector<PhiOcc *> &PhiStack,
                         DenseMap<const BasicBlock *, PhiOcc> &Phis) {
  auto pushPhiDefsOf = [&](PhiOcc &P) {
    for (PhiOcc::Operand &Op : P.Defs)
      if (auto *PhiDef = dyn_cast<PhiOcc>(Op.Occ))
        if (PhiDef->DownSafe)
          PhiStack.push_back(PhiDef);
  };

  for (auto &Pair : Phis) {
    PhiOcc &Phi = Pair.second;
    if (!Phi.DownSafe) {
      pushPhiDefsOf(Phi);
      while (!PhiStack.empty()) {
        PhiOcc *P = PhiStack.back();
        PhiStack.pop_back();
        P->resetDownSafe();
        pushPhiDefsOf(*P);
      }
    }
  }
}

// Depth-first propagation of false CanBeAvail from phi occs to their phi users.
void propagateCantBeAvail(std::vector<PhiOcc *> &PhiStack,
                          DenseMap<const BasicBlock *, PhiOcc> &Phis) {
  auto resetAndPushUses = [&](PhiOcc &P) {
    P.resetCanBeAvail();
    for (PhiOcc::PhiUse &Use : P.PhiUses)
      if (Use.User->CanBeAvail && !Use.User->DownSafe)
        PhiStack.push_back(Use.User);
  };

  // If PRE insertion is required by one of a phi's operands, then the
  // corresponding predecessor edge has to be split if critical. And if the edge
  // is critical but can't be split, then insertion isn't possible and renders
  // the phi !CanBeAvail.
  auto critEdgeIssues = [](const PhiOcc &P) {
    return any_of(P.Unavail, [&](const BasicBlock *B) {
      // TODO: do this.
      // return cantPREInsert(*B) || (needsSplit(*B) && cantSplit(*B));
      return false;
    });
  };

  for (auto &Pair : Phis) {
    PhiOcc &Phi = Pair.second;
    if (Phi.CanBeAvail &&
        (!Phi.DownSafe && !Phi.Unavail.empty() || critEdgeIssues(Phi))) {
      resetAndPushUses(Phi);

      while (!PhiStack.empty()) {
        PhiOcc *P = PhiStack.back();
        PhiStack.pop_back();
        resetAndPushUses(*P);
      }
    }
  }
}

bool NewGVN::preClass(Function &F, CongruenceClass &Cong, ClearGuard IDFCalc,
                      std::vector<Occurrence *> ExitOccs) {
  // const DominatorTree &DT = *DT;

  if (Cong.size() <= 1)
    // On singleton classes, PRE's sole possible effect is loop-invariant
    // hoisting. But this is already covered by other loop-hoisting passes.
    return false;

  std::vector<RealOcc> RealOccs;
  RealOccs.reserve(Cong.size());
  // ^ Important: RealOccs must not and should not reallocate.
  std::vector<Occurrence *> &DPOSorted = ExitOccs;
  DPOSorted.reserve(Cong.size() + ExitOccs.size());

  // Add a real occurrence for each cong member, an exit occurrence for every
  // exit block, and phi occurrences at IDFs of each real occurrence (these
  // possible sites of partial redundancy). Then sort the occurrences into the
  // order in which each would be encountered during a pre-order walk of the dom
  // tree.

  // TODO: Not all cong members should be pushed, such as maybe ones with side
  // effects that won't be eliminated regardless of redundancy.
  for (Value *V : Cong) {
    Instruction *I = cast<Instruction>(V);
    RealOccs.emplace_back(*DT->getNode(I->getParent()), InstrToDFSNum(I), *I,
                          I == Cong.getLeader());
    DPOSorted.push_back(&RealOccs.back());
    IDFCalc.addDef(RealOccs.back());
  }

  // Phi occurrences are given operands as they are placed. TODO: Since we'll
  // need to iterate over all phis at several points of this pass, considering
  // copying the values of Phis to a separate vector.
  DenseMap<const BasicBlock *, PhiOcc> Phis = IDFCalc.calculate();
  DPOSorted.reserve(DPOSorted.size() + Phis.size());
  for (auto &P : Phis) {
    P.second.verify(*DT);
    DPOSorted.push_back(&P.second);
  }

  std::sort(DPOSorted.begin(), DPOSorted.end(), [](const Occurrence *A,
                                                   const Occurrence *B) {
    unsigned ain = A->in(), bin = B->in(), aout = A->out(), bout = B->out();
    return std::tie(ain, bout, A->LocalNum) < std::tie(bin, aout, B->LocalNum);
  });

  // Link uses to defs and eliminate full redundancies wherever possible. This
  // is just sparsified SSA renaming.
  DPOStack<Occurrence, 32> Stack;
  SmallVector<RealOcc *, 32> ProbablyDead;
  for (Occurrence *Occ : DPOSorted) {
    assert(Occ);
    Stack.popUntilDFSScope(*Occ);

    // TODO: Re-order this from most to least likely.
    //
    // Possibilities:
    //
    // tos:           real    phi
    // cur:
    // real           fre     set def, add real use
    // real, leader   [1]     set down-unsafe
    // exit           [2]     set down-unsafe
    // phi            fre     fre
    //
    // [1]: Not possible for a congruence leader to be dominated by another
    // class member.
    // [2]: Exit occurrences have no effect when exposed to real occurrences.

    // Check the occurrence type of the top of stack.
    if (!Stack.top()) {
      // Nothing dominates Occ, so the only thing left is to push it onto the
      // stack. Exit occs are never pushed because exit blocks dominate nothing.
      if (!isa<ExitOcc>(Occ))
        Stack.push(*Occ);

    } else if (auto *PDom = dyn_cast<PhiOcc>(Stack.top())) {
      if (auto *R = dyn_cast<RealOcc>(Occ)) {
        if (R->isNewVersion())
          PDom->resetDownSafe();
        else
          R->setDef(*PDom);
        Stack.push(*R);
      } else if (auto *P = dyn_cast<PhiOcc>(Occ)) {
        Stack.push(*P);
      } else if (auto *Ex = dyn_cast<ExitOcc>(Occ)) {
        // PDom is directly exposed to an exit and therefore down-unsafe.
        PDom->resetDownSafe();
      } else
        llvm_unreachable("Unexpected occurrence type.");

    } else if (auto *RDom = dyn_cast<RealOcc>(Stack.top())) {
      // Everything dominated by a real occurrence is fully redundant.

      if (auto *R = dyn_cast<RealOcc>(Occ)) {
        assert(!R->isNewVersion() && "R is marked new version and thus the "
                                     "congruence class leader with the lowest "
                                     "DPO number, yet it's somehow dominated "
                                     "by another member.");
        // R is fully redundant to RDom. Don't bother pushing onto the renaming
        // stack because it's probably dead if it has no side effects, but do
        // set its def because its phi operand uses need to be updated to RDom
        // (later).
        R->setDef(*RDom);

        // Mark its deadness. Quickly short-circuit if a store (which trivially
        // has side effects).
        if (!R->getInst().is<StoreInst *>())
          ProbablyDead.push_back(R);
      } else if (auto *P = dyn_cast<PhiOcc>(Occ)) {
        // This phi is fully redundant to RDom and should not have been placed.
        // TODO: Unnecessary phis are placed when P is in the DF of some R
        // dominated by RDom. We could prevent this by running FRE before PRE.
        // P->replaceWith(*RDom);
      } else if (auto *Ex = dyn_cast<ExitOcc>(Occ)) {
        // Exposure to exit has no effect on real occurrences.
      } else
        llvm_unreachable("Unexpected occurrence type.");
    }
  }

  // Update phi operands to most-dominating real occs. Also start tracking which
  // predecessors are unavailable.
  for (auto &Pair : Phis) {
    PhiOcc &Phi = Pair.second;
    // Fill in unavailable predecessors. TODO: This is quadratic in the number
    // of predecessors per phi.
    for (BasicBlock *Pred : predecessors(&Phi.getBlock())) {
      using Op = PhiOcc::Operand;
      if (find_if(Phi.Defs, [&](const Op &O) { return O.Pred == Pred; }) ==
          Phi.Defs.end())
        Phi.Unavail.push_back(Pred);
    }

    Phi.verify(*DT);

    // TODO: This could be done later.
    for (PhiOcc::Operand &Op : Phi.Defs)
      if (auto *R = dyn_cast<RealOcc>(Op.Occ))
        Op.Occ = R->getDef() ? R->getDef() : Op.Occ;
  }

  // Run availability and anticipability analysis on phis.
  std::vector<PhiOcc *> PhiStack;
  PhiStack.reserve(Phis.size());
  propagateDownUnsafe(PhiStack);
  propagateCantBeAvail(PhiStack);

  // At this point, CanBeAvail will be true for a phi iff it's fully available
  // (empty Unavail) or partially available (non-empty Unavail) but down-safe
  // insertions can be made.
  return false;
}

bool NewGVN::scalarPRE(Function &F) PROFILE_POINT {
  // Pre-compute set of exit occurrences as it's the same for all cong classes.
  std::list<ExitOcc> ExitOccs;
  std::vector<Occurrence *> Ptrs;
  for (BasicBlock &BB : F)
    if (isa<ReturnInst>(BB.getTerminator()) ||
        isa<UnreachableInst>(BB.getTerminator())) {
      if (DomTreeNode *Node = DT->getNode(&BB)) {
        ExitOccs.emplace_back(*Node);
        Ptrs.push_back(&ExitOccs.back());
      }
    }

  PlaceAndFill IDF(*DT, F.size());
  return any_of(CongruenceClasses, [&](CongruenceClass *Cong) {
    return preClass(F, *Cong, ClearGuard(IDF), Ptrs);
  });
}
}
