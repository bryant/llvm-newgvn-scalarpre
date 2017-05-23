enum OccType {
  OccReal,
  OccPhi,
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
      : Occurrence{&N, LocalNum} {
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

  std::vector<std::pair<Occurrence *, BasicBlock *>> Defs;
  std::vector<BasicBlock *> Unavail;
  std::vector<RealOcc *> Uses;
  std::vector<PhiUse *> PhiUses;

  // LocalNum is set to 0 to ensure that when sorted in DPO, phi occurrences
  // precede all other occurrences in the same block.
  PhiOcc(DomTreeNode &N, Occurrence &FirstOperand, BasicBlock &OpBlock)
      : Occurrence{&N, 0}, Defs(1) {
    addOperand(FirstOperand, OpBlock);
  }

  void addOperand(Occurrence &Occ, BasicBlock &Block) {
    Defs.emplace_back(&Occ, &Block);
  }

  static bool classof(const Occurrence &Occ) { return Occ.Type == OccPhi; }
};

// PiggyBank from Sreedhar and Gao 1994.
struct PiggyBank {
  using Node = Occurrence *;

  std::vector<Node> Banks;
  unsigned CurrentLevel;

  PiggyBank(const DominatorTree &DT)

  void top();
  bool empty();
  void pop();
  void push();
  void setCurrentLevel(bool Init = true);
};

struct PlaceAndFill {
  PiggyBank DefQ;
  // ^ Imposes an order on defs so that phis are inserted from highest- to
  // lowest-ranked.
  DenseMap<DomTreeNode *, unsigned> Levels;
  DenseMap<BasicBlock *, PiggyBank::Node *> Defs;
  Visited;

  PlaceAndFill(const DominatorTree &DT, unsigned NumBlocks) {}
  void addDef(RealOcc &Occ);
  void calculate();
  void clear();
};

struct ClearGuard {
  PlaceAndFill Inner;

  ~ClearGuard() { Inner.clear(); }
  void addDef(RealOcc &Occ) { return Inner.addDef(Occ); }
  void calculate() { return Inner.calculate(); }
};

bool NewGVN::scalarPRE(Function &F, CongruenceClass &Cong, ClearGuard IDF) {
  std::vector<RealOcc> RealOccs;
  RealOccs.reserve(Cong.size());
  std::vector<Occurrence *> DPOSorted;
  DPOSorted.reserve(Cong.size());

  for (Instruction *I : Cong) {
    DomTreeNode *Node = DT.getNode(I->getParent());
    RealOccs.emplace_back(*Node, *I);
    DPOSorted.push_back(&RealOccs.back());
    IDF.addDef(RealOccs.back());
  }

  DenseMap<const BasicBlock *, PhiOcc> Phis = IDF.calculate();
  DPOSorted.reserve(DPOSorted.size() + Phis.size());
  for (auto &P : Phis)
    DPOSorted.push_back(&P.second);

  std::sorted(DPOSorted.begin(), DPOSorted.end(),
              [](const Occurrence *A, const Occurrence *B) {
                return std::tie(A->in(), B->out(), A->LocalNum) <
                       std::tie(b->in(), A->out(), B->LocalNum);
              });
}
