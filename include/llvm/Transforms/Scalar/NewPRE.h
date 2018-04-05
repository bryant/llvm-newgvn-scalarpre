#include "llvm/IR/Dominators.h"
#include "llvm/IR/Instructions.h"
#include <forward_list>
#include <utility>

namespace {
using namespace llvm;

// Utility to print BasicBlock names.
struct pbb {
  const BasicBlock &BB;

  pbb(BasicBlock &BB) : BB(BB) {}
  pbb(const BasicBlock &BB) : BB(BB) {}
  pbb(BasicBlock *BB) : BB(*BB) {}
  pbb(const BasicBlock *BB) : BB(*BB) {}

  template <typename Stream>
  friend Stream &operator<<(Stream &Out, const pbb &P) {
    if (!P.BB.hasName()) {
      P.BB.printAsOperand(Out, false);
      return Out;
    }
    return Out << P.BB.getName();
  }
};

} // namespace

// Our job is to PRE each congruence class. To do this, we re-use SSAPRE's
// factored redundancy graph concept and down-safety/willBeAvail rules to
// evaluate PRE insertions. Briefly, congruence class members are RealOccs and
// PhiOccs are placed at the IDF of each RealOcc. Collectively, the PhiOccs
// represent all possible PRE points. We also place ExitOccs at the bottom of
// exiting basic blocks to know which phis are down-unsafe.
namespace occ {
using namespace llvm;

enum OccType {
  OccReal,
  OccPhi,
  OccExit,
};

struct Occurrence {
  DomTreeNode *Node;

  // This is basically the instruction DFS number, used to correctly DFS-order
  // occurrences that live in the same block.
  unsigned LocalNum;

  const OccType Type;

  Occurrence(DomTreeNode *Node, unsigned LocalNum, OccType Type)
      : Node(Node), LocalNum(LocalNum), Type(Type) {}

  BasicBlock &getBlock() const { return *Node->getBlock(); }

  unsigned in() const { return Node->getDFSNumIn(); }

  unsigned out() const { return Node->getDFSNumOut(); }

  // TODO: This could return the incorrect result if the dom tree changes, which
  // may happen if we split crit edges.
  bool dominates(const Occurrence &Other) const {
    return (in() == Other.in() && LocalNum < Other.LocalNum) ||
           (in() < Other.in() && Other.out() < out());
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

    friend raw_ostream &operator<<(raw_ostream &O, const PhiOcc::Operand &Op) {
      return O << "Phi Op @ " << pbb(Op.Pred);
    }
  };

  // If PRE happens at this PhiOcc, we need to materialize a PHINode.
  PHINode *P = nullptr;
  std::vector<Operand> Defs;
  std::vector<BasicBlock *> Unavail;
  std::vector<PhiUse> PhiUses;
  bool DownSafe = true;
  bool CanBeAvail = true;
  bool FullyAvail = true;

  // PhiOccs live at the top of their block, hence LocalNum 0.
  PhiOcc(DomTreeNode &N, Occurrence &FirstOperand, BasicBlock &OpBlock)
      : Occurrence{&N, 0, OccPhi} {
    addOperand(FirstOperand, OpBlock);
  }

  // Phi node congruence class members are also wrapped in a PhiOcc.
  PhiOcc(PHINode &P, DomTreeNode &PN) : Occurrence{&PN, 0, OccPhi}, P(&P) {
    assert(P.getParent() == PN.getBlock());
  }

  void addOperand(Occurrence &Occ, BasicBlock &Block) {
    Defs.push_back({&Occ, &Block});
    if (auto *P = dyn_cast<PhiOcc>(&Occ))
      P->addUse(*this, Defs.size() - 1);
  }

  void addUse(PhiOcc &P, unsigned OpIdx) { PhiUses.push_back({&P, OpIdx}); }

  void addUse(RealOcc &R) {
    // Uses.emplace_back(&R);
  }

  void verify(const DominatorTree &DT) const;

  raw_ostream &print(raw_ostream &Out) const {
    if (P) {
      Out << "Materialized PhiOcc ";
      P->printAsOperand(Out);
      Out << " @ ";
    } else
      Out << "PhiOcc @ ";
    Out << pbb(getBlock());
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
      Out << "RealOcc @ " << pbb(II->getParent()) << ": " << *II;
    else if (auto *II = I.dyn_cast<StoreInst *>())
      Out << "RealOcc @ " << pbb(II->getParent()) << ": " << *II;
    return Out;
  }

  static bool classof(Occurrence *Occ) { return Occ->Type == OccReal; }
  static bool classof(const Occurrence *Occ) { return Occ->Type == OccReal; }
};

// Exit occurrences live at bottom of exit blocks. A phi is down-unsafe if it
// has a CFG path to an ExitOcc that doesn't cross a RealOcc.
struct ExitOcc final : public Occurrence {
  // Exit occs live at the bottom of their (exit) blocks; set LocalNum
  // accordingly.
  ExitOcc(DomTreeNode &N) : Occurrence{&N, -1u, OccExit} {}

  raw_ostream &print(raw_ostream &Out) const {
    Out << "ExitOcc @ bottom of " << pbb(getBlock());
    return Out;
  }

  static bool classof(Occurrence *Occ) { return Occ->Type == OccExit; }
  static bool classof(const Occurrence *Occ) { return Occ->Type == OccExit; }
};

} // namespace occ

// Utilities to efficiently enumerate IDFs. Used to place phi occurrences.
namespace idf {
using namespace llvm;
using namespace occ;

// PiggyBank from Sreedhar and Gao 1994. This structure fulfills the same
// purpose as the priority_queue in IDFCalculator but does so with amortized
// constant time per insertion and deletion.
template <typename Node> struct PiggyBank {
  // Indexes into Banks. The left index is dom tree level of the desired node.
  using NodeRef = std::pair<unsigned, unsigned>;

  // Nodes are popped from Banks, from highest to lowest index.
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

  NodeRef push(const Node &N, unsigned Level) {
    Banks[Level].push_back(N);
    return {Level, Banks[Level].size() - 1};
  }

  Node &operator[](NodeRef Ref) { return Banks[Ref.first][Ref.second]; }
};

// This is like ForwardIDFCalculator. It 1) places phi occs at IDFs and 2) fills
// each phi's operands as it is placed. This saves the cost of a separate
// renaming DPO walk.
struct PlaceAndFill {
  const DominatorTree &DT;

  // Imposes an order on defs so that phis are inserted from highest- to lowest-
  // ranked, thus preventing dom subtree re-traversals.
  PiggyBank<Occurrence *> DefQueue;

  // Tracks basic blocks that contain a def (real occurrence). Needed to know
  // when to stop iterating on dom frontiers. If there are multiple defs in one
  // block, we keep only the latest.
  DenseMap<const DomTreeNode *, PiggyBank<Occurrence *>::NodeRef> DefBlocks;

  // Avoid re-visiting the same block during IDF placement to stay linear time.
  DenseSet<const DomTreeNode *> Visited;

  // Stack for visiting def node subtrees in pre-order.
  std::vector<DomTreeNode *> SubtreeStack;

  // Also allocate some space to hold PhiOccs.
  std::forward_list<PhiOcc> Pool;
  DenseMap<const DomTreeNode *, PhiOcc *> PhiBlocks;

  PlaceAndFill(DominatorTree &DT) : DT(DT), DefQueue(0) {
    // Figure out height of dom tree.
    unsigned Height =
        std::max_element(GraphTraits<DominatorTree *>::nodes_begin(&DT),
                         GraphTraits<DominatorTree *>::nodes_end(&DT),
                         [](const DomTreeNode *A, const DomTreeNode *B) {
                           return A->getLevel() < B->getLevel();
                         })
            ->getLevel();
    DefQueue = PiggyBank<Occurrence *>(Height + 1);
    // Prevent re-allocs.
    SubtreeStack.reserve(Height + 1);
  }

  void addDef(Occurrence &Occ) {
    // If there are multiple definitions in a block, keep only the latest
    // because that is the one exposed to phis on the block's DF.
    auto InsPair = DefBlocks.insert({Occ.Node, {0, 0}});
    if (InsPair.second)
      // First def of this block. Push it into the PiggyBank.
      InsPair.first->second = DefQueue.push(&Occ, Occ.Node->getLevel());
    else if (DefQueue[InsPair.first->second]->LocalNum < Occ.LocalNum)
      // Occ is later in the block than the previously inserted def.
      DefQueue[InsPair.first->second] = &Occ;
  }

  // Insert a PhiOcc or return a reference to the existing PhiOcc of P's block.
  std::pair<PhiOcc *, bool> addPhiOcc(PhiOcc &&P) {
    auto Pair = PhiBlocks.insert({P.Node, nullptr});
    if (Pair.second) {
      Pool.push_front(std::move(P));
      return {Pair.first->second = &Pool.front(), true};
    }
    return {Pair.first->second, false};
  }

  decltype(Pool) getPhis() { return Pool; }

  void calculate() {
    while (!DefQueue.empty())
      visitSubtree(*DefQueue.pop(), DefQueue.CurrentLevel);
  }

  void clear() {
    assert(DefQueue.empty() &&
           "All defs should have been popped after calculate().");
    assert(SubtreeStack.empty());
    DefBlocks.clear();
    Visited.clear();
    PhiBlocks.clear();
    Pool.clear();
  }

private:
  // Search CurDef's dom subtree for J-edges. CurDef's DF will be the targets of
  // all J-edges whose shadow contains CurDef.
  void visitSubtree(Occurrence &CurDef, unsigned CurDefLevel) {
    assert(SubtreeStack.empty());
    SubtreeStack.push_back(CurDef.Node);
    Visited.insert(CurDef.Node);

    while (!SubtreeStack.empty()) {
      DomTreeNode &SubNode = *SubtreeStack.back();
      SubtreeStack.pop_back();
      for (BasicBlock *Succ : successors(SubNode.getBlock())) {
        DomTreeNode &SuccNode = *DT.getNode(Succ);
        unsigned SuccLevel;

        // Skip if it's a dom tree edge (not a J-edge).
        if (SuccNode.getIDom() == &SubNode ||
            (SuccLevel = SuccNode.getLevel() > CurDefLevel))
          continue;

        // SuccNode belongs in CurDef's DF. Check if a phi has been placed.
        auto InsPair = addPhiOcc(PhiOcc(SuccNode, CurDef, *SubNode.getBlock()));
        if (!InsPair.second) {
          // Already inserted a phi into this block, which means that its DF+
          // has already been visited.
          InsPair.first->addOperand(CurDef, *SubNode.getBlock());
        } else if (!DefBlocks.count(&SuccNode)) {
          // New phi was inserted, meaning that this is the first encounter of
          // this DF member. Also there is no def in this block, so we need to
          // iterate on the DF.
          DefQueue.push(InsPair.first, SuccLevel);
        }
      }

      // Continue dom subtree DFS.
      for (DomTreeNode *Child : SubNode)
        if (Visited.insert(Child).second)
          SubtreeStack.push_back(Child);
    }
  }
};

// To avoid re-allocations, we re-use the same PlaceAndFill instance to PRE each
// congruence class. ClearGuard ensures that PlaceAndFill is cleared in between
// PREs. TODO: Remove once unused.
struct ClearGuard {
  PlaceAndFill &Inner;

  ClearGuard(PlaceAndFill &Inner) : Inner(Inner) {}
  ~ClearGuard() { Inner.clear(); }
  auto addDef(Occurrence &Occ) -> decltype(Inner.addDef(Occ)) {
    return Inner.addDef(Occ);
  }
  auto addPhiOcc(PhiOcc &&P) -> decltype(Inner.addPhiOcc(std::move(P))) {
    return Inner.addPhiOcc(std::move(P));
  }
  auto getPhis() -> decltype(Inner.getPhis()) { return Inner.getPhis(); }
  auto calculate() -> decltype(Inner.calculate()) { return Inner.calculate(); }
};
} // namespace idf

namespace {
class NewGVN;

class CongruenceClass;

class NewPRE {
  NewGVN &GVN;
  DominatorTree &DT;

  // Owns the PhiOccs, too.
  PlaceAndFill IDF;
  std::vector<ExitOcc> ExitOccs;
  std::vector<RealOcc> RealOccs;

public:
  NewPRE(NewGVN &GVN, DominatorTree &DT) : GVN(GVN), DT(DT), IDF(DT) {
    for (DomTreeNode *DTN : nodes(&DT))
      if (isa<ReturnInst>(DTN->getBlock()->getTerminator()))
        ExitOccs.emplace_back(*DTN);
  }

  // Compute and insert fully available phis. Partial redundancy elim is only
  // performed if PRE is true.
  void insertFullyAvailPhis(CongruenceClass &, bool PRE);

  void placePhis(CongruenceClass &);

  void clear();

private:
};
} // namespace
