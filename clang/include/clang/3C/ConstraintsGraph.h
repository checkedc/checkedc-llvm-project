//=--ConstraintsGraph.h-------------------------------------------*- C++-*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
// Class we use to maintain constraints in a graph form.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_3C_CONSTRAINTSGRAPH_H
#define LLVM_CLANG_3C_CONSTRAINTSGRAPH_H

#include "clang/3C/Constraints.h"
#include "llvm/ADT/BreadthFirstIterator.h"
#include "llvm/ADT/DirectedGraph.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/Support/GraphWriter.h"

template <class DataType> struct DataEdge;

template <typename DataType, typename EdgeType = DataEdge<DataType>>
class DataNode : public llvm::DGNode<DataNode<DataType, EdgeType>, EdgeType> {
public:
  typedef DataNode<DataType, EdgeType> NodeType;
  typedef llvm::DGNode<NodeType, EdgeType> SuperType;

  DataNode() = delete;
  DataNode(DataType D, EdgeType &E) : SuperType(E), Data(D) {}
  explicit DataNode(DataType D) : SuperType(), Data(D) {}
  DataNode(const DataNode &N) : SuperType(N), Data(N.Data) {}
  DataNode(const DataNode &&N) : SuperType(std::move(N)), Data(N.Data) {}

  ~DataNode() = default;

  DataType getData() const { return Data; }

  void connectTo(NodeType &Other, bool SoftEdge = false,
                 Constraint *C = nullptr) {
    auto *BLR = new EdgeType(Other, C);
    BLR->IsSoft = SoftEdge;
    this->addEdge(*BLR);
    auto *BRL = new EdgeType(*this, C);
    Other.addPredecessor(*BRL);
  }

  const llvm::SetVector<EdgeType *> &getPredecessors() {
    return PredecessorEdges;
  }

  // Nodes are defined exactly by the data they contain, not by their
  // connections to other nodes.
  bool isEqualTo(const DataNode &N) const { return this->Data == N.Data; }

private:
  // Data element stored in each node. This is used by isEqualTo to discriminate
  // between nodes.
  DataType Data;

  // While the constraint graph is directed, we want to efficiently traverse
  // edges in the opposite direction. This set contains an edge entry pointing
  // back to every node that has an edge to this node.
  llvm::SetVector<EdgeType *> PredecessorEdges;
  void addPredecessor(EdgeType &E) { PredecessorEdges.insert(&E); }
};

namespace llvm {
// Boilerplate template specialization
template <typename Data, typename EdgeType>
struct GraphTraits<DataNode<Data, EdgeType> *> {
  using NodeRef = DataNode<Data, EdgeType> *;

  static NodeRef getTargetNode(EdgeType *P) { return &P->getTargetNode(); }

  using ChildIteratorType =
      mapped_iterator<typename DataNode<Data, EdgeType>::iterator,
                      decltype(&getTargetNode)>;

  static NodeRef getEntryNode(NodeRef N) { return N; }
  // See clang/doc/checkedc/3C/clang-tidy.md#names-referenced-by-templates
  // NOLINTNEXTLINE(readability-identifier-naming)
  static ChildIteratorType child_begin(NodeRef N) {
    return ChildIteratorType(N->begin(), &getTargetNode);
  }
  // See clang/doc/checkedc/3C/clang-tidy.md#names-referenced-by-templates
  // NOLINTNEXTLINE(readability-identifier-naming)
  static ChildIteratorType child_end(NodeRef N) {
    return ChildIteratorType(N->end(), &getTargetNode);
  }
};
} // namespace llvm

template <class DataType>
struct DataEdge : public llvm::DGEdge<DataNode<DataType>, DataEdge<DataType>> {
  typedef llvm::DGEdge<DataNode<DataType>, DataEdge<DataType>> SuperType;
  explicit DataEdge(DataNode<DataType> &Node, Constraint *C = nullptr)
      : SuperType(Node), EdgeConstraint(C) {}
  DataEdge(const DataEdge &E, Constraint *C = nullptr)
      : SuperType(E), EdgeConstraint(C) {}
  bool IsSoft = false;
  Constraint *EdgeConstraint;
};

class GraphVizOutputGraph;

// Define a general purpose extension to the llvm provided graph class that
// stores some data at each node in the graph. This is used by the checked and
// pointer type constraint graphs (which store atoms at each node) as well as
// the array bounds graph (which stores BoundsKeys).
template <typename Data, typename EdgeType = DataEdge<Data>>
class DataGraph
    : public llvm::DirectedGraph<DataNode<Data, EdgeType>, EdgeType> {
public:
  typedef DataNode<Data, EdgeType> NodeType;

  virtual ~DataGraph() {
    for (auto *N : this->Nodes) {
      for (auto *E : N->getEdges())
        delete E;
      N->getEdges().clear();
      delete N;
      N = nullptr;
    }
    this->Nodes.clear();
    invalidateBFSCache();
  }

  void removeEdge(Data Src, Data Dst) {
    NodeType *NSrc = this->findNode(Src);
    NodeType *NDst = this->findNode(Dst);
    assert(NSrc && NDst);
    llvm::SmallVector<EdgeType *, 10> Edges;
    NDst->findEdgesTo(*NSrc, Edges);
    for (EdgeType *E : Edges) {
      NDst->removeEdge(*E);
      delete E;
    }
    invalidateBFSCache();
  }

  void addEdge(Data L, Data R, bool SoftEdge = false, Constraint *C = nullptr) {
    NodeType *BL = this->findOrCreateNode(L);
    NodeType *BR = this->findOrCreateNode(R);
    BL->connectTo(*BR, SoftEdge, C);
    invalidateBFSCache();
  }

  void addUniqueEdge(Data L, Data R) {
    NodeType *BL = this->findOrCreateNode(L);
    NodeType *BR = this->findOrCreateNode(R);
    llvm::SmallVector<EdgeType *, 10> Edges;
    BL->findEdgesTo(*BR, Edges);
    if (Edges.empty()) {
      addEdge(L, R);
    }
  }

  // This version provides more info by returning graph edges
  // rather than data items
  bool getIncidentEdges(Data D, std::set<EdgeType*> &EdgeSet, bool Succ,
                      bool Append = false, bool IgnoreSoftEdges = false) const {
    NodeType *N = this->findNode(D);
    if (N == nullptr)
      return false;
    if (!Append)
      EdgeSet.clear();
    llvm::SetVector<EdgeType *> Edges;
    if (Succ)
      Edges = N->getEdges();
    else
      Edges = N->getPredecessors();
    for (auto *E : Edges)
      if (!E->IsSoft || !IgnoreSoftEdges)
        EdgeSet.insert(E);
    return !EdgeSet.empty();
  }

  bool getNeighbors(Data D, std::set<Data> &DataSet, bool Succ,
                    bool Append = false, bool IgnoreSoftEdges = false) const {
    if (!Append)
      DataSet.clear();

    std::set<EdgeType *> Edges;
    getIncidentEdges(D, Edges, Succ, Append, IgnoreSoftEdges);
    for (auto *E : Edges)
      DataSet.insert(E->getTargetNode().getData());
    return !DataSet.empty();
  }

  bool getSuccessorsEdges(Atom *A, std::set<EdgeType*> &EdgeSet,
                     bool Append = false) {
    return getIncidentEdges(A, EdgeSet, true, Append);
  }

  bool getPredecessorsEdges(Atom *A, std::set<EdgeType*> &EdgeSet,
                            bool Append = false) {
    return getIncidentEdges(A, EdgeSet, false, Append);
  }

  bool
  getSuccessors(Data D, std::set<Data> &DataSet, bool Append = false) const {
    return getNeighbors(D, DataSet, true, Append);
  }

  bool
  getPredecessors(Data D, std::set<Data> &DataSet, bool Append = false) const {
    return getNeighbors(D, DataSet, false, Append);
  }

  auto getNodes(){
    return NodeSet;
  }
  
  NodeType *findNode(Data D) const {
    if (NodeSet.find(D) != NodeSet.end())
      return NodeSet.at(D);
    return nullptr;
  }

  void visitBreadthFirst(Data Start, llvm::function_ref<void(Data)> Fn) const {
    NodeType *N = this->findNode(Start);
    if (N == nullptr)
      return;
    // Insert into BFS cache.
    if (BFSCache.find(Start) == BFSCache.end()) {
      std::set<Data> ReachableNodes;
      for (auto TNode : llvm::breadth_first(N)) {
        ReachableNodes.insert(TNode->getData());
      }
      BFSCache[Start] = ReachableNodes;
    }
    for (auto SN : BFSCache[Start])
      Fn(SN);
  }

protected:
  // Finds the node containing the Data if it exists, otherwise a new Node
  // is allocated. Node equality is defined only by the data stored in a node,
  // so if any node already contains the data, this node will be found.
  virtual NodeType *findOrCreateNode(Data D) {
    if (NodeSet.find(D) != NodeSet.end())
      return NodeSet[D];

    auto *NewN = new NodeType(D);
    this->Nodes.push_back(NewN);
    NodeSet[D] = NewN;
    return NewN;
  }

private:
  template <typename G> friend struct llvm::GraphTraits;
  friend class GraphVizOutputGraph;
  mutable std::map<Data, std::set<Data>> BFSCache;
  std::map<Data, NodeType *> NodeSet;

  void invalidateBFSCache() { BFSCache.clear(); }
};

// Specialize the graph for the checked and pointer type constraint graphs. This
// graphs stores atoms at each node, and constraints on each edge. These edges
// are returned by the specialized `getNeighbors` function to provide constraint
// data to clients.
class ConstraintsGraph : public DataGraph<Atom *> {
public:
  // Add an edge to the graph according to the Geq constraint. This is an edge
  // RHSAtom -> LHSAtom
  void addConstraint(Geq *C, const Constraints &CS);

  // Const atoms are the starting points for the solving algorithm so, we need
  // be able to retrieve them from the graph.
  std::set<ConstAtom *> &getAllConstAtoms();

  typedef DataEdge<Atom*> EdgeType;
protected:
  // Add vertex is overridden to save const atoms as they are added to the graph
  // so that getAllConstAtoms can efficiently retrieve them.
  NodeType *findOrCreateNode(Atom *A) override;

private:
  std::set<ConstAtom *> AllConstAtoms;
};

// Below this point we define a graph class specialized for generating the
// graphviz output for the combine checked and ptype graphs.

// Once we combine the graphs, we need to know if an edge came from the ptype
// or the checked constraint graph. We also combine edges to render a pair of
// edges pointing in different directions between the same pair of nodes as a
// single bidirectional edge.
class GraphVizEdge
    : public llvm::DGEdge<DataNode<Atom *, GraphVizEdge>, GraphVizEdge> {
public:
  enum EdgeKind { EK_Checked, EK_Ptype };
  explicit GraphVizEdge(DataNode<Atom *, GraphVizEdge> &Node, EdgeKind Kind,
                        bool Soft)
      : DGEdge(Node), Kind(Kind), IsBidirectional(false), IsSoft(Soft) {}
  GraphVizEdge(const GraphVizEdge &E)
      : DGEdge(E), Kind(E.Kind), IsBidirectional(E.IsBidirectional),
        IsSoft(E.IsSoft) {}

  EdgeKind Kind;
  bool IsBidirectional;
  bool IsSoft;
};

// The graph subclass for graphviz output uses the specialized edge class to
// hold the extra information required. It also provides the methods for
// merging the checked and ptype graphs as well as a static function to do the
// actual conversion and output to file.
class GraphVizOutputGraph : public DataGraph<Atom *, GraphVizEdge> {
public:
  // Merge the provided graphs and dump the graphviz visualization to the given
  // file name. The first graph argument is the checked graph while the second
  // is the pointer type graph.
  static void dumpConstraintGraphs(const std::string &GraphDotFile,
                                   const ConstraintsGraph &Chk,
                                   const ConstraintsGraph &Pty);

  // These maps are used because the graphviz utility provided by llvm does not
  // give an easy way to differentiate between multiple edges between the same
  // pair of nodes. When there is both a checked an a ptype edge between two
  // nodes, these maps ensure that each is output exactly once and has the
  // correct color when it is output.
  mutable std::set<std::pair<Atom *, Atom *>> DoneChecked;
  mutable std::set<std::pair<Atom *, Atom *>> DonePtyp;

private:
  void mergeConstraintGraph(const ConstraintsGraph &Graph,
                            GraphVizEdge::EdgeKind EdgeType);
};

// Below this is boiler plate needed to work with the llvm graphviz output
// functions.

namespace llvm {
template <> struct GraphTraits<GraphVizOutputGraph> {
  using NodeRef = DataNode<Atom *, GraphVizEdge> *;
  using nodes_iterator = GraphVizOutputGraph::iterator;

  static NodeRef getTargetNode(GraphVizEdge *P) { return &P->getTargetNode(); }

  using ChildIteratorType =
      mapped_iterator<typename DataNode<Atom *, GraphVizEdge>::iterator,
                      decltype(&getTargetNode)>;

  // See clang/doc/checkedc/3C/clang-tidy.md#names-referenced-by-templates
  // NOLINTNEXTLINE(readability-identifier-naming)
  static nodes_iterator nodes_begin(const GraphVizOutputGraph &G) {
    return const_cast<GraphVizOutputGraph &>(G).Nodes.begin();
  }

  // See clang/doc/checkedc/3C/clang-tidy.md#names-referenced-by-templates
  // NOLINTNEXTLINE(readability-identifier-naming)
  static nodes_iterator nodes_end(const GraphVizOutputGraph &G) {
    return const_cast<GraphVizOutputGraph &>(G).Nodes.end();
  }

  // See clang/doc/checkedc/3C/clang-tidy.md#names-referenced-by-templates
  // NOLINTNEXTLINE(readability-identifier-naming)
  static ChildIteratorType child_begin(NodeRef N) {
    return {N->begin(), &getTargetNode};
  }

  // See clang/doc/checkedc/3C/clang-tidy.md#names-referenced-by-templates
  // NOLINTNEXTLINE(readability-identifier-naming)
  static ChildIteratorType child_end(NodeRef N) {
    return {N->end(), &getTargetNode};
  }
};

template <>
struct DOTGraphTraits<GraphVizOutputGraph>
    : public llvm::DefaultDOTGraphTraits,
      llvm::GraphTraits<GraphVizOutputGraph> {
  DOTGraphTraits(bool Simple = false) : DefaultDOTGraphTraits(Simple) {}

  std::string getNodeLabel(const DataNode<Atom *, GraphVizEdge> *Node,
                           const GraphVizOutputGraph &CG);
  static std::string
  getEdgeAttributes(const DataNode<Atom *, GraphVizEdge> *Node,
                    ChildIteratorType T, const GraphVizOutputGraph &CG);
};
} // namespace llvm

#endif // LLVM_CLANG_3C_CONSTRAINTSGRAPH_H
