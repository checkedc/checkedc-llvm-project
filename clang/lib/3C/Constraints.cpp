//=--Constraints.cpp----------------------------------------------*- C++-*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
// Constraint solver implementation
//
//===----------------------------------------------------------------------===//

#include "clang/3C/Constraints.h"
#include "clang/3C/3CGlobalOptions.h"
#include "clang/3C/ConstraintVariables.h"
#include "clang/3C/ConstraintsGraph.h"
#include <iostream>
#include <set>

using namespace llvm;

// Remove the constraint from the global constraint set.
bool Constraints::removeConstraint(Constraint *C) {
  bool RetVal = false;
  Geq *GE = dyn_cast<Geq>(C);
  assert(GE != nullptr && "Invalid constrains requested to be removed.");
  // We can only remove constraints from ConstAtoms.
  if (isa<ConstAtom>(GE->getRHS()) && isa<VarAtom>(GE->getLHS())) {
    removeReasonBasedConstraint(C);
    RetVal = TheConstraints.erase(C) != 0;
    // Delete from graph.
    ConstraintsGraph *TG = nullptr;
    TG = GE->constraintIsChecked() ? ChkCG : PtrTypCG;
    RetVal = true;
    // Remove the edge form the corresponding constraint graph.
    TG->removeEdge(GE->getRHS(), GE->getLHS());
  }
  return RetVal;
}

// Check if we can add this constraint. This provides a global switch to
// control what constraints we can add to our system.
void Constraints::editConstraintHook(Constraint *C) {
  if (!_3COpts.AllTypes) {
    // Invalidate any pointer-type constraints.
    if (Geq *E = dyn_cast<Geq>(C)) {
      if (!E->constraintIsChecked()) {
        VarAtom *LHSA = dyn_cast<VarAtom>(E->getLHS());
        VarAtom *RHSA = dyn_cast<VarAtom>(E->getRHS());
        if (LHSA != nullptr && RHSA != nullptr) {
          return;
        }
        // Make this checked only if the const atom is other than Ptr.
        if (RHSA) {
          if (!dyn_cast<PtrAtom>(E->getLHS())) {
            E->setChecked(getWild());
            ReasonLoc Rsn = E->getReason();
            Rsn.Reason = POINTER_IS_ARRAY_REASON;
            E->setReason(Rsn);
          }
        } else {
          assert(LHSA && "Adding constraint between constants?!");
          if (!dyn_cast<PtrAtom>(E->getRHS())) {
            E->setChecked(getWild());
            ReasonLoc Rsn = E->getReason();
            Rsn.Reason = POINTER_IS_ARRAY_REASON;
            E->setReason(Rsn);
          }
        }
      }
    }
  }
}

// Add a constraint to the set of constraints. If the constraint is already
// present (by syntactic equality) return false.
bool Constraints::addConstraint(Constraint *C) {
  editConstraintHook(C);

  auto Search = TheConstraints.find(C);

  // Check if C is already in the set of constraints.
  if (Search == TheConstraints.end()) {
    TheConstraints.insert(C);

    if (Geq *G = dyn_cast<Geq>(C)) {
      if (G->constraintIsChecked())
        ChkCG->addConstraint(G, *this);
      else
        PtrTypCG->addConstraint(G, *this);
    }

    addReasonBasedConstraint(C);

    // Update the variables that depend on this constraint.
    if (Geq *E = dyn_cast<Geq>(C)) {
      if (VarAtom *VLhs = dyn_cast<VarAtom>(E->getLHS()))
        VLhs->Constraints.insert(C);
      else if (VarAtom *VRhs = dyn_cast<VarAtom>(E->getRHS())) {
        VRhs->Constraints.insert(C);
      }
    } else
      llvm_unreachable("unsupported constraint");
    return true;
  }

  // If the constraint being added is due to unwritability,
  // propagate this reason to the existing constraint.
  // This way we always prioritize the unwritability as the reason
  // for wildness.
  // This is needed as 3C will currently only report one cause of wildness
  // (See https://github.com/correctcomputation/checkedc-clang/issues/664)
  if (C->isUnwritable()) {
    auto *StoredConstraint = *Search;
    StoredConstraint->setReason(C->getReason());
  }

  return false;
}

bool Constraints::addReasonBasedConstraint(Constraint *C) {
  // Only insert if this is an Eq constraint and has a valid reason.
  if (Geq *E = dyn_cast<Geq>(C)) {
    if (E->getReasonText() != DEFAULT_REASON && !E->getReasonText().empty() &&
        E->getReason().Location.valid())
      return this->ConstraintsByReason[E->getReasonText()].insert(E).second;
  }
  return false;
}

bool Constraints::removeReasonBasedConstraint(Constraint *C) {
  if (Geq *E = dyn_cast<Geq>(C)) {
    // Remove if the constraint is present.
    if (this->ConstraintsByReason.find(E->getReasonText()) !=
        this->ConstraintsByReason.end())
      return this->ConstraintsByReason[E->getReasonText()].erase(E) > 0;
  }
  return false;
}

// Make a graph G:
//- with nodes for each variable k and each qualifier constant q.
//- with edges Q --> Q’ for each constraint Q <: Q’
// Note: Constraints (q <: k ⇒ q’ <: k’) are not supported, but we shouldn’t
// actually need them. So make your algorithm die if it comes across them.
//
// For each non-constant node k in G,
//- set sol(k) = q_\bot (the least element, i.e., Ptr)
//
// For each constant node q_i, starting with the highest and working down,
//- set worklist W = { q_i }
//- while W nonempty
//-- let Q = take(W)
//-- For all edges (Q --> k) in G
//--- if sol(k) <> (sol(k) JOIN Q) then
//---- set sol(k) := (sol(k) JOIN Q)
//---- for all edges (k --> q) in G, confirm that sol(k) <: q; else fail
//---- add k to W

static bool
doSolve(ConstraintsGraph &CG,
        ConstraintsEnv &Env, Constraints *CS, bool DoLeastSolution,
        std::set<VarAtom *> *InitVs,
        std::set<ConstraintsGraph::EdgeType *> &Conflicts) {

  std::vector<Atom *> WorkList;

  // Initialize with seeded VarAtom set (pre-solved).
  if (InitVs != nullptr)
    WorkList.insert(WorkList.begin(), InitVs->begin(), InitVs->end());

  // Initialize work list with ConstAtoms.
  auto &InitC = CG.getAllConstAtoms();
  WorkList.insert(WorkList.begin(), InitC.begin(), InitC.end());

  while (!WorkList.empty()) {
    auto *Curr = *(WorkList.begin());
    // Remove the first element, get its solution.
    WorkList.erase(WorkList.begin());
    ConstAtom *CurrSol = Env.getAssignment(Curr);

    // get its neighbors.
    std::set<Atom *> Neighbors;
    CG.getNeighbors(Curr, Neighbors, DoLeastSolution);
    // update each successor's solution.
    for (auto *NeighborA : Neighbors) {
      if (VarAtom *Neighbor = dyn_cast<VarAtom>(NeighborA)) {
        ConstAtom *NghSol = Env.getAssignment(Neighbor);
        // update solution if doing so would change it
        // checked? --- if sol(Neighbor) <> (sol(Neighbor) JOIN Cur)
        //   else   --- if sol(Neighbor) <> (sol(Neighbor) MEET Cur)
        if ((DoLeastSolution && *NghSol < *CurrSol) ||
            (!DoLeastSolution && *CurrSol < *NghSol)) {
          // ---- set sol(k) := (sol(k) JOIN/MEET Q)
          bool Changed = Env.assign(Neighbor, CurrSol);
          assert(Changed);
          WorkList.push_back(Neighbor);
        }
      } // ignore ConstAtoms for now; will confirm solution below
    }
  }

  // Check Upper/lower bounds hold; collect failures in conflicts set.
  std::set<ConstraintsGraph::EdgeType*> IncidentEdges;
  bool Ok = true;
  for (ConstAtom *Cbound : CG.getAllConstAtoms()) {
    if (CG.getIncidentEdges(Cbound, IncidentEdges, !DoLeastSolution)) {
      for (auto *E : IncidentEdges) {
        VarAtom *VA = dyn_cast<VarAtom>(E->getTargetNode().getData());
        if (VA == nullptr)
          continue;
        ConstAtom *Csol = Env.getAssignment(VA);
        if ((DoLeastSolution && *Cbound < *Csol) ||
            (!DoLeastSolution && *Csol < *Cbound)) {
          Ok = false;
          // Save effected VarAtom in conflict set. This will be constrained to
          // wild after pointer type solving is finished. Checked types will
          // be resolved with this new constraint, transitively propagating the
          // new WILD-ness.
          Conflicts.insert(E);
          // Failure case.
          if (_3COpts.Verbose) {
            errs() << "Unsolvable constraints: ";
            VA->print(errs());
            errs() << "=";
            Csol->print(errs());
            errs() << (DoLeastSolution ? "<" : ">");
            Cbound->print(errs());
            errs() << " var will be made WILD\n";
          }
        }
      }
    }
  }

  return Ok;
}

VarAtomPred IsReturn = [](VarAtom *VA) -> bool {
  return VA->getVarKind() == VarAtom::V_Return;
};
VarAtomPred IsParam = [](VarAtom *VA) -> bool {
  return VA->getVarKind() == VarAtom::V_Param;
};
VarAtomPred IsNonParamReturn = [](VarAtom *VA) -> bool {
  return !IsReturn(VA) && !IsParam(VA);
};

// Remove from S all elements that don't match the predicate P
void filter(VarAtomPred P, std::set<VarAtom *> &S) {
  for (auto I = S.begin(), E = S.end(); I != E;) {
    if (!P(*I))
      I = S.erase(I);
    else
      ++I;
  }
}

// For the provided constraint graph, construct the set of atoms bounded in a
// direction (defined by Succs) by an atom from the set of concrete atoms.
// When Succs is true, the traversal flows from each node to its successor - in
// the direction the edges are oriented. When false, the traversal is reversed.
// To view this another way, true checks for a lower bound in the Ptyp
// constraint graph, but an upper bound in the checked graph. UseConstAtoms
// decides if constant atoms should be used in addition to the provided Concrete
// atoms.
static std::set<VarAtom *> findBounded(ConstraintsGraph &CG,
                                       std::set<VarAtom *> *Concrete,
                                       bool Succs, bool UseConstAtoms = true) {
  std::set<VarAtom *> Bounded;
  std::set<Atom *> Open;

  // Initialize the open set of atoms with the provided set of fixed atoms.
  // These are the start points for a traversal of the constraint graph.
  if (Concrete != nullptr) {
    Open.insert(Concrete->begin(), Concrete->end());
    Bounded.insert(Concrete->begin(), Concrete->end());
  }

  // We often, but not always, want to consider constant atoms as concrete.
  if (UseConstAtoms) {
    auto &ConstA = CG.getAllConstAtoms();
    Open.insert(ConstA.begin(), ConstA.end());
  }

  // Traversal of the constraint graph. An atom is bounded in a direction by
  // one of the Concrete atoms if it is reachable from one of the atoms taking
  // only edges in that direction. The particular atom bounding it does not
  // matter.
  while (!Open.empty()) {
    auto *Curr = *(Open.begin());
    Open.erase(Open.begin());

    std::set<Atom *> Neighbors;
    CG.getNeighbors(Curr, Neighbors, Succs, false, true);
    for (Atom *A : Neighbors) {
      VarAtom *VA = dyn_cast<VarAtom>(A);
      if (VA && Bounded.find(VA) == Bounded.end()) {
        Open.insert(VA);
        Bounded.insert(VA);
      }
    }
  }

  return Bounded;
}

bool Constraints::graphBasedSolve() {
  std::set<ConstraintsGraph::EdgeType *> Conflicts;
  ConstraintsGraph SolChkCG;
  ConstraintsGraph SolPtrTypCG;
  ConstraintsEnv &Env = Environment;

  // Checked well-formedness.
  Environment.checkAssignment(getDefaultSolution());

  // Setup the Checked Constraint Graph.
  for (const auto &C : TheConstraints) {
    if (Geq *G = dyn_cast<Geq>(C)) {
      if (G->constraintIsChecked())
        SolChkCG.addConstraint(G, *this);
      else
        // Need to copy whether or not this constraint into the new graph
        SolPtrTypCG.addConstraint(G, *this);
    }
  }

  if (_3COpts.DebugSolver)
    GraphVizOutputGraph::dumpConstraintGraphs("initial_constraints_graph.dot",
                                              SolChkCG, SolPtrTypCG);

  // Solve Checked/unchecked constraints first.
  Env.doCheckedSolve(true);

  bool Res = doSolve(SolChkCG, Env, this, true, nullptr, Conflicts);

  // Now solve PtrType constraints
  if (Res && _3COpts.AllTypes) {
    Env.doCheckedSolve(false);
    bool RegularSolve = !(_3COpts.OnlyGreatestSol || _3COpts.OnlyLeastSol);

    if (_3COpts.OnlyLeastSol) {
      // Do only least solution.
      // First reset ptr solution to NTArr.
      Env.resetSolution(
          [](VarAtom *VA) -> bool {
            // We want to reset solution for all pointers.
            return true;
          },
          getNTArr());
      Res = doSolve(SolPtrTypCG, Env, this, true, nullptr, Conflicts);
    } else if (_3COpts.OnlyGreatestSol) {
      // Do only greatest solution
      Res = doSolve(SolPtrTypCG, Env, this, false, nullptr, Conflicts);
    } else {
      // Regular solve
      // Step 1: Greatest solution
      Res = doSolve(SolPtrTypCG, Env, this, false, nullptr, Conflicts);
    }

    // Step 2: Reset all solutions but for function params,
    // and compute the least.
    if (Res && RegularSolve) {

      // We want to find all local variables with an upper bound that provide a
      // lower bound for return variables that are not otherwise bounded.

      // 1. Find return vars with a lower bound.
      std::set<VarAtom *> ParamVars = Env.filterAtoms(IsParam);
      std::set<VarAtom *> LowerBoundedRet =
          findBounded(SolPtrTypCG, &ParamVars, true);
      filter(IsReturn, LowerBoundedRet);

      // 2. Find local vars where one of the return vars is an upper bound.
      //    Conversely, these are an alternative lower bound for the return var.
      std::set<VarAtom *> RetUpperBoundedLocals =
          findBounded(SolPtrTypCG, &LowerBoundedRet, false, false);
      filter(IsNonParamReturn, RetUpperBoundedLocals);

      // 3. Find local vars upper bounded by a const var.
      std::set<VarAtom *> ConstUpperBoundedLocals =
          findBounded(SolPtrTypCG, nullptr, false);
      filter(IsNonParamReturn, ConstUpperBoundedLocals);

      // 4. Take set difference of 2 and 3 to find bounded vars that do not
      //    effect an existing lower bound.
      std::set<VarAtom *> Diff;
      std::set_difference(
          ConstUpperBoundedLocals.begin(), ConstUpperBoundedLocals.end(),
          RetUpperBoundedLocals.begin(), RetUpperBoundedLocals.end(),
          std::inserter(Diff, Diff.begin()));

      // 5. Reset var to NTArr if not a param var and not in the previous set.
      std::set<VarAtom *> Rest = Env.resetSolution(
          [Diff](VarAtom *VA) -> bool {
            return !(IsParam(VA) || Diff.find(VA) != Diff.end());
          },
          getNTArr());

      // Remember which variables have a concrete lower bound. Variables without
      // a lower bound will be resolved in the final greatest solution.
      std::set<VarAtom *> LowerBounded = findBounded(SolPtrTypCG, &Rest, true);

      Res = doSolve(SolPtrTypCG, Env, this, true, &Rest, Conflicts);

      // Step 3: Reset local variable solutions, compute greatest
      if (Res) {
        Rest.clear();

        Rest = Env.resetSolution(
            [LowerBounded](VarAtom *VA) -> bool {
              return IsNonParamReturn(VA) ||
                     LowerBounded.find(VA) == LowerBounded.end();
            },
            getPtr());

        Res = doSolve(SolPtrTypCG, Env, this, false, &Rest, Conflicts);
      }
    }
    // If PtrType solving (partly) failed, make the affected VarAtoms wild.
    if (!Res) {
      std::set<VarAtom *> Rest;
      Env.doCheckedSolve(true);
      for (auto *Conflict : Conflicts) {
        Atom *ConflictAtom = Conflict->getTargetNode().getData();
        assert(ConflictAtom != nullptr);
        ReasonLoc Rsn1 = Conflict->EdgeConstraint->getReason();
        // Determine a second from the constraints immediately incident to the
        // conflicting atom. A future improvement should traverse the
        // constraint graph to find the contradictory constraints to constant
        // atoms. See correctcomputation/checkedc-clang#680.
        auto Succs = Conflict->getTargetNode().getEdges();
        ReasonLoc Rsn2;
        for (auto *Succ : Succs) {
          if (auto *SuccGeq = dyn_cast<Geq>(Succ->EdgeConstraint)) {
            if (Env.getAssignment(ConflictAtom) ==
                Env.getAssignment(SuccGeq->getLHS()) ||
                Env.getAssignment(ConflictAtom) ==
                    Env.getAssignment(SuccGeq->getRHS())) {
              Rsn2 = Succ->EdgeConstraint->getReason();
              break;
            }
          }
        }
        auto Rsn = ReasonLoc("Inferred conflicting types",
                             PersistentSourceLoc());
        Geq *ConflictConstraint = createGeq(ConflictAtom, getWild(), Rsn);
        ConflictConstraint->addReason(Rsn1);
        ConflictConstraint->addReason(Rsn2);
        addConstraint(ConflictConstraint);
        SolChkCG.addConstraint(ConflictConstraint, *this);
        Rest.insert(cast<VarAtom>(ConflictAtom));
      }
      Conflicts.clear();
      /* FIXME: Should we propagate the old res? */
      Res = doSolve(SolChkCG, Env, this, true, &Rest, Conflicts);
    }
    // Final Step: Merge ptyp solution with checked solution.
    Env.mergePtrTypes();
  }

  return Res;
}

// Solve the system of constraints. Return true in the second position if
// the system is solved. If the system is solved, the first position is
// an empty. If the system could not be solved, the constraints in conflict
// are returned in the first position.
void Constraints::solve() {
  if (_3COpts.DebugSolver) {
    errs() << "constraints beginning solve\n";
    dump();
  }
  graphBasedSolve();

  if (_3COpts.DebugSolver) {
    errs() << "solution, when done solving\n";
    Environment.dump();
  }
}

void Constraints::print(raw_ostream &O) const {
  O << "CONSTRAINTS: \n";
  for (const auto &C : TheConstraints) {
    C->print(O);
    O << "\n";
  }
  Environment.print(O);
}

void Constraints::dump(void) const { print(errs()); }

void Constraints::dumpJson(llvm::raw_ostream &O) const {
  O << "{\"Constraints\":[";
  bool AddComma = false;
  for (const auto &C : TheConstraints) {
    if (AddComma) {
      O << ",\n";
    }
    C->dumpJson(O);
    AddComma = true;
  }
  O << "],\n";

  Environment.dumpJson(O);
}

bool Constraints::removeAllConstraintsOnReason(std::string &Reason,
                                               ConstraintSet &RemovedCons) {
  // Are there any constraints with this reason?
  bool Removed = false;
  if (this->ConstraintsByReason.find(Reason) !=
      this->ConstraintsByReason.end()) {
    RemovedCons.insert(this->ConstraintsByReason[Reason].begin(),
                       this->ConstraintsByReason[Reason].end());
    for (auto *CToDel : RemovedCons) {
      Removed = this->removeConstraint(CToDel) || Removed;
    }
    return Removed;
  }
  return Removed;
}

VarAtom *Constraints::getOrCreateVar(ConstraintKey V, std::string Name,
                                     VarAtom::VarKind VK) {
  return Environment.getOrCreateVar(V, getDefaultSolution(), Name, VK);
}

VarSolTy Constraints::getDefaultSolution() {
  return std::make_pair(getPtr(), getPtr());
}

VarAtom *Constraints::getFreshVar(std::string Name, VarAtom::VarKind VK) {
  return Environment.getFreshVar(getDefaultSolution(), Name, VK);
}

VarAtom *Constraints::getVar(ConstraintKey V) const {
  return Environment.getVar(V);
}

// Constructs a fresh VarAtom constrained GEQ the specified constant atom. This
// should generally be used instead of using constant atoms directly if the the
// VarAtom will be used in the variables vector of a PVConstraint.
VarAtom *Constraints::createFreshGEQ(std::string Name, VarAtom::VarKind VK,
                                     ConstAtom *Con, ReasonLoc Rsn) {
  VarAtom *VA = getFreshVar(Name, VK);
  addConstraint(createGeq(VA, Con, Rsn));
  return VA;
}

PtrAtom *Constraints::getPtr() const { return PrebuiltPtr; }
ArrAtom *Constraints::getArr() const { return PrebuiltArr; }
NTArrAtom *Constraints::getNTArr() const { return PrebuiltNTArr; }
WildAtom *Constraints::getWild() const { return PrebuiltWild; }

ConstAtom *Constraints::getAssignment(Atom *A) {
  Environment.doCheckedSolve(true);
  return Environment.getAssignment(A);
}

const ConstraintsGraph &Constraints::getChkCG() const {
  assert(ChkCG != nullptr && "Checked Constraint graph cannot be nullptr");
  return *ChkCG;
}

const ConstraintsGraph &Constraints::getPtrTypCG() const {
  assert(PtrTypCG != nullptr && "Pointer type Constraint graph "
                                "cannot be nullptr");
  return *PtrTypCG;
}

Geq *Constraints::createGeq(Atom *Lhs, Atom *Rhs, ReasonLoc Rsn,
                            bool IsCheckedConstraint, bool Soft) {
  if (Rsn.Location.valid()) {
    // Make this invalid, if the source location is not absolute path
    // this is to avoid crashes in clangd.
    if (!llvm::sys::path::is_absolute(Rsn.Location.getFileName()))
      Rsn.Location = PersistentSourceLoc();
  }
  assert("Shouldn't be constraining WILD >= VAR" && Lhs != getWild());
  return new Geq(Lhs, Rhs, Rsn, IsCheckedConstraint, Soft);
}

void Constraints::resetEnvironment() {
  Environment.resetFullSolution(getDefaultSolution());
}

void Constraints::clear() {
  TheConstraints.clear();
  ConstraintsByReason.clear();
  resetEnvironment();
}

bool Constraints::checkInitialEnvSanity() {
  return Environment.checkAssignment(getDefaultSolution());
}

Constraints::Constraints() {
  PrebuiltPtr = new PtrAtom();
  PrebuiltArr = new ArrAtom();
  PrebuiltNTArr = new NTArrAtom();
  PrebuiltWild = new WildAtom();
  ChkCG = new ConstraintsGraph();
  PtrTypCG = new ConstraintsGraph();
}

Constraints::~Constraints() {
  delete PrebuiltPtr;
  delete PrebuiltArr;
  delete PrebuiltNTArr;
  delete PrebuiltWild;
  if (ChkCG != nullptr)
    delete (ChkCG);
  if (PtrTypCG != nullptr)
    delete (PtrTypCG);
}

/* ConstraintsEnv methods */

void ConstraintsEnv::dump(void) const { print(errs()); }

void ConstraintsEnv::print(raw_ostream &O) const {
  O << "ENVIRONMENT: \n";
  for (const auto &V : Environment) {
    V.first->print(O);
    O << " = [";
    O << "Checked=";
    V.second.first->print(O);
    O << ", PtrType=";
    V.second.second->print(O);
    O << "]";
    O << "\n";
  }
}

void ConstraintsEnv::dumpJson(llvm::raw_ostream &O) const {
  bool AddComma = false;
  O << "\"Environment\":[";
  for (const auto &V : Environment) {
    if (AddComma) {
      O << ",\n";
    }
    O << "{\"var\":";
    V.first->dumpJson(O);
    O << ", \"value:\":{\"checked\":";
    V.second.first->dumpJson(O);
    O << ", \"PtrType\":";
    V.second.second->dumpJson(O);
    O << "}}";
    AddComma = true;
  }
  O << "]}";
}

VarAtom *ConstraintsEnv::getFreshVar(VarSolTy InitC, std::string Name,
                                     VarAtom::VarKind VK) {
  VarAtom *NewVA = getOrCreateVar(ConsFreeKey, InitC, Name, VK);
  ConsFreeKey++;
  return NewVA;
}

VarAtom *ConstraintsEnv::getOrCreateVar(ConstraintKey V, VarSolTy InitC,
                                        std::string Name, VarAtom::VarKind VK) {
  VarAtom Tv(V, Name, VK);
  EnvironmentMap::iterator I = Environment.find(&Tv);

  if (I != Environment.end())
    return I->first;
  VarAtom *VA = new VarAtom(Tv);
  Environment[VA] = InitC;
  return VA;
}

VarAtom *ConstraintsEnv::getVar(ConstraintKey V) const {
  VarAtom Tv(V);
  EnvironmentMap::const_iterator I = Environment.find(&Tv);

  if (I != Environment.end())
    return I->first;
  return nullptr;
}

ConstAtom *ConstraintsEnv::getAssignment(Atom *A) {
  if (VarAtom *VA = dyn_cast<VarAtom>(A)) {
    if (UseChecked) {
      return Environment[VA].first;
    }
    return Environment[VA].second;
  }
  assert(dyn_cast<ConstAtom>(A) != nullptr &&
         "This is not a VarAtom or ConstAtom");
  return dyn_cast<ConstAtom>(A);
}

bool ConstraintsEnv::checkAssignment(VarSolTy Sol) {
  for (const auto &EnvVar : Environment) {
    if (EnvVar.second.first != Sol.first ||
        EnvVar.second.second != Sol.second) {
      return false;
    }
  }
  return true;
}

bool ConstraintsEnv::assign(VarAtom *V, ConstAtom *C) {
  auto VI = Environment.find(V);
  if (UseChecked) {
    VI->second.first = C;
  } else {
    VI->second.second = C;
  }
  return true;
}

// Find VarAtoms in the environment that match a predicate.
std::set<VarAtom *> ConstraintsEnv::filterAtoms(VarAtomPred Pred) {
  std::set<VarAtom *> Matches;
  for (const auto &CurrE : Environment) {
    VarAtom *VA = CurrE.first;
    if (Pred(VA))
      Matches.insert(VA);
  }
  return Matches;
}

// Reset solution of all VarAtoms that satisfy the given predicate
//  to be the given ConstAtom.
std::set<VarAtom *> ConstraintsEnv::resetSolution(VarAtomPred Pred,
                                                  ConstAtom *C) {
  std::set<VarAtom *> Unchanged;
  for (auto &CurrE : Environment) {
    VarAtom *VA = CurrE.first;
    if (Pred(VA)) {
      if (UseChecked) {
        CurrE.second.first = C;
      } else {
        CurrE.second.second = C;
      }
    } else {
      Unchanged.insert(VA);
    }
  }
  return Unchanged;
}

void ConstraintsEnv::resetFullSolution(VarSolTy InitC) {
  for (auto &CurrE : Environment) {
    CurrE.second = InitC;
  }
}

// Copy solutions from the ptyp map into the checked one
//   if the checked solution is non-WILD.
void ConstraintsEnv::mergePtrTypes() {
  UseChecked = true;
  for (auto &Elem : Environment) {
    VarAtom *VA = dyn_cast<VarAtom>(Elem.first);
    ConstAtom *CAssign = Elem.second.first;
    if (dyn_cast<WildAtom>(CAssign) == nullptr) {
      ConstAtom *OAssign = Elem.second.second;
      assert(dyn_cast<WildAtom>(OAssign) == nullptr &&
             "Expected a checked pointer type.");
      assign(VA, OAssign);
    }
  }
}
