//=--AvarBoundsConflictResolver.cpp-------------------------------*- C++-*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Implementation of methods in AVarBoundsConflictResolver.h.
//
//===----------------------------------------------------------------------===//

#include "clang/3C/AVarBoundsConflictResolver.h"

void AVarBoundsConflictResolver::seedInitialWorkList(AVarBoundsInfo *BI, AVarGraph &BKGraph,
                                                     std::set<BoundsKey> &WorkList){
  AvarBoundsInference ABI(BI);
  // Make sure previous inference does not interfere.
  ABI.clearInferredBounds();
  for(auto *Node = BKGraph.begin(); Node!= BKGraph.end(); Node++){
    BoundsKey Curr =  (*Node)->getData();
    ABounds *OldABounds = BI->getBounds(Curr, BoundsPriority::FlowInferred);
    if(OldABounds){
      OldABounds = OldABounds->makeCopy(OldABounds->getLengthKey());
      BI->removeBounds(Curr, BoundsPriority::FlowInferred);
      ABI.inferBounds(Curr, BKGraph, false);
      ABI.convergeInferredBounds();
      ABI.clearInferredBounds();
      ABounds *NewABounds = BI->getBounds(Curr, BoundsPriority::FlowInferred);
      // If the node does not have FlowInferred bounds or
      // it has a bounds which is different from the previous one,
      // then we add the node to WorkList.
      if(!NewABounds || !NewABounds->areSame(OldABounds, BI)){
        WorkList.insert(Curr);
        // If we got conflicting bounds, we don't want to keep it
        // since we assume this node's bounds is unknown when we add it to
        // the WorkList. 
        // TODO:
        //  Verify if this is correct method.
        if(NewABounds)
          BI->removeBounds(Curr, BoundsPriority::FlowInferred);
      }
      delete OldABounds;
    }
  }
}

void AVarBoundsConflictResolver::propogateConflicts(const BoundsKey &N, AVarBoundsInfo *BI,
                                                    AVarGraph &BKGraph, std::set<BoundsKey> &WorkList){
  std::set<BoundsKey> SuccKeys;
  AvarBoundsInference ABI(BI);
  BKGraph.getSuccessors(N, SuccKeys);
  ABI.clearInferredBounds();
  for(auto &S: SuccKeys){
    ABounds *OldABounds = BI->getBounds(S, BoundsPriority::FlowInferred);
    if(OldABounds){
      OldABounds = OldABounds->makeCopy(OldABounds->getLengthKey());
      BI->removeBounds(S, BoundsPriority::FlowInferred);
      ABI.inferBounds(S, BKGraph, false);
      ABI.convergeInferredBounds();
      ABI.clearInferredBounds();
      ABounds *NewABounds = BI->getBounds(S, BoundsPriority::FlowInferred);
      if(!NewABounds || !NewABounds->areSame(OldABounds, BI)){
        WorkList.insert(S);
      }
      delete OldABounds;
    }
  }
}

void AVarBoundsConflictResolver::resolveConflicts(AVarBoundsInfo *BI){
  std::set<BoundsKey> WorkList;
  std::set<BoundsKey> OldWorkList;
  
  // Find initial conflicts from ProgVarGraph and add it to WorkList
  seedInitialWorkList(BI, BI->getProgVarGraph(), WorkList);
  // Find initial conflicts from CtxSensProgVarGraph and add it to WorkList
  // seedInitialWorkList(BI, BI->getCtxSensProgVarGraph(), WorkList);
  // Find initial conflicts from RevCtxSensProgVarGraph and add it to WorkList
  // seedInitialWorkList(BI, BI->getRevCtxSensProgVarGraph(), WorkList);
  
  bool WorkListChanged = WorkList != OldWorkList;
  OldWorkList = WorkList;

  while(WorkListChanged){
    for(auto &N: OldWorkList){
      // Propogate conflicts in ProgVarGraph
      propogateConflicts(N, BI, BI->getProgVarGraph(), WorkList);
      // Propogate conflicts in CtxSensProgVarGraph
      propogateConflicts(N, BI, BI->getCtxSensProgVarGraph(), WorkList);
      // Propogate conflicts in RevCtxSensProgVarGraph
      propogateConflicts(N, BI, BI->getRevCtxSensProgVarGraph(), WorkList);
    }
    WorkListChanged = OldWorkList != WorkList;
    OldWorkList = WorkList;
  }
}