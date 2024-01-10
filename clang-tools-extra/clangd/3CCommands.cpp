//=--3CCommands.cpp-----------------------------------------------*- C++-*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
// Implementation of 3C command helper methods.
//===----------------------------------------------------------------------===//

#ifdef LSP3C
#include "3CCommands.h"
#include "support/Logger.h"

namespace clang {
namespace clangd {

#define _3CSOURCE "3C_RealWild"

static bool GetPtrIDFromDiagMessage(const Diagnostic &DiagMsg,
                                    unsigned long &PtrId) {
  if (DiagMsg.source.rfind(_3CSOURCE, 0) == 0) {
    PtrId = atoi(DiagMsg.code.c_str());
    return true;
  }
  return false;
}

void AsCCCommands(const Diagnostic &D, std::vector<Command> &OutCommands) {
  unsigned long PtrId;
  if (GetPtrIDFromDiagMessage(D, PtrId)) {
    Command AllPtrsCmd;
    _3CManualFix PtrFix;
    PtrFix.ptrID = PtrId;
    AllPtrsCmd._3CFix = PtrFix;
    Command SinglePtrCmd = AllPtrsCmd;

    AllPtrsCmd.command = ExecuteCommandParams::_3C_APPLY_FOR_ALL.str();
    AllPtrsCmd.title = "Make this pointer non-WILD and apply the "
                       "same observation to all the pointers.";

    OutCommands.push_back(AllPtrsCmd);

    SinglePtrCmd.command = Command::_3C_APPLY_ONLY_FOR_THIS.str();
    SinglePtrCmd.title = "Make ONLY this pointer non-WILD.";

    OutCommands.push_back(SinglePtrCmd);
  }
}

bool Is3CCommand(const ExecuteCommandParams &Params) {
  return (Params.command.rfind(Command::_3C_APPLY_ONLY_FOR_THIS.str(), 0) == 0) ||
         (Params.command.rfind(Command::_3C_APPLY_FOR_ALL.str(), 0) == 0);
}

bool ExecuteCCCommand(const ExecuteCommandParams &Params,
                      std::string &ReplyMessage,
                      _3CInterface &CcInterface) {
  ReplyMessage = "Checked C Pointer Modified.";
  if (Params.command.rfind(Command::_3C_APPLY_ONLY_FOR_THIS.str(), 0) == 0) {
    int PtrId = Params._3CFix->ptrID;
    /*CcInterface.makeSinglePtrNonWild(PtrId);*/
    log("Single Pointer Wild.");
    return true;
  }
  if (Params.command.rfind(Command::_3C_APPLY_FOR_ALL.str(), 0) == 0) {
    int PtrId = Params._3CFix->ptrID;
    log("Global Pointer Wild.");
    return true;
  }
  return false;
}
}
}
#endif