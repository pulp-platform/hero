// -------------------------------------------------------------------------- //
//                                                                            //
// This file is part of the HERCULES Compiler Passes for PREM transformation  //
// of code. See README and LICENSE for more info.                             //
//                                                                            //
// Copyright (C) 2016-2018 ETH Zurich, Switzerland                            //
//                                                                            //
// -------------------------------------------------------------------------- //
#ifndef OMP_PREPROCESS_H
#define OMP_PREPROCESS_H

#include <llvm/ADT/StringRef.h>
#include <llvm/Analysis/TargetTransformInfo.h>
#include <llvm/IR/Module.h>
#include <llvm/Pass.h>

#include <vector>

namespace hrcl {

class OmpHostPointerLegalizer : public llvm::ModulePass {
public:
  static char ID;
  OmpHostPointerLegalizer() : llvm::ModulePass(ID) {}

  void getAnalysisUsage(llvm::AnalysisUsage &AU) const override {
    AU.addRequired<llvm::TargetTransformInfoWrapperPass>();
  }

  bool runOnModule(llvm::Module &M);
private:
  void expandMemIntrinsicUses(llvm::Function &F);
};

} // namespace hrcl

#endif
