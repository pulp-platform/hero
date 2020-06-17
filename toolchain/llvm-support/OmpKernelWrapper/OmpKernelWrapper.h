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
#include <llvm/IR/Module.h>
#include <llvm/Pass.h>

#include <vector>

namespace hero {

class OmpKernelWrapper : public llvm::ModulePass {
private:
  void changeTypeOfArgSizes(llvm::Module &M, llvm::StringRef fnName,
                            unsigned int argIdx);
  void wrapOmpKernels(llvm::Module &M);

  void wrapOmpOutlinedFuncs(llvm::Module &M);

public:
  static char ID;
  OmpKernelWrapper() : llvm::ModulePass(ID) {}

  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const;
  bool runOnModule(llvm::Module &M);
};

llvm::Pass *createOmpKernelWrapper();

} // namespace hrcl

#endif
