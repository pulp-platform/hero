// -------------------------------------------------------------------------- //
//                                                                            //
// This file is part of the HERCULES Compiler Passes for PREM transformation  //
// of code. See README and LICENSE for more info.                             //
//                                                                            //
// Copyright (C) 2016-2018 ETH Zurich, Switzerland                            //
//                                                                            //
// -------------------------------------------------------------------------- //
#include "OmpKernelWrapper.h"

#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/Value.h>
#include <llvm/Transforms/IPO.h>
#include <llvm/Transforms/IPO/PassManagerBuilder.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>

#include <array>

#define OMP_WRAPPER_PREFIX "__wrapper_omp"
#define OMP_WRAPPED_PREFIX "__wrapped_omp"

using namespace llvm;
using namespace hero;

std::vector<llvm::CallInst *> getKMPForkCalls(llvm::Module &M) {
  Function *kfc = M.getFunction("__kmpc_fork_call");
  if (!kfc) {
    return {};
  }

  std::vector<llvm::CallInst *> calls;
  for (Use &use : kfc->uses()) {
    CallInst *invc = dyn_cast<CallInst>(use.getUser());
    if (!invc) {
      continue;
    }
    calls.push_back(invc);
  }
  return calls;
}

std::vector<GlobalVariable *> getOmpOffloadEntries(Module &M) {
  std::vector<GlobalVariable *> entries;
  for (auto &G : M.globals()) {
    if (G.getName().startswith(".omp_offloading.entry.")) {
      entries.push_back(&G);
    }
  }
  return entries;
}

Function *getOmpOffloadFunction(GlobalVariable *offloadingEntry) {
  ConstantStruct *initializer =
      dyn_cast<ConstantStruct>(offloadingEntry->getInitializer());
  Constant *fnPtrs = dyn_cast<Constant>(initializer->getOperand(0));
  return dyn_cast_or_null<Function>(fnPtrs->stripPointerCasts());
}

Optional<GlobalVariable *> getOmpOffloadEntry(Function *kernel) {
  Module *M = kernel->getParent();
  for (auto &G : M->globals()) {
    if (G.getName().startswith(".omp_offloading.entry.")) {
      if (getOmpOffloadFunction(&G) == kernel) {
        return Optional<GlobalVariable *>(&G);
      }
    }
  }
  return Optional<GlobalVariable *>(None);
}

void setOmpOffloadFunction(GlobalVariable *offloadingEntry,
                                 Function *newKernel) {
  ConstantStruct *initializer =
      dyn_cast<ConstantStruct>(offloadingEntry->getInitializer());
  Constant *fnPtrs = dyn_cast<Constant>(initializer->getOperand(0));

  Value *castKernel =
      ConstantExpr::getPointerCast(newKernel, fnPtrs->getOperand(0)->getType());
  fnPtrs->handleOperandChange(fnPtrs->getOperand(0), castKernel);
}

void OmpKernelWrapper::getAnalysisUsage(AnalysisUsage &AU) const {}

bool OmpKernelWrapper::runOnModule(Module &M) {
  // Workaround to convert arg_sizes arrays from i32* to i64*
  if (M.getTargetTriple() == "armv6kz-unknown-linux-gnueabihf") {
    this->changeTypeOfArgSizes(M, "__tgt_target_data_begin", 4);
    this->changeTypeOfArgSizes(M, "__tgt_target_data_begin_nowait", 4);
    this->changeTypeOfArgSizes(M, "__tgt_target_data_begin_depend", 4);
    this->changeTypeOfArgSizes(M, "__tgt_target_data_begin_nowait_depend", 4);

    this->changeTypeOfArgSizes(M, "__tgt_target_data_end", 4);
    this->changeTypeOfArgSizes(M, "__tgt_target_data_end_nowait", 4);
    this->changeTypeOfArgSizes(M, "__tgt_target_data_end_depend", 4);
    this->changeTypeOfArgSizes(M, "__tgt_target_data_end_nowait_depend", 4);

    this->changeTypeOfArgSizes(M, "__tgt_target_data_update", 4);
    this->changeTypeOfArgSizes(M, "__tgt_target_data_update_nowait", 4);
    this->changeTypeOfArgSizes(M, "__tgt_target_data_update_depend", 4);
    this->changeTypeOfArgSizes(M, "__tgt_target_data_update_nowait_depend", 4);

    this->changeTypeOfArgSizes(M, "__tgt_target", 5);
    this->changeTypeOfArgSizes(M, "__tgt_target_nowait", 5);
    this->changeTypeOfArgSizes(M, "__tgt_target_teams", 5);
    this->changeTypeOfArgSizes(M, "__tgt_target_teams_nowait", 5);
  }

  if (M.getTargetTriple() == "riscv32-hero-unknown-elf") {
    this->wrapOmpKernels(M);
    this->wrapOmpOutlinedFuncs(M);
  }
  return true;
}

std::pair<Value *, GlobalVariable *> rebuildArgSizesArgument(Module &M,
                                                             Value *arg_sizes) {
  Type *i32 = Type::getInt32Ty(M.getContext());
  Type *i64 = Type::getInt64Ty(M.getContext());
  PointerType *i64p = i64->getPointerTo();

  if (isa<ConstantPointerNull>(arg_sizes)) {
    return std::make_pair(ConstantPointerNull::get(i64p), nullptr);
  } else {
    GEPOperator *arg_sizes_gep = dyn_cast<GEPOperator>(arg_sizes);

    // @.offload_sizes = private unnamed_addr constant [n x i32] [..]
    GlobalVariable *offload_sizes =
        dyn_cast<GlobalVariable>(arg_sizes_gep->getOperand(0));
    ArrayType *oldTy =
        dyn_cast<ArrayType>(offload_sizes->getType()->getPointerElementType());
    Type *newTy = ArrayType::get(i64, oldTy->getNumElements());

    // [n x i32] [..]
    Constant *initializer = offload_sizes->getInitializer();
    Constant *new_initializer = nullptr;

    if (isa<ConstantDataArray>(initializer)) {
      ConstantDataArray *old_data = dyn_cast<ConstantDataArray>(initializer);
      SmallVector<uint64_t, 8> content;
      for (unsigned int i = 0; i < old_data->getNumElements(); i++) {
        content.push_back(old_data->getElementAsInteger(i));
      }

      new_initializer = ConstantDataArray::get(M.getContext(), content);
    } else if (isa<ConstantAggregateZero>(initializer)) {
      new_initializer = ConstantAggregateZero::get(newTy);
    } else {
      assert(false && "unexpected constant type");
    }

    GlobalVariable *new_offload_sizes =
        new GlobalVariable(M, newTy, true, GlobalValue::PrivateLinkage,
                           new_initializer, "new_offload_sizes");

    // remove arg_sizes GEPO and replace
    Value *index = ConstantInt::get(i32, 0);
    Value *arg_sizes_new = ConstantExpr::getInBoundsGetElementPtr(
        newTy, new_offload_sizes, {index, index});

    return std::make_pair(arg_sizes_new, offload_sizes);
  }
}

// Workaround for OpenMP bug on ARM32:
// Replaces i32 type of arg_sizes argument in __tgt_target with i64 to match
// interface in omptarget.h
void OmpKernelWrapper::changeTypeOfArgSizes(Module &M, StringRef fnName,
                                            unsigned int argIdx) {
  Function *tgt_target = M.getFunction(fnName);
  if (!tgt_target) {
    return;
  }

  Type *i64 = Type::getInt64Ty(M.getContext());
  Type *i64p = i64->getPointerTo();

  // int __tgt_target(int64_t device_id, void *host_ptr, int32_t arg_num,
  //                  void **args_base, void **args, int64_t *arg_sizes,
  //                  int64_t *arg_types);
  FunctionType *FT = tgt_target->getFunctionType();
  SmallVector<Type *, 9> paramTypes;
  for (unsigned int i = 0; i < FT->getNumParams(); i++) {
    if (i != argIdx) {
      paramTypes.push_back(FT->getParamType(i));
    } else {
      paramTypes.push_back(i64p);
    }
  }

  FunctionType *FT_new =
      FunctionType::get(FT->getReturnType(), paramTypes, false);
  Function *tgt_target_new = Function::Create(FT_new, Function::ExternalLinkage,
                                              "__tgt_target_new", &M);

  for (Use &use : tgt_target->uses()) {
    CallInst *invocation = dyn_cast<CallInst>(use.getUser());

    // i32* getelementptr inbounds ([n x i32], [n x i32]* @.offload_sizes, i32
    // 0, i32 0)
    Value *arg_sizes = invocation->getArgOperand(argIdx);
    Value *arg_sizes_new;
    GlobalVariable *offload_sizes;
    std::tie(arg_sizes_new, offload_sizes) =
        rebuildArgSizesArgument(M, arg_sizes);

    // create new call instruction
    SmallVector<Value *, 9> args;
    for (unsigned int i = 0; i < FT->getNumParams(); i++) {
      if (i != argIdx) {
        args.push_back(invocation->getArgOperand(i));
      } else {
        args.push_back(arg_sizes_new);
      }
    }

    CallInst *invocation_new =
        CallInst::Create(tgt_target_new, args, "", invocation);
    invocation->replaceAllUsesWith(invocation_new);

    invocation->eraseFromParent();
    if (offload_sizes && offload_sizes->use_empty()) {
      offload_sizes->eraseFromParent();
    }
  }

  tgt_target->eraseFromParent();
  tgt_target_new->setName(fnName);
}

// Find OMP kernels and wrap list of T* args to single void** arg:
// fn(A*, B*, C*) => fn(void**)
void OmpKernelWrapper::wrapOmpKernels(Module &M) {
  unsigned DeviceAS = M.getDataLayout().getProgramAddressSpace();
  unsigned HostAS = 1;
  if (DeviceAS == 0) {
    HostAS = 1;
  } else {
    HostAS = 0;
  }
  Type *rawArgTy = Type::getInt64Ty(M.getContext());
  Type *argTy = Type::getInt64Ty(M.getContext())->getPointerTo(HostAS);
  Type *voidTy = Type::getVoidTy(M.getContext());
  FunctionType *wrapperTy = FunctionType::get(voidTy, {rawArgTy}, false);

  for (GlobalVariable *entry : getOmpOffloadEntries(M)) {
    Function *kernel = getOmpOffloadFunction(entry);
    if (kernel == nullptr) {
      // This is not a function, but some other global variable defined in a
      // target declare section.
      continue;
    }
    Function *wrapper =
        Function::Create(wrapperTy, Function::WeakAnyLinkage,
                         OMP_WRAPPER_PREFIX + kernel->getName(), &M);

    // begin building body of wrapper function
    IRBuilder<> builder(M.getContext());
    BasicBlock *BB = BasicBlock::Create(M.getContext(), "entry", wrapper);
    builder.SetInsertPoint(BB);

    Value *rawArg = &(*(wrapper->arg_begin()));
    Value *arg = builder.CreateIntToPtr(rawArg, argTy);
    FunctionType *kernelTy = kernel->getFunctionType();

    // dereference arguments from buffer and cast to respective pointer types
    SmallVector<Value *, 8> derefArgs;
    for (unsigned int i = 0; i < kernelTy->getNumParams(); i++) {
      Value *index = ConstantInt::get(Type::getInt32Ty(M.getContext()), i);

      // ptr to ptr to argument of type i8
      Value *argBufPtr = builder.CreateGEP(arg, {index});

      // cast ptr to ptr type to parameter type
      Type *paramType = kernelTy->getParamType(i);
      Value *paramPtr =
          builder.CreateBitCast(argBufPtr, paramType->getPointerTo(HostAS));

      // load parameter
      Value *param = builder.CreateLoad(paramPtr);
      derefArgs.push_back(param);
    }

    // Call original kernel, finish function
    builder.CreateCall(kernel, derefArgs);
    builder.CreateRetVoid();

    // replace function in OpenMP offload table
    setOmpOffloadFunction(entry, wrapper);

    std::string oldName = kernel->getName().str();
    kernel->setName(OMP_WRAPPED_PREFIX + oldName);
    wrapper->setName(oldName);
  }
}

// Find OMP kernels and wrap list of T* args to single void** arg:
// fn(A*, B*, C*) => fn(void**)
void OmpKernelWrapper::wrapOmpOutlinedFuncs(Module &M) {
  unsigned DeviceAS = M.getDataLayout().getProgramAddressSpace();
  Type *argTy = Type::getInt8PtrTy(M.getContext(), DeviceAS)->getPointerTo(DeviceAS);
  Type *thdTy = Type::getInt32Ty(M.getContext())->getPointerTo(DeviceAS);
  Type *voidTy = Type::getVoidTy(M.getContext());
  FunctionType *wrapperTy =
      FunctionType::get(voidTy, {thdTy, thdTy, argTy}, false);

  for (CallInst *CAI : getKMPForkCalls(M)) {
    Function *kernel =
        dyn_cast<Function>(CAI->getArgOperand(2)->stripPointerCasts());
    if (!kernel) {
      continue;
    }

    // Create replacement wrapper function if not existent yet
    std::string funcName = (OMP_WRAPPER_PREFIX + kernel->getName()).str();
    Function *wrapper = M.getFunction(funcName);
    if (wrapper == nullptr) {
      wrapper =
          Function::Create(wrapperTy, Function::PrivateLinkage, funcName, M);

      // begin building body of wrapper function
      BasicBlock *BB = BasicBlock::Create(M.getContext(), "entry", wrapper);
      IRBuilder<> builder(BB);

      Value *arg = wrapper->arg_begin() + 2;
      FunctionType *kernelTy = kernel->getFunctionType();

      // dereference arguments from buffer and cast to respective pointer types
      SmallVector<Value *, 10> derefArgs;
      derefArgs.push_back(wrapper->arg_begin());
      derefArgs.push_back(wrapper->arg_begin() + 1);

      for (unsigned int i = 2; i < kernelTy->getNumParams(); i++) {
        Value *index =
            ConstantInt::get(Type::getInt32Ty(M.getContext()), i - 2);

        // ptr to ptr to argument of type i8
        Value *argBufPtr = builder.CreateGEP(arg, {index});

        // cast ptr to ptr type to parameter type
        Type *paramType = kernelTy->getParamType(i);
        Value *paramPtr =
            builder.CreateBitCast(argBufPtr, paramType->getPointerTo(DeviceAS));

        // load parameter
        Value *param = builder.CreateLoad(paramPtr);
        derefArgs.push_back(param);
      }

      // call original kernel, finish function
      builder.CreateCall(kernel, derefArgs);
      builder.CreateRetVoid();
    }

    // replace argument with the wrapper function
    Constant *bc =
        ConstantExpr::getPointerCast(wrapper, CAI->getArgOperand(2)->getType());
    CAI->setArgOperand(2, bc);
  }
}

char OmpKernelWrapper::ID = 1;
static RegisterPass<OmpKernelWrapper>
    Xmark("HERCULES-omp-kernel-wrapper",
          "Wraps OpenMP kernels in special functions", true, false);

static void registerMyPass(const PassManagerBuilder &PMB,
                           legacy::PassManagerBase &PM) {}

static RegisterStandardPasses
    RegisterMyPass(PassManagerBuilder::EP_ModuleOptimizerEarly, registerMyPass);
static RegisterStandardPasses
    RegisterMyPass0(PassManagerBuilder::EP_EnabledOnOptLevel0, registerMyPass);

llvm::Pass *hero::createOmpKernelWrapper() { return new OmpKernelWrapper(); }
