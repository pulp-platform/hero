// -------------------------------------------------------------------------- //
//                                                                            //
// This file is part of the HERCULES Compiler Passes for PREM transformation  //
// of code. See README and LICENSE for more info.                             //
//                                                                            //
// Copyright (C) 2016-2018 ETH Zurich, Switzerland                            //
//                                                                            //
// -------------------------------------------------------------------------- //
#include "OmpHostPointerLegalizer.h"

#include "llvm/Transforms/Utils/LowerMemIntrinsics.h"
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/AbstractCallSite.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InstVisitor.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/Value.h>
#include <llvm/Transforms/IPO.h>
#include <llvm/Transforms/IPO/PassManagerBuilder.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/Transforms/Utils/Cloning.h>

#include <vector>

#define OMP_LOAD_PREFIX "hero_load"
#define OMP_STORE_PREFIX "hero_store"

using namespace llvm;
using namespace hrcl;

static unsigned HostAS = 0;
static unsigned DeviceAS = 0;

class HostPointerVisitor : public InstVisitor<HostPointerVisitor> {
  Module *M;

public:
  HostPointerVisitor(Module *IM) : M(IM) {}

  void visitLoadInst(LoadInst &LI) {
    // Do not modify loads in support functions
    if (LI.getParent()->getParent()->getName().startswith(OMP_LOAD_PREFIX) ||
        LI.getParent()->getParent()->getName().startswith(OMP_STORE_PREFIX)) {
      return;
    }
    // Only convert loads to host address space
    if (LI.getPointerAddressSpace() != HostAS) {
      return;
    }

    // Get relevant types and construct function name
    Type *PST = LI.getPointerOperandType();
    Type *PDT = LI.getType();
    unsigned SS = M->getDataLayout().getTypeAllocSizeInBits(PST);
    unsigned DS = PDT->getPrimitiveSizeInBits();
    if (!DS) {
      DS = M->getDataLayout().getTypeAllocSizeInBits(PDT);
    }
    std::string FName = OMP_LOAD_PREFIX;
    FName += "_uint";
    FName += std::to_string(DS);

    // Create or find load function
    FunctionType *FTy =
        FunctionType::get(Type::getIntNTy(M->getContext(), DS),
                          {Type::getIntNTy(M->getContext(), SS)}, false);
    Value *F = M->getOrInsertFunction(FName, FTy).getCallee();

    // Convert arguments to integers and pass to the load function
    Type *IST = Type::getIntNTy(M->getContext(),
                                M->getDataLayout().getTypeAllocSizeInBits(PST));
    PtrToIntInst *PII = new PtrToIntInst(LI.getPointerOperand(), IST, "", &LI);
    DebugLoc DL = LI.getDebugLoc();
    CallInst *CI = CallInst::Create(FTy, F, {PII}, "", &LI);
    CI->setDebugLoc(DL);
    Instruction *CTI = CI;
    // If the type we are trying to load is not the same as dictated by the
    // hero_store function, we need to cast it. For pointers we use the IntToPtr
    // cast, which preserves the bits, just changes the type.
    // As this instruction can only be used for pointers, we use the bitcast
    // instruction for non-pointer types. This instruction also preserves the
    // bits (i.e., there is no semantic conversion of an integer value to its
    // corresponding float representation), and just changes the IR type of
    // the value.
    if (PDT != CI->getType()) {
      if (PDT->isPointerTy()) {
        assert(PDT->isPointerTy() &&
               "Only loads of pointer and integers are supported");
        CTI = new IntToPtrInst(CI, PDT, "", &LI);
      } else {
        // Bitcasts require the source and destination types to be first-class
        // non-aggregate values. We know the source type is an integer type, so
        // we just assert that the destination type is that as well.
        // FIXME: This was implemented to deal with loading of floats from the
        //        host AS. Possibly we can find a more general solution that
        //        also deals with aggregate types?
        assert(PDT->isFirstClassType() && !PDT->isAggregateType() &&
               "For non-pointer type loads the type must be first-class and "
               "non-aggregate.");
        CTI = new BitCastInst(CI, PDT, "", &LI);
      }
    }

    // Replace load with call
    LI.replaceAllUsesWith(CTI);
    LI.eraseFromParent();
  }

  void visitStoreInst(StoreInst &SI) {
    // Only convert stores to host address space
    if (SI.getPointerAddressSpace() != HostAS) {
      return;
    }

    // Get relevant types and construct function name
    Type *PST = SI.getPointerOperandType();
    Type *PDT = SI.getValueOperand()->getType();
    unsigned SS = M->getDataLayout().getTypeAllocSizeInBits(PST);
    unsigned DS = PDT->getPrimitiveSizeInBits();
    if (!DS) {
      DS = M->getDataLayout().getTypeAllocSizeInBits(PDT);
    }
    std::string FName = OMP_STORE_PREFIX;
    FName += "_uint";
    FName += std::to_string(DS);

    // Create or find store function
    FunctionType *FTy =
        FunctionType::get(Type::getVoidTy(M->getContext()),
                          {Type::getIntNTy(M->getContext(), SS),
                           Type::getIntNTy(M->getContext(), DS)},
                          false);
    Value *F = M->getOrInsertFunction(FName, FTy).getCallee();

    // Convert arguments to integers and pass to the store function
    Type *IST = Type::getIntNTy(M->getContext(),
                                M->getDataLayout().getTypeAllocSizeInBits(PST));
    PtrToIntInst *PII = new PtrToIntInst(SI.getPointerOperand(), IST, "", &SI);
    Value *SVI = SI.getValueOperand();
    // If the type we are trying to store is not the same as dictated by the
    // hero_store function, we need to cast it. For pointers we use the PtrToInt
    // cast, which preserves the bits, just changes the type.
    // As this instruction can only be used for pointers, we use the bitcast
    // instruction for non-pointer types. This instruction also preserves the
    // bits (i.e., there is no semantic conversion of a float value to its
    // corresponding integer representation), and just changes the IR type of
    // the value.
    if (PDT != FTy->getParamType(1)) {
      if (PDT->isPointerTy()) {
        assert(PDT->isPointerTy() &&
               "Only stores of pointer and integers are supported");
        SVI = new
              PtrToIntInst(SI.getValueOperand(), FTy->getParamType(1), "", &SI);
      } else {
        // Bitcasts require the source and destination types to be first-class
        // non-aggregate values. We know the source type is an integer type, so
        // we just assert that the destination type is that as well.
        // FIXME: This was implemented to deal with loading of floats from the
        //        host AS. Possibly we can find a more general solution that
        //        also deals with aggregate types?
        assert(PDT->isFirstClassType() && !PDT->isAggregateType() &&
               "For non-pointer type stores the type must be first-class and "
               "non-aggregate.");
        SVI = new
              BitCastInst(SI.getValueOperand(), FTy->getParamType(1), "", &SI);
      }
    }
    DebugLoc DL = SI.getDebugLoc();
    CallInst *CI = CallInst::Create(FTy, F, {PII, SVI}, "", &SI);
    CI->setDebugLoc(DL);

    // Replace store with call
    SI.replaceAllUsesWith(CI);
    SI.eraseFromParent();
  }

  void visitAddrSpaceCastInst(AddrSpaceCastInst &AI) {
    // Only modify generic <-> host address space pairs
    auto AS = std::make_pair(AI.getSrcAddressSpace(), AI.getDestAddressSpace());
    if (AS.second < AS.first)
      std::swap(AS.second, AS.first);
    if (!(AS.first == (unsigned)std::min(HostAS, DeviceAS) &&
          AS.second == (unsigned)std::max(HostAS, DeviceAS))) {
      return;
    }

    Type *PDT = AI.getType();
    unsigned DS = M->getDataLayout().getTypeAllocSizeInBits(PDT);
    Type *IDT = Type::getIntNTy(M->getContext(), DS);

    // Convert to integer with appropriate size
    PtrToIntInst *PII = new PtrToIntInst(AI.getPointerOperand(), IDT, "", &AI);

    // Convert modified integer back to pointer
    IntToPtrInst *IPI = new IntToPtrInst(PII, AI.getType(), "", &AI);

    // Replace address space cast
    AI.replaceAllUsesWith(IPI);
    AI.eraseFromParent();
  }
};

static void handleConstExpr(ConstantExpr *CE, HostPointerVisitor &HPV,
                            Module *M) {
  // Replace address space conversion
  if (CE->getOpcode() == Instruction::AddrSpaceCast) {
    Type *PST = CE->getOperand(0)->getType();
    Type *PDT = CE->getType();

    // Check if we need to legalize
    auto AS = std::make_pair(PST->getPointerAddressSpace(),
                             PDT->getPointerAddressSpace());
    if (AS.second < AS.first)
      std::swap(AS.second, AS.first);
    if (!(AS.first == (unsigned)std::min(HostAS, DeviceAS) &&
          AS.second == (unsigned)std::max(HostAS, DeviceAS))) {
      return;
    }

    unsigned DS = M->getDataLayout().getTypeAllocSizeInBits(PDT);
    Type *IDT = Type::getIntNTy(M->getContext(), DS);

    // Convert to integer with appropriate size
    Constant *PII = ConstantExpr::getPtrToInt(CE->getOperand(0), IDT);

    // Convert modified integer back to pointer
    Constant *IPI = ConstantExpr::getIntToPtr(PII, PDT);

    // Replace the constant expression
    CE->replaceAllUsesWith(IPI);
  }

  for (auto &Ops : CE->operands()) {
    auto NCE = dyn_cast<ConstantExpr>(Ops.get());
    if (!NCE) {
      continue;
    }
    handleConstExpr(NCE, HPV, M);
  }
}

// The ugly expandMem*AsLoop functions don't return a handle, so after each time
// such a function is called we need to go through the function and add it.
void addDbgMetadataToCallsIfNonePresent(Function &F, DebugLoc &DL) {
  for (BasicBlock &BB : F) {
    for (Instruction &I : BB) {
      if (I.getMetadata("dbg") == nullptr) {
        I.setDebugLoc(DL);
      }
    }
  }
}

void OmpHostPointerLegalizer::expandMemIntrinsicUses(Function &F) {
  llvm::Intrinsic::ID IID = F.getIntrinsicID();

  for (auto I = F.user_begin(), E = F.user_end(); I != E;) {
    Instruction *Inst = cast<Instruction>(*I);
    Function &userF = *Inst->getParent()->getParent();
    ++I;

    switch (IID) {
    case Intrinsic::memcpy: {
      auto *Memcpy = cast<MemCpyInst>(Inst);
      if (Memcpy->getSourceAddressSpace() == DeviceAS &&
          Memcpy->getDestAddressSpace() == DeviceAS) {
        break;
      }
      Function *ParentFunc = Memcpy->getParent()->getParent();
      const TargetTransformInfo &TTI =
          getAnalysis<TargetTransformInfoWrapperPass>().getTTI(*ParentFunc);
      DebugLoc DL = Memcpy->getDebugLoc();
      expandMemCpyAsLoop(Memcpy, TTI);
      addDbgMetadataToCallsIfNonePresent(userF, DL);
      Memcpy->eraseFromParent();
      break;
    }
    case Intrinsic::memmove: {
      auto *Memmove = cast<MemMoveInst>(Inst);
      if (Memmove->getSourceAddressSpace() == DeviceAS &&
          Memmove->getDestAddressSpace() == DeviceAS) {
        break;
      }
      DebugLoc DL = Memmove->getDebugLoc();
      expandMemMoveAsLoop(Memmove);
      addDbgMetadataToCallsIfNonePresent(userF, DL);
      Memmove->eraseFromParent();
      break;
    }
    case Intrinsic::memset: {
      auto *Memset = cast<MemSetInst>(Inst);
      if (Memset->getDestAddressSpace() == DeviceAS) {
        break;
      }
      DebugLoc DL = Memset->getDebugLoc();
      expandMemSetAsLoop(Memset);
      addDbgMetadataToCallsIfNonePresent(userF, DL);
      Memset->eraseFromParent();
      break;
    }
    default:
      break;
    }
  }
}

bool OmpHostPointerLegalizer::runOnModule(Module &M) {
  DeviceAS = M.getDataLayout().getProgramAddressSpace();
  if (DeviceAS == 0) {
    HostAS = 1;
  } else {
    HostAS = 0;
  }

  // Patch memory intrinsics
  for (auto &Func : M) {
    if (!Func.isIntrinsic()) {
      continue;
    }
    expandMemIntrinsicUses(Func);
  }

  // Patch instructions
  HostPointerVisitor HPV(&M);
  HPV.visit(M);

  // Patch constant expressions in functions and globals
  // FIXME: there is a lack of functionality to iterate over ConstantExprs
  for (auto &Func : M) {
    for (auto &Block : Func) {
      for (auto &Inst : Block) {
        for (auto &Op : Inst.operands()) {
          auto CE = dyn_cast<ConstantExpr>(Op.get());
          if (CE) {
            handleConstExpr(CE, HPV, &M);
          }
        }
      }
    }
  }

  return true;
}

char OmpHostPointerLegalizer::ID = 3;
static RegisterPass<OmpHostPointerLegalizer>
    Xmark("HERCULES-omp-host-pointer-legalizer",
          "Legalize host pointers to 64-bit address space to support functions",
          true, false);

static void registerMyPass(const PassManagerBuilder &PMB,
                           legacy::PassManagerBase &PM) {}

static RegisterStandardPasses
    RegisterMyPass(PassManagerBuilder::EP_ModuleOptimizerEarly, registerMyPass);
static RegisterStandardPasses
    RegisterMyPass0(PassManagerBuilder::EP_EnabledOnOptLevel0, registerMyPass);
