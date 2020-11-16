//===--- omptarget-nvptx.cu - NVPTX OpenMP GPU initialization ---- CUDA -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is dual licensed under the MIT and the University of Illinois Open
// Source Licenses. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
//
// This file contains the initialization code for the GPU
//
//===----------------------------------------------------------------------===//

#include "omptarget-pulp.h"

////////////////////////////////////////////////////////////////////////////////
// init entry points
////////////////////////////////////////////////////////////////////////////////

EXTERN void __kmpc_kernel_init_params(void *Ptr) {
}

EXTERN void __kmpc_kernel_init(int ThreadLimit, int16_t RequiresOMPRuntime) {
}

EXTERN void __kmpc_kernel_deinit(int16_t IsOMPRuntimeInitialized) {
}

EXTERN void __kmpc_spmd_kernel_init(int ThreadLimit, int16_t RequiresOMPRuntime,
                                    int16_t RequiresDataSharing) {
}

EXTERN void __kmpc_spmd_kernel_deinit() {
}

EXTERN int8_t __kmpc_is_spmd_exec_mode() {
  return false;
}
