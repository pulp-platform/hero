/*
 * Copyright (C) 2017 ETH Zurich and University of Bologna
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef __VMM_HOST_H__
#define __VMM_HOST_H__

// This header file defines how the host configures the RAB at offload so that PULP can manage the
// TLBs at run time.

#include "archi/rab/rab_v1.h"

// The following RAB slices are set up by the host at offload time.  They are thus static from the
// perspective of PULP and we should not change them in the Virtual Memory Management code.
#define RAB_CFG_STAT_L3_PTR     ((RAB_CFG_BPTR))
#define RAB_CFG_STAT_PGD_PTR    ((RAB_CFG_STAT_L3_PTR) + 1)
#ifndef HOST_ARCH
    #error "Define HOST_ARCH!"
#endif
#if HOST_ARCH == ARM64
    #ifdef STATIC_PMD_SLICES
        #define RAB_CFG_PTE_PTR     ((RAB_CFG_STAT_PGD_PTR) + N_STATIC_PMD_SLICES)
    #else
        #define RAB_CFG_PMD_PTR     ((RAB_CFG_STAT_PGD_PTR) + 1)
        #define RAB_CFG_PTE_PTR     ((RAB_CFG_PMD_PTR) + 1)
    #endif
#elif HOST_ARCH == ARM
    #define RAB_CFG_PTE_PTR     ((RAB_CFG_STAT_PGD_PTR) + 1)
#elif HOST_ARCH == RISCV64
    #define RAB_CFG_PTE_PTR     ((RAB_CFG_STAT_PGD_PTR) + 1)
#else
    #error "Unknown host architecture!"
#endif

#endif
