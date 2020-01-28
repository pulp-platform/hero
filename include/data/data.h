/*
 * Copyright (C) 2019 ETH Zurich, University of Bologna
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


#ifndef __POS_DATA_DATA_H__
#define __POS_DATA_DATA_H__


#ifndef LANGUAGE_ASSEMBLY

#include <archi/pulp.h>

// We cannot use tiny attribute if we use a generic riscv toolchain or LLVM or we there is fc specific memeory (TCDM or L2)
#if (defined(ARCHI_HAS_FC_TCDM) || defined(ARCHI_HAS_L2_ALIAS)) && !defined(__LLVM__) && !defined(__RISCV_GENERIC__)
#define POS_FC_TINY_ATTRIBUTE __attribute__ ((tiny))
#else
#define POS_FC_TINY_ATTRIBUTE
#endif


#define FC_GLOBAL_DATA __attribute__((section(".l2_data")))
#define FC_DATA FC_GLOBAL_DATA

#define PI_FC_TINY FC_DATA

#define PI_L2 __attribute__((section(".l2_data")))
#define L2_DATA PI_L2

#define L1_GLOBAL_DATA __attribute__((section(".data_l1")))
#define L1_DATA L1_GLOBAL_DATA

#ifdef USE_CLUSTER
#define RT_LOCAL_DATA L1_DATA
#else
#define RT_LOCAL_DATA FC_DATA
#endif

#endif



#if defined(ARCHI_HAS_L2)
#ifdef ARCHI_HAS_L2_MULTI
#define POS_NB_ALLOC_L2 3
#else
#define POS_NB_ALLOC_L2 1
#endif
#endif

#ifdef ARCHI_CLUSTER_NB_PE
#define ARCHI_NB_PE ARCHI_CLUSTER_NB_PE
#endif


#include "alloc.h"


#endif
