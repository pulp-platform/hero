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

#ifndef __POS_IMPLEM_IMPLEM_H__
#define __POS_IMPLEM_IMPLEM_H__

#define   likely(x) __builtin_expect(x, 1)
#define unlikely(x) __builtin_expect(x, 0)

#define PI_PLATFORM_OTHER 0
#define PI_PLATFORM_FPGA  1
#define PI_PLATFORM_RTL   2
#define PI_PLATFORM_GVSOC 3
#define PI_PLATFORM_BOARD 4

static int pi_platform()
{
    return __PLATFORM__;
}


#if defined(ARCHI_HAS_CLUSTER)

static inline int pos_nb_cluster()
{
#ifndef ARCHI_NB_CLUSTER
    return 1;
#else
    return ARCHI_NB_CLUSTER;
#endif
}

#endif

extern int pos_kernel_pmsis_exit_value;


static inline int pmsis_kickoff(void *arg)
{
    ((void (*)())arg)();
    return pos_kernel_pmsis_exit_value;
}

static inline void pmsis_exit(int err)
{
    pos_kernel_pmsis_exit_value = err;
}

#ifdef ARCHI_HAS_CLUSTER

static inline unsigned int tas_addr(unsigned int addr)
{
  return addr | (1<<ARCHI_L1_TAS_BIT);
}

static inline int tas_lock_32(unsigned int addr)
{
  __asm__ __volatile__ ("" : : : "memory");
  signed int result = *(volatile signed int *)tas_addr(addr);
  __asm__ __volatile__ ("" : : : "memory");
  return result;
}

static inline void tas_unlock_32(unsigned int addr, signed int value)
{
  __asm__ __volatile__ ("" : : : "memory");
  *(volatile signed int *)addr = value;
  __asm__ __volatile__ ("" : : : "memory");
}

#endif

#include "alloc.h"
#include "irq.h"
#include "link.h"
#include "soc_event.h"
#include "alloc.h"
#include "alloc_pool.h"
#include "soc.h"
#include "freq.h"

#endif