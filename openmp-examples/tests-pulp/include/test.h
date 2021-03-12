/*
 * Copyright 2019 ETH Zurich, University of Bologna
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

#ifndef __TEST_H__
#define __TEST_H__

#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>

static unsigned condition_or_printf(bool condition, const char* fmt, ...)
{
  if (!condition) {
    va_list args;
    va_start(args, fmt);
    char buf[256];
    vsnprintf(buf, sizeof(buf), fmt, args);
    printf("ERROR: %s!\n", buf);
    return 1;
  } else {
    return 0;
  }
}

inline __device static void* pulp_l1_base()
{
  extern void __pulp_l1_base;
  return &__pulp_l1_base;
}

inline __device static void* pulp_l1_end()
{
  extern void __pulp_l1_end;
  return &__pulp_l1_end;
}

inline __device static void* pulp_l1_alias_base()
{
  extern void __pulp_l1_alias_base;
  return &__pulp_l1_alias_base;
}

inline __device static void* pulp_l1_alias_end()
{
  extern void __pulp_l1_alias_end;
  return &__pulp_l1_alias_end;
}

inline __device static void* pulp_l2_base()
{
  extern void __pulp_l2_base;
  return &__pulp_l2_base;
}

inline __device static void* pulp_l2_end()
{
  extern void __pulp_l2_end;
  return &__pulp_l2_end;
}

inline static unsigned pulp_l2_size()
{
  return (unsigned)pulp_l2_end() - (unsigned)pulp_l2_base();
}

inline static unsigned pulp_cluster_n_cores()
{
  extern void __rt_nb_pe;
  return (unsigned)&__rt_nb_pe;
}

inline static unsigned pulp_n_clusters()
{
  extern void __rt_nb_cluster;
  return (unsigned)&__rt_nb_cluster;
}

inline static size_t pulp_stack_size()
{
  extern void __rt_stack_size;
  return (size_t)&__rt_stack_size;
}

inline static void* pulp_cluster_base(const unsigned cluster_id)
{
  extern void __pulp_cluster_size;
  return pulp_l1_base() + cluster_id * (unsigned)&__pulp_cluster_size;
}

inline static uint64_t align_64(uint64_t addr)
{
  return (addr >> 3) << 3;
}

inline static uint64_t test_l1_base()
{
  return align_64((uint64_t)pulp_l1_end() - pulp_cluster_n_cores()*pulp_stack_size());
}

inline static uint64_t test_l1_alias_base()
{
  return align_64((uint64_t)pulp_l1_alias_end() - pulp_cluster_n_cores()*pulp_stack_size());
}

inline static uint64_t test_l1_other_base()
{
  return align_64((uint64_t)pulp_cluster_base(1) + 0x1000);
}
inline static uint64_t test_l2_base()
{
  return align_64((uint64_t)pulp_l2_end() - 0x1000);
}

inline static uint64_t test_dram_base()
{
  return align_64(0x80000000);
}

inline static uint64_t test_dram_64bit_addr()
{
  return align_64(0x123480000000);
}

#endif
