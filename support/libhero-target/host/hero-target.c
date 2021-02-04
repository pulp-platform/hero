/*
* Copyright (C) 2018 ETH Zurich and University of Bologna
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

#include <hero-target.h>
#include <assert.h>
#include <omp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

hero_dma_job_t
hero_memcpy_host2dev_async(DEVICE_VOID_PTR dst, const HOST_VOID_PTR src,
                           uint32_t size)
{
  memcpy((HOST_VOID_PTR)dst, src, size);
  return 0;
}

hero_dma_job_t
hero_memcpy_dev2host_async(HOST_VOID_PTR dst, const DEVICE_VOID_PTR src,
                           uint32_t size)
{
  memcpy(dst, (HOST_VOID_PTR)src, size);
  return 0;
}

void
hero_memcpy_host2dev(DEVICE_VOID_PTR dst, const HOST_VOID_PTR src,
                     uint32_t size)
{
  memcpy((HOST_VOID_PTR)dst, src, size);
}

void
hero_memcpy_dev2host(HOST_VOID_PTR dst, const DEVICE_VOID_PTR src,
                     uint32_t size)
{
  memcpy(dst, (HOST_VOID_PTR)src, size);
}

void
hero_dma_wait(hero_dma_job_t id)
{
  return;
}

DEVICE_PTR
hero_l1malloc(int32_t size)
{
  printf("Trying to allocate L1 memory from host, which is not defined\n");
  return (DEVICE_PTR) NULL;
}

DEVICE_PTR
hero_l2malloc(int32_t size)
{
  printf("Trying to allocate L2 memory from host, which is not defined\n");
  return (DEVICE_PTR) NULL;
}

HOST_VOID_PTR
hero_l3malloc(int32_t size)
{
  // The concept of L3 exposed to the HERO end-user is just L3 = DRAM, and as
  // such this function is just a wrapper for malloc. This is different from
  // the understandig of L3 in libpulp, where it refers to unpaged buffer
  // memory for copy-on-offload data mappings. We don't expose this to the
  // end-user, as for BIGPULP_MEMCPY the offloading runtime takes care of the
  // buffer allocation, and for BIGPULP_SVM any address in DRAM can be
  // resolved.
  return malloc(size);
}

void
hero_l1free(DEVICE_PTR a)
{
  printf("Trying to free L1 memory from host, which is not defined\n");
  return;
}

void
hero_l2free(DEVICE_PTR a)
{
  printf("Trying to free L2 memory from host, which is not defined\n");
  return;
}

void
hero_l3free(HOST_VOID_PTR a)
{
  free(a);
}

int32_t
hero_rt_core_id(void)
{
  return omp_get_thread_num();
}

// FIXME implement clock counters for host
int32_t
hero_get_clk_counter(void) {
  return 0;
}

#define __hero_atomic_define(op, type) \
  type hero_atomic_ ## op(DEVICE_PTR_CONST ptr, const type val) \
  { \
    assert(0 && "Atomics are not supported on the Host"); \
    return val; \
  }

__hero_atomic_define(swap, int32_t)
__hero_atomic_define(add,  int32_t)
__hero_atomic_define(and,  int32_t)
__hero_atomic_define(or,   int32_t)
__hero_atomic_define(xor,  int32_t)
__hero_atomic_define(max,  int32_t)
__hero_atomic_define(maxu, uint32_t)
__hero_atomic_define(min,  int32_t)
__hero_atomic_define(minu, uint32_t)
