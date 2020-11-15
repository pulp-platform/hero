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
#include <pulp.h>
#include <bench/bench.h>
#include <libgomp/pulp/memutils.h>
#include <archi-host/pgtable_hwdef.h>
#include <vmm/vmm.h>

#define L3_MEM_BASE_ADDR 0x80000000
#define PULP_DMA_MAX_XFER_SIZE_B 32768

#define DEBUG(...) //printf(__VA_ARGS__)

uint64_t
hero_tryread(CONST_HOST_PTR_CONST addr)
{
  // FIXME: Try* commands currently only work with 32-bit addresses. When this
  //        is fixed, we should remove the cast.
  return pulp_tryread((CONST_DEVICE_PTR_CONST) addr);
}

int32_t
hero_tryread_prefetch(CONST_HOST_PTR_CONST addr)
{
  // FIXME: Try* commands currently only work with 32-bit addresses. When this
  //        is fixed, we should remove the cast.
  return pulp_tryread_prefetch((DEVICE_PTR_CONST) addr);
}

void
hero_trywrite(HOST_PTR_CONST addr, const uint64_t val)
{
  // FIXME: Try* commands currently only work with 32-bit addresses. When this
  //        is fixed, we should remove the cast.
  return pulp_trywrite((DEVICE_PTR_CONST) addr, val);
}

int32_t
hero_trywrite_prefetch(HOST_PTR_CONST addr)
{
  // FIXME: Try* commands currently only work with 32-bit addresses. When this
  //        is fixed, we should remove the cast.
  return pulp_trywrite_prefetch((DEVICE_PTR_CONST) addr);
}

int32_t
hero_handle_rab_misses(void)
{
  return handle_rab_misses();
}

// -------------------------------------------------------------------------- //

// Internal function
hero_dma_job_t
__hero_dma_memcpy_async(HOST_VOID_PTR dst, HOST_VOID_PTR src, int32_t len,
                        int32_t ext2loc)
{

  hero_dma_job_t dma_job = plp_dma_counter_alloc();
  uint32_t dma_cmd;

  // we might need to split the transfer into chunks of PULP_DMA_MAX_XFER_SIZE_B
  while (len > 0) {

    // get XFER length
    int32_t len_tmp = len;
    if (len > PULP_DMA_MAX_XFER_SIZE_B) {
      len_tmp = PULP_DMA_MAX_XFER_SIZE_B;
    }

    DEBUG("copy cmd: loc: 0x%llx ext: 0x%llx ext2loc: %ld len: %ld\n", dst, src,
           ext2loc, len);
    dma_cmd = plp_dma_getCmd(ext2loc, len_tmp, PLP_DMA_1D, PLP_DMA_TRIG_EVT,
                             PLP_DMA_NO_TRIG_IRQ, PLP_DMA_PRIV);
    __asm__ __volatile__ ("" : : : "memory");
    // FIXME: DMA commands currently only work with 32-bit addresses. When this
    //        is fixed, we should remove the cast.
    plp_dma_cmd_push(dma_cmd, (uint32_t) dst, (uint32_t) src);

    len -= len_tmp;
    dst += len_tmp;
    src += len_tmp;
  }

  return dma_job;
}


hero_dma_job_t
hero_memcpy_host2dev_async(DEVICE_VOID_PTR spm, HOST_VOID_PTR ram, uint32_t len)
{
  DEBUG("hero_memcpy_host2dev_async(0x%x, 0x%x, 0x%x)\n", spm, ram, len);
  if (ram > UINT32_MAX) {
    printf("DMA cannot handle addresses this wide!\n");
  }
  return __hero_dma_memcpy_async(spm, ram, len, 1);
}

hero_dma_job_t
hero_memcpy_dev2host_async(HOST_VOID_PTR ram, DEVICE_VOID_PTR spm, uint32_t len)
{
  DEBUG("hero_memcpy_dev2host_async(0x%x, 0x%x, 0x%x)\n", ram, spm, len);
  if (ram > UINT32_MAX) {
    printf("DMA cannot handle addresses this wide!\n");
  }
  return __hero_dma_memcpy_async(spm, ram, len, 0);
}

void
hero_memcpy_host2dev(DEVICE_VOID_PTR dst, HOST_VOID_PTR src, uint32_t size)
{
  DEBUG("hero_memcpy_host2dev(0x%x, 0x%x, 0x%x)\n", dst, src, size);
  hero_dma_wait(hero_memcpy_host2dev_async(dst, src, size));
}

void
hero_memcpy_dev2host(HOST_VOID_PTR dst, DEVICE_VOID_PTR src, uint32_t size)
{
  DEBUG("hero_memcpy_dev2host(0x%x, 0x%x, 0x%x)\n", dst, src, size);
  hero_dma_wait(hero_memcpy_dev2host_async(dst, src, size));
}

void
hero_dma_wait(hero_dma_job_t id)
{
  plp_dma_wait(id);
}

// -------------------------------------------------------------------------- //

DEVICE_VOID_PTR
hero_l1malloc(int32_t size)
{
  return l1malloc(size);
}

DEVICE_VOID_PTR
hero_l2malloc(int32_t size)
{
  return l2malloc(size);
}

HOST_VOID_PTR
hero_l3malloc(int32_t size)
{
  printf("Trying to allocate L3 memory from PULP, which is not defined\n");
  return (HOST_VOID_PTR)NULL;
}

void
hero_l1free(DEVICE_VOID_PTR a)
{
  l1free(a);
}

void
hero_l2free(DEVICE_VOID_PTR a)
{
  l2free(a);
}

void
hero_l3free(HOST_VOID_PTR a)
{
  printf("Trying to free L3 memory from PULP, which is not defined\n");
  return;
}

int32_t
hero_rt_core_id(void)
{
  return rt_core_id();
}

void
hero_reset_clk_counter(void)
{
  reset_timer();
  start_timer();
}

int32_t
hero_get_clk_counter(void)
{
  return get_time();
}
