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

unsigned int
hero_tryread(const unsigned int* const addr)
{
  return pulp_tryread(addr);
}

int
hero_tryread_prefetch(const unsigned int* const addr)
{
  return pulp_tryread_prefetch(addr);
}

void
hero_trywrite(unsigned int* const addr, const unsigned int val)
{
  return pulp_trywrite(addr, val);
}

int
hero_trywrite_prefetch(unsigned int* const addr)
{
  return pulp_trywrite_prefetch(addr);
}

int
hero_handle_rab_misses(void)
{
  return handle_rab_misses();
}

hero_dma_job_t
hero_dma_memcpy_async(void *dst, void *src, int size)
{
  int ext2loc;
  unsigned int ext_addr_tmp, ext_addr, loc_addr;
  int size_tmp = size;
  hero_dma_job_t dma = 0;

  // get direction
  if ((unsigned int) dst < ARCHI_CLUSTER_GLOBAL_ADDR(0) ||
      (unsigned int) dst >= (ARCHI_CLUSTER_GLOBAL_ADDR(0) + ARCHI_CLUSTER_SIZE))
  {
    ext2loc = 0;
    ext_addr = (unsigned int) dst;
    loc_addr = (unsigned int) src;
  }
  else
  {
    ext2loc = 1;
    ext_addr = (unsigned int) src;
    loc_addr = (unsigned int) dst;
  }

  // we might need to split the transfer into chunks of PULP_DMA_MAX_XFER_SIZE_B
  while (size > 0) {

    // get XFER size
    if (size > PULP_DMA_MAX_XFER_SIZE_B)
      size_tmp = PULP_DMA_MAX_XFER_SIZE_B;
    else
      size_tmp = size;

    // TLB prefetch
    pulp_tryread_prefetch((unsigned *)ext_addr);
    for (ext_addr_tmp = ( ext_addr & PAGE_MASK) + PAGE_SIZE;
         ext_addr_tmp < ((ext_addr + size_tmp - 1) & PAGE_MASK);
         ext_addr_tmp += PAGE_SIZE)
      pulp_tryread_prefetch((unsigned *)ext_addr_tmp);
    pulp_tryread_prefetch((unsigned *)((ext_addr + size_tmp - 1) & 0xFFFFFFFC));

    // TLB tryread
    pulp_tryread((unsigned *)ext_addr);
    for (ext_addr_tmp = ( ext_addr & PAGE_MASK) + PAGE_SIZE;
         ext_addr_tmp < ((ext_addr + size_tmp - 1) & PAGE_MASK);
         ext_addr_tmp += PAGE_SIZE)
      pulp_tryread((unsigned *)ext_addr_tmp);
    pulp_tryread((unsigned *)((ext_addr + size_tmp - 1) & 0xFFFFFFFC));

    // just wait for the last one...
    dma = (hero_dma_job_t)plp_dma_memcpy(ext_addr,loc_addr,size_tmp,ext2loc);

    size     -= size_tmp;
    ext_addr += size_tmp;
    loc_addr += size_tmp;
  }

  return dma;
}

void
hero_dma_memcpy(void *dst, void *src, int size)
{
  plp_dma_wait(hero_dma_memcpy_async(dst, src, size));
}

void
hero_dma_wait(hero_dma_job_t id)
{
  plp_dma_wait(id);
}

void *
hero_l1malloc(int size)
{
  return l1malloc(size);
}

void *
hero_l2malloc(int size)
{
  return l2malloc(size);
}
static void *l3_ptr = (void*)L3_MEM_BASE_ADDR;
void *
hero_l3malloc(int size)
{
  void *ptr = l3_ptr;
  l3_ptr += size;
  return ptr;
}

void
hero_l1free(void * a)
{
  l1free(a);
}

void
hero_l2free(void * a)
{
  l2free(a);
}
void
hero_l3free(void *a)
{
  //FIXME: implement
  return;
}

int
hero_rt_core_id(void)
{
  return rt_core_id();
}

void
hero_reset_clk_counter(void) {
    reset_timer();
    start_timer();
}

int
hero_get_clk_counter(void) {
    return get_time();
}
