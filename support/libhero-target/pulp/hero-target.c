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

#include <stdbool.h>
#include <hero-target.h>
#include <pulp.h>
#include <bench/bench.h>
#include <libgomp/pulp/memutils.h>
#include <archi-host/pgtable_hwdef.h>
#include <vmm/vmm.h>

#define L3_MEM_BASE_ADDR 0x80000000
#define PULP_DMA_MAX_XFER_SIZE_B 512 // Larger causes RAB problems
#define PULP_DMA_MAX_XFERS 16
#define PULP_DMA_MASK_DATA_TYPE uint16_t // Holds bitmask for PULP_DMA_MAX_XFERS
#define PULP_DMA_MUTEX_BACKOFF_CYCLES 60

#define DEBUG(...) //printf(__VA_ARGS__)

__attribute__((__aligned__(4))) volatile int32_t __hero_dma_lock = 0x0;
void __hero_dma_take_lock() {
  // Spin for lock
  while (hero_atomic_xor(&__hero_dma_lock, 0x1) != 0x0) {
    for (int i = 0; i < PULP_DMA_MUTEX_BACKOFF_CYCLES; i++) {
      asm volatile("nop;": : :"memory");
    }
  }
  return;
}

void __hero_dma_give_lock() {
  hero_atomic_swap(&__hero_dma_lock, 0x0);
}

struct hero_dma_job *__hero_dma_job_ctor(DEVICE_VOID_PTR loc, HOST_VOID_PTR ext,
                                   int32_t len, int32_t ext2loc) {
  struct hero_dma_job *job =
      (struct hero_dma_job *) l1malloc(sizeof(struct hero_dma_job));
  job->loc = (uint32_t)loc;
  job->ext = (uint64_t)ext;
  job->len = len;
  job->ext2loc = ext2loc;
  job->counter_mask = 0U;

  printf("Allocated job 0x%x: loc = 0x%x, ext = 0x%lx",
         (uint32_t) job, job->loc, job->ext);
  printf(", len = %d, ext2loc = %d, mask = 0x%x\n",
         job->len, job->ext2loc, job->counter_mask);

  return job;
}

void __hero_dma_job_print(struct hero_dma_job *job) {
  printf("Job 0x%x: ", (uint32_t) job);
  printf("  Loc = 0x%x", job->loc);
  printf("  Ext = 0x%lx", job->ext);
  printf("  Len = %d", job->len);
  printf("  E2L = %d", job->ext2loc);
  printf("  Msk = 0x%x\n", job->counter_mask);
}

// This keeps track of how many counters we have allocated. It does not
// necessarily match the DMA counter that is returned from the hardware.
PULP_DMA_MASK_DATA_TYPE __hero_dma_status = 0x0;
uint32_t __hero_dma_num_inflight = 0;

int16_t __hero_dma_global_get_next_counter() {
  __hero_dma_take_lock();
  if (__hero_dma_num_inflight < PULP_DMA_MAX_XFERS) {
    __hero_dma_num_inflight++;
    uint32_t counter = plp_dma_counter_alloc();
    __hero_dma_status |= (1 << counter);
    __hero_dma_give_lock();
    return counter;
  }
  // If we reached end, there was no counter. Return error.
  __hero_dma_give_lock();
  return -1;
}

void __hero_dma_global_release_counter(uint32_t id) {
  __hero_dma_take_lock();
  __hero_dma_status &= ~(1 << id);
  __hero_dma_num_inflight--;
  plp_dma_counter_free(id);
  __hero_dma_give_lock();
}

bool __hero_dma_job_get_counter(struct hero_dma_job *job) {
  bool success = false;
  int8_t counter = __hero_dma_global_get_next_counter();
  if (counter >= 0) {
    // There are free counters, take one, add it to our mask, and set successful
    // state.
    printf("DMA Job 0x%x: Reserved counter %d\n", (uint32_t) job, counter);
    job->counter_mask |= (1 << counter);
    success = true;
  }
  return success;
}

bool __hero_dma_job_worker(struct hero_dma_job *job) {

  // As long as there is more data to transfer, and we still manage to add
  // another counter to our job, enqueue another transfer.
  while (job->len > 0 && __hero_dma_job_get_counter(job)) {

    // get XFER length
    int32_t len_tmp = job->len;
    if (job->len > PULP_DMA_MAX_XFER_SIZE_B) {
      len_tmp = PULP_DMA_MAX_XFER_SIZE_B;
    }

    printf("DMA Job 0x%x: Burst: loc: 0x%x ext: 0x%lx, ", (uint32_t) job,
           job->loc, job->ext);
    printf("ext2loc: %d, len: %d\n", job->ext2loc, job->len);
    uint32_t dma_cmd = plp_dma_getCmd(job->ext2loc, len_tmp, PLP_DMA_1D,
                             PLP_DMA_TRIG_EVT, PLP_DMA_NO_TRIG_IRQ,
                             PLP_DMA_PRIV);
    __asm__ __volatile__ ("" : : : "memory");
    // FIXME: DMA commands currently only work with 32-bit addresses. When this
    //        is fixed, we should remove the cast.
    plp_dma_cmd_push(dma_cmd, (uint32_t) job->loc, (uint32_t) job->ext);

    job->len -= len_tmp;
    job->loc += len_tmp;
    job->ext += len_tmp;

  }

  // Return true if there is still data to transfer.
  return (job->len > 0);
}

void __hero_dma_job_wait(struct hero_dma_job *job) {
  for (int i = 0; i < PULP_DMA_MAX_XFERS; i++) {
    // Walk through mask, wait for every counter we have allocated, and then
    // clear mask.
    if (job->counter_mask & (1 << i)) {
      printf("DMA Job 0x%x: Waiting for burst %d...\n", (uint32_t) job, i);
      while(DMA_READ(PLP_DMA_STATUS_OFFSET) & (1 << i)) {
        eu_evt_maskWaitAndClr(1<<ARCHI_CL_EVT_DMA0);
      }
      printf("DMA Job 0x%x: Releasing counter %d...\n", (uint32_t) job, i);
      job->counter_mask &= ~(1 << i);
      __hero_dma_global_release_counter(i);
    }
  }
}

// Internal function
struct hero_dma_job *
__hero_dma_memcpy_async(DEVICE_VOID_PTR loc, HOST_VOID_PTR ext, int32_t len,
                        int32_t ext2loc)
{

  // TODO When DMA can handle wide jobs, remove this warning.
  if ((uint64_t)ext > UINT32_MAX) {
    printf("DMA cannot handle addresses this wide!\n");
  }

  // Create the new job.
  struct hero_dma_job *dma_job = __hero_dma_job_ctor(loc, ext, len, ext2loc);

  // Run as much of the job as possible
  __hero_dma_job_worker(dma_job);

  // Return the job to caller
  return dma_job;
}

void
hero_dma_wait(struct hero_dma_job *job)
{

  __hero_dma_job_print(job);

  // First wait for all transfers we have already started.
  __hero_dma_job_wait(job);

  // If we still have bursts left to issue, issue as many as we can, wait for
  // them to complete, and then repeat until all data has been transfered.
  while (__hero_dma_job_worker(job)) {
    printf("Job 0x%x: Issuing straggler jobs\n", (uint32_t) job);
    __hero_dma_job_wait(job);
  }

  // Once we have finished issuing commands, ensure that the last bursts
  // complete before returning to the program.
  __hero_dma_job_wait(job);

  // Free the job
  l1free(job);

}

hero_dma_job_t
hero_memcpy_host2dev_async(DEVICE_VOID_PTR dst, HOST_VOID_PTR src, uint32_t len)
{
  DEBUG("hero_memcpy_host2dev_async(0x%x, 0x%x, 0x%x)\n", dst, src, len);
  return __hero_dma_memcpy_async(dst, src, len, 1);
}

hero_dma_job_t
hero_memcpy_dev2host_async(HOST_VOID_PTR dst, DEVICE_VOID_PTR src, uint32_t len)
{
  DEBUG("hero_memcpy_dev2host_async(0x%x, 0x%x, 0x%x)\n", dst, src, len);
  return __hero_dma_memcpy_async(src, dst, len, 0);
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

// -------------------------------------------------------------------------- //

#define __hero_atomic_define(op, type) \
  type hero_atomic_ ## op(DEVICE_PTR_CONST ptr, const type val) \
  { \
    /*assert(((uint32_t)ptr & 0x3) == 0);*/ /* only four-byte aligned addresses are supported */ \
    type orig; \
    __asm__ volatile("amo" #op ".w %[orig], %[val], (%[ptr])" \
        : [orig] "=r" (orig), "+m" (*ptr) \
        : [val] "r" (val), [ptr] "r" (ptr) \
        : "memory" \
    ); \
    return orig; \
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
