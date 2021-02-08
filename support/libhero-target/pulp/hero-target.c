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

#include <assert.h>
#include <stdbool.h>
#include <hero-target.h>
#include <pulp.h>
#include <bench/bench.h>
#include <rt/rt_alloc.h>
#include <archi-host/pgtable_hwdef.h>
#include <vmm/vmm.h>

#define L3_MEM_BASE_ADDR 0x80000000
#define PULP_DMA_MAX_XFER_SIZE_B 32768
#define PULP_DMA_MAX_XFERS 16
#define PULP_DMA_MASK_DATA_TYPE uint16_t // Holds bitmask for PULP_DMA_MAX_XFERS
#define PULP_DMA_MUTEX_BACKOFF_CYCLES 60
#define HERO_DMA_JOB_POOL_SIZE 8

#define DEBUG(...) //printf(__VA_ARGS__)

// Lock for entering critical sections in the DMA functions.
__attribute__((__aligned__(4))) volatile int32_t __hero_dma_lock = 0x0;

// A zero-initialized array of DMA jobs that keeps track of asynchronous state.
struct hero_dma_job __HERO_DMA_JOB_POOL[HERO_DMA_JOB_POOL_SIZE] HERO_L1_BSS;

// How many counters we have allocated to ANY job. This should only be updated
// while holding the lock.
PULP_DMA_MASK_DATA_TYPE __hero_dma_status = 0x0;

// The number of DMA counters/transfers that are currently in use. Should match
// the number of high bits in __hero_dma_status. This should only be updated
// while holding the lock.
uint32_t __hero_dma_num_inflight = 0;

// For debug purposes: Print the current state of a DMA job.
void
__hero_dma_job_print(const struct hero_dma_job * const job)
{
  DEBUG("Job 0x%x: ", (uint32_t) job);
  DEBUG("  Loc = 0x%x", job->loc);
  DEBUG("  Ext = 0x%lx", (uint32_t)job->ext);
  DEBUG("  Len = %6d", job->len);
  DEBUG("  E2L = %d", job->ext2loc);
  DEBUG("  Msk = 0x%4x", job->counter_mask);
  DEBUG("  Act = %d\n", job->active);
}

// Aquire the DMA lock.
void
__hero_dma_take_lock()
{
  // Spin for lock
  while (hero_atomic_or((void *)&__hero_dma_lock, 0x1) != 0x0) {
    for (int i = 0; i < PULP_DMA_MUTEX_BACKOFF_CYCLES; i++) {
      asm volatile("nop;": : :"memory");
    }
  }
  return;
}

// Release the DMA lock.
void __hero_dma_give_lock() {
  hero_atomic_swap((void *)&__hero_dma_lock, 0x0);
}

// Initialize the first free DMA job from the pool.
struct hero_dma_job *
__hero_dma_job_ctor(CONST_DEVICE_PTR_CONST loc, CONST_HOST_PTR_CONST ext,
                    const uint32_t len, const bool ext2loc)
{
  __hero_dma_take_lock();
  for (int i = 0; i < HERO_DMA_JOB_POOL_SIZE; i++) {
    struct hero_dma_job *job = &__HERO_DMA_JOB_POOL[i];
    if (job->active == false) {
      job->active = true;
      job->loc = (uint32_t)loc;
      job->ext = (uint64_t)ext;
      job->len = len;
      job->ext2loc = ext2loc;
      job->counter_mask = 0U;

      DEBUG("[%d] Allocated ", hero_get_clk_counter());
      __hero_dma_job_print(job);

      __hero_dma_give_lock();
      return job;
    }
  }
  printf("ERROR: No free DMA transfer jobs to start!\n");
  exit(-1);
}

// Release the DMA job and return it to the pool for re-selection.
void
__hero_dma_job_dtor(struct hero_dma_job * const job)
{
  DEBUG("[%d] Freeing ", hero_get_clk_counter());
  __hero_dma_job_print(job);
  job->active = false;
}

// Get a DMA counter, and update the global counter mask and inflight counter.
// Must be called while holding lock.
int32_t
__hero_dma_global_get_next_counter()
{
  if (__hero_dma_num_inflight < PULP_DMA_MAX_XFERS) {
    DEBUG("Getting DMA counter\n");
    uint32_t counter = plp_dma_counter_alloc();
    DEBUG("Got DMA counter %d\n", counter);
    if (__hero_dma_status & (1 << counter)) {
      // If another job was using this counter, make sure to unset it there, so
      // that they do not "double-free" it.
      for (int i = 0; i < HERO_DMA_JOB_POOL_SIZE; i++) {
        if (__HERO_DMA_JOB_POOL[i].active == true) {
          struct hero_dma_job *job = &__HERO_DMA_JOB_POOL[i];
          if (job->counter_mask & (1 << counter)) {
            job->counter_mask &= ~(1 << counter);
          }
        }
      }
    } else {
      // If this counter is not reclaimed from another job, then we have one
      // more in-flight counter, and need to update the global mask.
      __hero_dma_num_inflight++;
      __hero_dma_status |= (1 << counter);
    }
    return counter;
  }
  // If we reached end, there was no counter. Return error.
  return -1;
}

// Free a counter from a) the global mask, b) the in-flight counter, and c) the
// PULP runtime. This function should only be called while holding the lock.
void
__hero_dma_global_release_counter(const uint32_t id)
{
  if (__hero_dma_status & (1 << id)) {
    __hero_dma_status &= ~(1 << id);
    __hero_dma_num_inflight--;
    plp_dma_counter_free(id);
  }
}

// Set the mask of a job to include a counter. This function should only be
// called while holding the lock.
void
__hero_dma_job_set_counter(struct hero_dma_job * const job,
                           const uint32_t counter)
{
  job->counter_mask |= (1 << counter);
}

// Clear the bit in the mask of a job from this counter. This function should
// only be called while holding the lock.
void
__hero_dma_job_unset_counter(struct hero_dma_job * const job,
                             const uint32_t counter)
{
  job->counter_mask &= ~(1 << counter);
}

// Add a counter to the mask of the job. Return true if this succeeded, in which
// case the job may enqueue one more DMA burst. Return false if it did not
// succeed, at which point the DMA job is not allowed to enqueue another DMA
// burst. Must be called while holding lock.
bool
__hero_dma_job_get_counter(struct hero_dma_job * const job)
{
  bool success = false;
  int32_t counter = __hero_dma_global_get_next_counter();
  if (counter >= 0) {
    // There are free counters, take one, add it to our mask, and set successful
    // state.
    DEBUG("DMA Job 0x%x: Reserved counter %d, now %d active.\n",
           (uint32_t) job, counter, __hero_dma_num_inflight);
    __hero_dma_job_set_counter(job, counter);
    success = true;
  } else {
    DEBUG("Didn't get a counter. There are %d active.\n",
          __hero_dma_num_inflight);
  }
  return success;
}

// This is the core of the asynchronous DMA. It takes the given job and enqueues
// as many DMA bursts as it can (up to the given length). The only limit is the
// number of DMA counters that it can claim. Once as many bursts as possible or
// needed are enqueued, this function returns. Any remaining bursts that require
// enqueuing are deferred to the DMA wait function. The reasoning behind this is
// that we want as much as possible to be done asynchronously, and thus return
// as early as possible from this function.
bool
__hero_dma_job_worker(struct hero_dma_job * const job)
{

  // As long as there is more data to transfer, and we still manage to add
  // another counter to our job, enqueue another transfer.
  __hero_dma_take_lock();
  while (job->len > 0 && __hero_dma_job_get_counter(job)) {

    // get XFER length
    uint32_t len_tmp = job->len;
    if (job->len > PULP_DMA_MAX_XFER_SIZE_B) {
      len_tmp = PULP_DMA_MAX_XFER_SIZE_B;
    }

    DEBUG("DMA Job 0x%x: Burst: loc: 0x%x ext: 0x%lx, ", (uint32_t) job,
           job->loc, job->ext);
    DEBUG("ext2loc: %d, len: %d\n", job->ext2loc, job->len);
    uint32_t dma_cmd = plp_dma_getCmd(job->ext2loc, len_tmp, PLP_DMA_1D,
                             PLP_DMA_TRIG_EVT, PLP_DMA_NO_TRIG_IRQ,
                             PLP_DMA_PRIV);
    __asm__ __volatile__ ("" : : : "memory");
    // FIXME: DMA commands currently only work with 32-bit addresses. When this
    //        is fixed, we should remove the cast.
    plp_dma_cmd_push(dma_cmd, (uint32_t) job->loc, (uint32_t) job->ext);
    DEBUG("  Finished issuing job\n");

    job->len -= len_tmp;
    job->loc += len_tmp;
    job->ext += len_tmp;

  }
  __hero_dma_give_lock();

  // Return true if there is still data to transfer.
  return (job->len > 0);
}

// This function waits for all outstanding counters to finish their bursts,
// after which they are freed in the global mask, the mask of the job, and in
// the PULP runtime.
void
__hero_dma_job_wait(struct hero_dma_job * const job)
{
  for (int i = 0; i < PULP_DMA_MAX_XFERS; i++) {
    if (job->counter_mask & (1 << i)) {
      DEBUG("Waiting for job %d\n", i);
      while(DMA_READ(PLP_DMA_STATUS_OFFSET) & (1 << i)) {
        eu_evt_maskWaitAndClr(1<<ARCHI_CL_EVT_DMA0);
      }
      DEBUG("DMA Job 0x%x: Releasing counter %d...\n", (uint32_t) job, i);
      __hero_dma_take_lock();
      // Double check with lock, so that noone has taken our counter in the
      // meantime -- we only want to release it if we still own it.
      if (job->counter_mask & (1 << i)) {
        __hero_dma_job_unset_counter(job, i);
        __hero_dma_global_release_counter(i);
      }
      __hero_dma_give_lock();
    }
  }
}

// This function goes through all active jobs and clears out the claim to
// counters whose bursts have already finished. This allows them to be reused by
// other jobs, to avoid deadlocks in case of DMA wait functions being called in
// another order than the transfers were enqueued.
void
__hero_dma_clear_finished_counters()
{
  __hero_dma_take_lock();
  for (int i = 0; i < HERO_DMA_JOB_POOL_SIZE; i++) {
    if (__HERO_DMA_JOB_POOL[i].active == true) {
      struct hero_dma_job *job = &__HERO_DMA_JOB_POOL[i];
      DEBUG("Clearing completed transfers for: ");
      __hero_dma_job_print(job);
      for (int i = 0; i < PULP_DMA_MAX_XFERS; i++) {
        // Walk through mask, check if counter has finished, and then clear it.
        if (job->counter_mask & (1 << i)) {
          DEBUG("DMA Job 0x%x: Checking completion of burst %d...\n",
                 (uint32_t) job, i);
          if ((DMA_READ(PLP_DMA_STATUS_OFFSET) & (1 << i)) == 0) {
            DEBUG("DMA Job 0x%x: Releasing counter %d...\n", (uint32_t) job, i);
            __hero_dma_job_unset_counter(job, i);
            __hero_dma_global_release_counter(i);
          } else {
            eu_evt_maskWaitAndClr(1<<ARCHI_CL_EVT_DMA0);
          }
        }
      }
    }
  }
  __hero_dma_give_lock();
}

// Sets up a DMA job with the given parameters, enqueues as many bursts as
// possible, and returns. Any bursts that remain are deferred to the DMA wait
// function.
struct hero_dma_job *
__hero_dma_memcpy_async(DEVICE_VOID_PTR loc, HOST_VOID_PTR ext,
                        const uint32_t len, const bool ext2loc)
{

  // TODO When DMA can handle wide jobs, remove this warning.
  if ((uint64_t)ext > UINT32_MAX) {
    printf("DMA cannot handle addresses this wide!\n");
  }

  // Create the new job.
  struct hero_dma_job *dma_job = __hero_dma_job_ctor(loc, ext, len, ext2loc);

  // Try to free up some no longer used counters, so that we can enqueue as many
  // bursts as possible.
  __hero_dma_clear_finished_counters();

  // Run as much of the job as possible
  __hero_dma_job_worker(dma_job);

  // Return the job to caller
  return dma_job;
}

void
hero_dma_wait(struct hero_dma_job *job)
{

  // Return early if nothing to do.
  if (!job->active) {
    return;
  }

  // First wait for all transfers we have already started.
  __hero_dma_job_wait(job);

  // If we still have bursts left to issue, issue as many as we can, wait for
  // them to complete, and then repeat until all data has been transfered.
  // Also clear up finished bursts from other jobs to free up more counters for
  // us.
  DEBUG("Job 0x%x: Issuing straggler jobs", (uint32_t) job);
  DEBUG("  In-flight: %d, Mask = 0x%x\n", __hero_dma_num_inflight,
        __hero_dma_status);
  while (__hero_dma_job_worker(job)) {
    __hero_dma_job_wait(job);
    __hero_dma_clear_finished_counters();
  }
  DEBUG("Job 0x%x: All straggler jobs issued\n", (uint32_t) job);

  // Once we have finished issuing commands, ensure that the last bursts
  // complete before returning to the program.
  __hero_dma_job_wait(job);

  // Free the job
  __hero_dma_job_dtor(job);

  return;
}

hero_dma_job_t
hero_memcpy_host2dev_async(DEVICE_VOID_PTR dst, const HOST_VOID_PTR src,
                           uint32_t len)
{
  DEBUG("hero_memcpy_host2dev_async(0x%x, 0x%x, 0x%x)\n", dst, src, len);
  return __hero_dma_memcpy_async(dst, (HOST_VOID_PTR) src, len, 1);
}

hero_dma_job_t
hero_memcpy_dev2host_async(HOST_VOID_PTR dst, const DEVICE_VOID_PTR src,
                           uint32_t len)
{
  DEBUG("hero_memcpy_dev2host_async(0x%x, 0x%x, 0x%x)\n", dst, src, len);
  return __hero_dma_memcpy_async((DEVICE_VOID_PTR) src, dst, len, 0);
}

void
hero_memcpy_host2dev(DEVICE_VOID_PTR dst, const HOST_VOID_PTR src,
                     uint32_t size)
{
  DEBUG("hero_memcpy_host2dev(0x%x, 0x%x, 0x%x)\n", dst, src, size);
  hero_dma_wait(hero_memcpy_host2dev_async(dst, src, size));
}

void
hero_memcpy_dev2host(HOST_VOID_PTR dst, const DEVICE_VOID_PTR src,
                     uint32_t size)
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
  return (HOST_VOID_PTR)0;
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

int32_t
hero_get_clk_counter(void)
{
  return get_time();
}

void __compiler_barrier(void) {
  asm volatile("" : : : "memory");
}

typedef struct {
  uint32_t pcer, pcer_pre_init;
  uint8_t pcmr_pre_init;
} hero_perf_t;

HERO_L1_BSS hero_perf_t* hero_perf[8]; // one pointer for each core in the cluster

int hero_perf_init(void) {
  // Abort early if already initialized.
  if (hero_perf[hero_rt_core_id()] != NULL) return -HERO_EALREADY;

  // Allocate memory for tracking state of performance counters.
  hero_perf[hero_rt_core_id()] = hero_l1malloc(sizeof(hero_perf_t));
  if (hero_perf[hero_rt_core_id()] == NULL) return -HERO_ENOMEM;

  // Disable all performance counters individually.
  hero_perf[hero_rt_core_id()]->pcer = 0;
  asm volatile("csrrw %0, 0x7E0, %1"
      : "=r"(hero_perf[hero_rt_core_id()]->pcer_pre_init)
      : "r"(hero_perf[hero_rt_core_id()]->pcer)
      : "memory");

  // Globally enable performance counters and enable saturation.
  asm volatile("csrrwi %0, 0x7E1, 3"
      : "=r"(hero_perf[hero_rt_core_id()]->pcmr_pre_init)
      :
      : "memory");

  return 0;
}

void hero_perf_term(void) {
  // Abort early if not allocated.
  if (hero_perf[hero_rt_core_id()] == NULL) return;

  // Restore PCER and PCMR to pre-init state.
  asm volatile("csrw 0x7E0, %0"
      :
      : "r"(hero_perf[hero_rt_core_id()]->pcer_pre_init)
      : "memory");
  asm volatile("csrw 0x7E1, %0"
      :
      : "r"(hero_perf[hero_rt_core_id()]->pcmr_pre_init)
      : "memory");

  // Free allocated memory and reset pointer.
  hero_l1free(hero_perf[hero_rt_core_id()]);
  hero_perf[hero_rt_core_id()] = 0;
};

static inline uint32_t pcer_mask(const hero_perf_event_t event) {
  uint8_t shift_amount;
  switch (event) {
    case hero_perf_event_load:            shift_amount = 5; break;
    case hero_perf_event_store:           shift_amount = 6; break;
    case hero_perf_event_load_external:   shift_amount = 12; break;
    case hero_perf_event_store_external:  shift_amount = 13; break;
    default:
      return 0;
  }
  return 1 << shift_amount;
}

int hero_perf_alloc(const hero_perf_event_t event) {
  // Obtain PCER mask for event.
  const uint32_t mask = pcer_mask(event);
  if (mask == 0) return -HERO_ENODEV;
  hero_perf[hero_rt_core_id()]->pcer |= mask;

  int ret = hero_perf_pause(event);
  assert(ret >= 0);
  ret = hero_perf_reset(event);
  assert(ret >= 0);

  return 0;
}

int hero_perf_dealloc(const hero_perf_event_t event) {
  // Obtain PCER mask for event.
  const uint32_t mask = pcer_mask(event);
  if (mask == 0) return -HERO_ENODEV;
  hero_perf[hero_rt_core_id()]->pcer &= ~mask;

  return 0;
}

int hero_perf_reset(const hero_perf_event_t event) {
  __compiler_barrier();
  int retval = 0;
  switch (event) {
    case hero_perf_event_load:            asm volatile("csrw 0x785, x0"); break;
    case hero_perf_event_store:           asm volatile("csrw 0x786, x0"); break;
    case hero_perf_event_load_external:   asm volatile("csrw 0x78C, x0"); break;
    case hero_perf_event_store_external:  asm volatile("csrw 0x78D, x0"); break;
    default:
      retval = -HERO_EINVAL;
  }
  __compiler_barrier();
  return retval;
}

void hero_perf_reset_all(void) {
  __compiler_barrier();
  asm volatile("csrw 0x79F, x0");
  __compiler_barrier();
}

int hero_perf_pause(const hero_perf_event_t event) {
  __compiler_barrier();
  int ret = 0;
  const uint32_t mask = pcer_mask(event);
  if (mask == 0) {
    ret = -HERO_ENODEV;
    goto __pause_end;
  }
  asm volatile("csrc 0x7E0, %0" : : "r"(mask));

__pause_end:
  __compiler_barrier();
  return ret;
}

void hero_perf_pause_all(void) {
  __compiler_barrier();
  asm volatile("csrw 0x7E0, x0");
  __compiler_barrier();
}

int hero_perf_continue(hero_perf_event_t event) {
  __compiler_barrier();
  int ret = 0;
  const uint32_t mask = pcer_mask(event);
  if (mask == 0) {
    ret = -HERO_ENODEV;
    goto __continue_end;
  }
  asm volatile("csrs 0x7E0, %0" : : "r"(mask));

__continue_end:
  __compiler_barrier();
  return ret;
}

void hero_perf_continue_all(void) {
  __compiler_barrier();
  asm volatile("csrs 0x7E0, %0" : : "r"(hero_perf[hero_rt_core_id()]->pcer));
  __compiler_barrier();
}

int hero_perf_read(const hero_perf_event_t event) {
  __compiler_barrier();

  int retval = 0;
  uint32_t val;
  switch (event) {
    case hero_perf_event_load:            asm volatile("csrr %0, 0x785" : "=r" (val)); break;
    case hero_perf_event_store:           asm volatile("csrr %0, 0x786" : "=r" (val)); break;
    case hero_perf_event_load_external:   asm volatile("csrr %0, 0x78C" : "=r" (val)); break;
    case hero_perf_event_store_external:  asm volatile("csrr %0, 0x78D" : "=r" (val)); break;
    default:
      retval = -HERO_EINVAL;
  }
  if (retval < 0) goto __read_end;
  if (val > INT32_MAX)
    retval = -HERO_EOVERFLOW;
  else
    retval = (int)val;

__read_end:
  __compiler_barrier();
  return retval;
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
