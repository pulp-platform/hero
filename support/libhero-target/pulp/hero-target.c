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

#define HPM_PROGRAMMABLE_COUNTERS 2
typedef struct {
  uint32_t mcountinhibit;
} hero_perf_t;

HERO_L1_BSS hero_perf_t* hero_perf[8]; // one pointer for each core in the cluster

static inline void set_mhpmevent(const uint8_t counter, const uint32_t event) {
  switch (counter) {
    case  3: asm volatile("csrw 0x323, %0" : : "r"(event)); break;
    case  4: asm volatile("csrw 0x324, %0" : : "r"(event)); break;
    case  5: asm volatile("csrw 0x325, %0" : : "r"(event)); break;
    case  6: asm volatile("csrw 0x326, %0" : : "r"(event)); break;
    case  7: asm volatile("csrw 0x327, %0" : : "r"(event)); break;
    case  8: asm volatile("csrw 0x328, %0" : : "r"(event)); break;
    case  9: asm volatile("csrw 0x329, %0" : : "r"(event)); break;
    case 10: asm volatile("csrw 0x32A, %0" : : "r"(event)); break;
    case 11: asm volatile("csrw 0x32B, %0" : : "r"(event)); break;
    case 12: asm volatile("csrw 0x32C, %0" : : "r"(event)); break;
    case 13: asm volatile("csrw 0x32D, %0" : : "r"(event)); break;
    case 14: asm volatile("csrw 0x32E, %0" : : "r"(event)); break;
    case 15: asm volatile("csrw 0x32F, %0" : : "r"(event)); break;
    case 16: asm volatile("csrw 0x330, %0" : : "r"(event)); break;
    case 17: asm volatile("csrw 0x331, %0" : : "r"(event)); break;
    case 18: asm volatile("csrw 0x332, %0" : : "r"(event)); break;
    case 19: asm volatile("csrw 0x333, %0" : : "r"(event)); break;
    case 20: asm volatile("csrw 0x334, %0" : : "r"(event)); break;
    case 21: asm volatile("csrw 0x335, %0" : : "r"(event)); break;
    case 22: asm volatile("csrw 0x336, %0" : : "r"(event)); break;
    case 23: asm volatile("csrw 0x337, %0" : : "r"(event)); break;
    case 24: asm volatile("csrw 0x338, %0" : : "r"(event)); break;
    case 25: asm volatile("csrw 0x339, %0" : : "r"(event)); break;
    case 26: asm volatile("csrw 0x33A, %0" : : "r"(event)); break;
    case 27: asm volatile("csrw 0x33B, %0" : : "r"(event)); break;
    case 28: asm volatile("csrw 0x33C, %0" : : "r"(event)); break;
    case 29: asm volatile("csrw 0x33D, %0" : : "r"(event)); break;
    case 30: asm volatile("csrw 0x33E, %0" : : "r"(event)); break;
    case 31: asm volatile("csrw 0x33F, %0" : : "r"(event)); break;
    default: /* do nothing */;
  }
}

static inline uint32_t get_mhpmevent(const uint8_t counter) {
  uint32_t event;
  switch (counter) {
    case  3: asm volatile("csrr %0, 0x323" : "=r"(event)); break;
    case  4: asm volatile("csrr %0, 0x324" : "=r"(event)); break;
    case  5: asm volatile("csrr %0, 0x325" : "=r"(event)); break;
    case  6: asm volatile("csrr %0, 0x326" : "=r"(event)); break;
    case  7: asm volatile("csrr %0, 0x327" : "=r"(event)); break;
    case  8: asm volatile("csrr %0, 0x328" : "=r"(event)); break;
    case  9: asm volatile("csrr %0, 0x329" : "=r"(event)); break;
    case 10: asm volatile("csrr %0, 0x32A" : "=r"(event)); break;
    case 11: asm volatile("csrr %0, 0x32B" : "=r"(event)); break;
    case 12: asm volatile("csrr %0, 0x32C" : "=r"(event)); break;
    case 13: asm volatile("csrr %0, 0x32D" : "=r"(event)); break;
    case 14: asm volatile("csrr %0, 0x32E" : "=r"(event)); break;
    case 15: asm volatile("csrr %0, 0x32F" : "=r"(event)); break;
    case 16: asm volatile("csrr %0, 0x330" : "=r"(event)); break;
    case 17: asm volatile("csrr %0, 0x331" : "=r"(event)); break;
    case 18: asm volatile("csrr %0, 0x332" : "=r"(event)); break;
    case 19: asm volatile("csrr %0, 0x333" : "=r"(event)); break;
    case 20: asm volatile("csrr %0, 0x334" : "=r"(event)); break;
    case 21: asm volatile("csrr %0, 0x335" : "=r"(event)); break;
    case 22: asm volatile("csrr %0, 0x336" : "=r"(event)); break;
    case 23: asm volatile("csrr %0, 0x337" : "=r"(event)); break;
    case 24: asm volatile("csrr %0, 0x338" : "=r"(event)); break;
    case 25: asm volatile("csrr %0, 0x339" : "=r"(event)); break;
    case 26: asm volatile("csrr %0, 0x33A" : "=r"(event)); break;
    case 27: asm volatile("csrr %0, 0x33B" : "=r"(event)); break;
    case 28: asm volatile("csrr %0, 0x33C" : "=r"(event)); break;
    case 29: asm volatile("csrr %0, 0x33D" : "=r"(event)); break;
    case 30: asm volatile("csrr %0, 0x33E" : "=r"(event)); break;
    case 31: asm volatile("csrr %0, 0x33F" : "=r"(event)); break;
    default: event = 0;
  }
  return event;
}

int hero_perf_init(void) {
  // Return if already initialized.
  if (hero_perf[hero_rt_core_id()] != NULL) return -HERO_EALREADY;

  // Allocate memory for tracking state of performance counters.
  hero_perf[hero_rt_core_id()] = hero_l1malloc(sizeof(hero_perf_t));
  if (hero_perf[hero_rt_core_id()] == NULL) return -HERO_ENOMEM;

  // Initialize state struct.
  *hero_perf[hero_rt_core_id()] = (hero_perf_t){
    .mcountinhibit = ~0 // mark all counters as deallocated
  };

  // Clear counter event assignments.
  for (unsigned i = 3; i < 3 + HPM_PROGRAMMABLE_COUNTERS; i++) set_mhpmevent(i, 0);

  // Pause all counters.
  hero_perf_pause_all();

  return 0;
}

void hero_perf_deinit(void) {
  // Return if not allocated.
  if (hero_perf[hero_rt_core_id()] == NULL) return;

  // Free allocated memory and reset pointer.
  hero_l1free(hero_perf[hero_rt_core_id()]);
  hero_perf[hero_rt_core_id()] = 0;
};

// Return the number of an event.  If the event is statically assigned to a counter, the returned
// event number equals the counter number.  If the event is dynamically assigned to a counter, the
// returned event number does not directly correspond to a counter and a return value of 0 means the
// event is not implemented.
static inline uint8_t event_num(const hero_perf_event_t event) {
  switch (event) {
    // statically assigned events
    case hero_perf_event_cycle:         return 0;
    case hero_perf_event_instr_retired: return 2;
    // dynamically assigned events
    case hero_perf_event_load:            return  4;
    case hero_perf_event_store:           return  5;
    case hero_perf_event_load_external:   return 15;
    case hero_perf_event_store_external:  return 16;
    default:                              return  0;
  }
}

// Return whether an event is statically assigned to a counter.
static inline bool event_static(const hero_perf_event_t event) {
  switch (event) {
    case hero_perf_event_cycle:
    case hero_perf_event_instr_retired:
      return true;
    default:
      return false;
  }
}

// Return whether the event is implemented.
static inline bool event_implemented(const hero_perf_event_t event) {
  if (event_static(event)) {
    // events with a statically assigned counter are implemented
    return true;
  } else {
    // some of the events with a dynamically assigned counter are implemented
    return event_num(event) != 0;
  }
}

// Return whether a counter is allocated.
static inline bool counter_allocated(const uint8_t counter_num) {
  return ((hero_perf[hero_rt_core_id()]->mcountinhibit >> counter_num) & 1) == 0;
}

// Return the counter *allocated* for an event;
// return -1 if the event is not allocated to any counter.
static int8_t event_counter(const hero_perf_event_t event) {
  if (event_static(event)) {
    const uint8_t counter_num = event_num(event);
    if (counter_allocated(counter_num)) return counter_num;
  } else {
    for (unsigned i = 3; i < 3 + HPM_PROGRAMMABLE_COUNTERS; i++) {
      if (get_mhpmevent(i) == event_num(event)) return i;
    }
  }
  return -1;
}

// Mask for the inhibit register to disable the counter; apply with bitwise OR.
static inline uint32_t inhibit_disable_mask(const uint8_t counter_num) {
  return 1 << counter_num;
}

// Mask for the inhibit register to enable the counter; apply with bitwise AND.
static inline uint32_t inhibit_enable_mask(const uint8_t counter_num) {
  return ~inhibit_disable_mask(counter_num);
}

static inline void counter_inhibit(const uint8_t counter_num) {
  asm volatile("csrs 0x320, %0" : : "r"(inhibit_disable_mask(counter_num)));
}

static inline void counter_uninhibit(const uint8_t counter_num) {
  asm volatile("csrc 0x320, %0" : : "r"(inhibit_disable_mask(counter_num)));
}

static inline void counter_reset(const uint8_t counter_num) {
  switch (counter_num) {
    case  0: asm volatile("csrw 0xB00, x0"); break;
    case  2: asm volatile("csrw 0xB02, x0"); break;
    case  3: asm volatile("csrw 0xB03, x0"); break;
    case  4: asm volatile("csrw 0xB04, x0"); break;
    case  5: asm volatile("csrw 0xB05, x0"); break;
    case  6: asm volatile("csrw 0xB06, x0"); break;
    case  7: asm volatile("csrw 0xB07, x0"); break;
    case  8: asm volatile("csrw 0xB08, x0"); break;
    case  9: asm volatile("csrw 0xB09, x0"); break;
    case 10: asm volatile("csrw 0xB0A, x0"); break;
    case 11: asm volatile("csrw 0xB0B, x0"); break;
    case 12: asm volatile("csrw 0xB0C, x0"); break;
    case 13: asm volatile("csrw 0xB0D, x0"); break;
    case 14: asm volatile("csrw 0xB0E, x0"); break;
    case 15: asm volatile("csrw 0xB0F, x0"); break;
    case 16: asm volatile("csrw 0xB10, x0"); break;
    case 17: asm volatile("csrw 0xB11, x0"); break;
    case 18: asm volatile("csrw 0xB12, x0"); break;
    case 19: asm volatile("csrw 0xB13, x0"); break;
    case 20: asm volatile("csrw 0xB14, x0"); break;
    case 21: asm volatile("csrw 0xB15, x0"); break;
    case 22: asm volatile("csrw 0xB16, x0"); break;
    case 23: asm volatile("csrw 0xB17, x0"); break;
    case 24: asm volatile("csrw 0xB18, x0"); break;
    case 25: asm volatile("csrw 0xB19, x0"); break;
    case 26: asm volatile("csrw 0xB1A, x0"); break;
    case 27: asm volatile("csrw 0xB1B, x0"); break;
    case 28: asm volatile("csrw 0xB1C, x0"); break;
    case 29: asm volatile("csrw 0xB1D, x0"); break;
    case 30: asm volatile("csrw 0xB1E, x0"); break;
    case 31: asm volatile("csrw 0xB1F, x0"); break;
    default: /* do nothing */;
  }
}

int hero_perf_alloc(const hero_perf_event_t event) {
  // Return if event not implemented.
  if (!event_implemented(event)) return -HERO_ENODEV;

  // Return if the event is already assigned to a hardware counter.
  if (event_counter(event) >= 0) return -HERO_EALREADY;

  // Determine index of counter to be allocated.
  uint8_t counter_idx;
  if (event == hero_perf_event_cycle) {
    counter_idx = 0; // cycles are always counted by counter 0
  } else if (event == hero_perf_event_instr_retired) {
    counter_idx = 2; // instructions retired are always counted by counter 2
  } else {
    const uint32_t free_mask = (hero_perf[hero_rt_core_id()]->mcountinhibit) >> 3;
    uint8_t first_free_counter;
    asm volatile("p.ff1 %0, %1" : "=r"(first_free_counter) : "r"(free_mask));
    if (first_free_counter >= 2) { // only two programmable counters implemented
      return -HERO_EBUSY;
    }
    counter_idx = first_free_counter + 3;
  }

  // Allocate counter in library.
  hero_perf[hero_rt_core_id()]->mcountinhibit &= inhibit_enable_mask(counter_idx);

  // Assign event to hardware counter.
  set_mhpmevent(counter_idx, event_num(event));

  // Inhibit and reset hardware counter.
  counter_inhibit(counter_idx);
  counter_reset(counter_idx);

  return 0;
}

int hero_perf_dealloc(const hero_perf_event_t event) {
  // Determine counter for event.
  const int8_t counter = event_counter(event);

  // Return if no counter allocated for event.
  if (counter < 0) return -HERO_EALREADY;

  // Inhibit hardware counter.
  counter_inhibit(counter);

  // Unassign event from hardware counter.
  set_mhpmevent(counter, 0);

  // Deallocate counter in library.
  hero_perf[hero_rt_core_id()]->mcountinhibit |= inhibit_disable_mask(counter);

  return 0;
}

int hero_perf_reset(const hero_perf_event_t event) {
  __compiler_barrier();
  int retval = 0;

  // Determine counter for event.
  const int8_t counter = event_counter(event);

  // Return if no counter allocated for event.
  if (counter < 0) {
    retval = -HERO_EINVAL;
    goto __reset_end;
  }

  // Reset hardware counter.
  counter_reset(counter);

__reset_end:
  __compiler_barrier();
  return retval;
}

void hero_perf_reset_all(void) {
  __compiler_barrier();
  for (unsigned i = 0; i < 3 + HPM_PROGRAMMABLE_COUNTERS; i++) counter_reset(i);
  __compiler_barrier();
}

int hero_perf_pause(const hero_perf_event_t event) {
  __compiler_barrier();
  int ret = 0;

  // Determine counter for event.
  const int8_t counter = event_counter(event);

  // Return if no counter allocated for event.
  if (counter < 0) {
    ret = -HERO_EINVAL;
    goto __pause_end;
  }

  // Inhibit hardware counter.
  counter_inhibit(counter);

__pause_end:
  __compiler_barrier();
  return ret;
}

void hero_perf_pause_all(void) {
  __compiler_barrier();
  // Inhibit all performance counters.
  asm volatile("csrw 0x320, %0" : : "r"(~0));
  __compiler_barrier();
}

int hero_perf_continue(hero_perf_event_t event) {
  __compiler_barrier();
  int ret = 0;

  // Determine counter for event.
  const int8_t counter = event_counter(event);

  // Return if no counter allocated for event.
  if (counter < 0) {
    ret = -HERO_EINVAL;
    goto __continue_end;
  }

  // Uninhibit hardware counter.
  counter_uninhibit(counter);

__continue_end:
  __compiler_barrier();
  return ret;
}

void hero_perf_continue_all(void) {
  __compiler_barrier();
  // Uninhibit all allocated performance counters.
  asm volatile("csrc 0x320, %0" : : "r"(~(hero_perf[hero_rt_core_id()]->mcountinhibit)));
  __compiler_barrier();
}

int64_t hero_perf_read(const hero_perf_event_t event) {
  __compiler_barrier();
  int64_t retval = 0;

  // Determine counter for event.
  const int8_t counter = event_counter(event);

  // Return if no counter allocated for event.
  if (counter < 0) {
    retval = -HERO_EINVAL;
    goto __read_end;
  }

  // Read value of hardware counter.
  uint32_t val;
  switch (counter) {
    case  0: asm volatile("csrr %0, 0xB00" : "=r"(val)); break;
    case  1: asm volatile("csrr %0, 0xB01" : "=r"(val)); break;
    case  2: asm volatile("csrr %0, 0xB02" : "=r"(val)); break;
    case  3: asm volatile("csrr %0, 0xB03" : "=r"(val)); break;
    case  4: asm volatile("csrr %0, 0xB04" : "=r"(val)); break;
    case  5: asm volatile("csrr %0, 0xB05" : "=r"(val)); break;
    case  6: asm volatile("csrr %0, 0xB06" : "=r"(val)); break;
    case  7: asm volatile("csrr %0, 0xB07" : "=r"(val)); break;
    case  8: asm volatile("csrr %0, 0xB08" : "=r"(val)); break;
    case  9: asm volatile("csrr %0, 0xB09" : "=r"(val)); break;
    case 10: asm volatile("csrr %0, 0xB0A" : "=r"(val)); break;
    case 11: asm volatile("csrr %0, 0xB0B" : "=r"(val)); break;
    case 12: asm volatile("csrr %0, 0xB0C" : "=r"(val)); break;
    case 13: asm volatile("csrr %0, 0xB0D" : "=r"(val)); break;
    case 14: asm volatile("csrr %0, 0xB0E" : "=r"(val)); break;
    case 15: asm volatile("csrr %0, 0xB0F" : "=r"(val)); break;
    case 16: asm volatile("csrr %0, 0xB10" : "=r"(val)); break;
    case 17: asm volatile("csrr %0, 0xB11" : "=r"(val)); break;
    case 18: asm volatile("csrr %0, 0xB12" : "=r"(val)); break;
    case 19: asm volatile("csrr %0, 0xB13" : "=r"(val)); break;
    case 20: asm volatile("csrr %0, 0xB14" : "=r"(val)); break;
    case 21: asm volatile("csrr %0, 0xB15" : "=r"(val)); break;
    case 22: asm volatile("csrr %0, 0xB16" : "=r"(val)); break;
    case 23: asm volatile("csrr %0, 0xB17" : "=r"(val)); break;
    case 24: asm volatile("csrr %0, 0xB18" : "=r"(val)); break;
    case 25: asm volatile("csrr %0, 0xB19" : "=r"(val)); break;
    case 26: asm volatile("csrr %0, 0xB1A" : "=r"(val)); break;
    case 27: asm volatile("csrr %0, 0xB1B" : "=r"(val)); break;
    case 28: asm volatile("csrr %0, 0xB1C" : "=r"(val)); break;
    case 29: asm volatile("csrr %0, 0xB1D" : "=r"(val)); break;
    case 30: asm volatile("csrr %0, 0xB1E" : "=r"(val)); break;
    case 31: asm volatile("csrr %0, 0xB1F" : "=r"(val)); break;
  }
  retval = (int64_t)val;

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
