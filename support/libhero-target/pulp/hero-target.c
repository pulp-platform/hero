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

#define DEBUG(...)  // printf(__VA_ARGS__)

#define DMA_MAX_NUM_STREAMS 8

typedef struct {
  uint32_t id;
  uint32_t padding;
} _hero_dma_done_id_t;

// base address struct of the dma
typedef struct {
  uint32_t src_addr_low;
  uint32_t src_addr_high;
  uint32_t dst_addr_low;
  uint32_t dst_addr_high;
  uint32_t num_bytes;
  uint32_t config __attribute__((aligned(8)));
  uint32_t tf_id __attribute__((aligned(8)));
  _hero_dma_done_id_t done[DMA_MAX_NUM_STREAMS] __attribute__((aligned(8)));
} _hero_dma_conf_t;

static volatile _hero_dma_conf_t* const _hero_dma_conf = (_hero_dma_conf_t*)0x1B204400;

// read the id of the last transaction that has been completed
static inline uint32_t _hero_read_completed_id(uint32_t stream_id) {
  return _hero_dma_conf->done[stream_id].id;
}

// wait for a given transaction to complete
static inline void _hero_wait_for_tf_completion(uint32_t stream_id, uint32_t tf_id) {
  // spin until transfer is completed
  while (tf_id > _hero_read_completed_id(stream_id)) {
    asm volatile("nop");
  }
}

hero_dma_job_t hero_memcpy_host2dev_async(DEVICE_VOID_PTR dst, const HOST_VOID_PTR src,
                                          uint32_t size) {
  // configure the dma
  _hero_dma_conf->src_addr_low = (uint32_t)src;
  _hero_dma_conf->dst_addr_low = (uint32_t)dst;
  _hero_dma_conf->num_bytes = size;

  // launch the transfer
  hero_dma_job_t hero_dma_job;
  hero_dma_job.id = _hero_dma_conf->tf_id;
  return hero_dma_job;
}

hero_dma_job_t hero_memcpy_dev2host_async(HOST_VOID_PTR dst, const DEVICE_VOID_PTR src,
                                          uint32_t size) {
  // configure the dma
  _hero_dma_conf->src_addr_low = (uint32_t)src;
  _hero_dma_conf->dst_addr_low = (uint32_t)dst;
  _hero_dma_conf->num_bytes = size;

  // launch the transfer
  hero_dma_job_t hero_dma_job;
  hero_dma_job.id = _hero_dma_conf->tf_id;
  return hero_dma_job;
}

void hero_memcpy_host2dev(DEVICE_VOID_PTR dst, const HOST_VOID_PTR src, uint32_t size) {
  hero_dma_wait(hero_memcpy_host2dev_async(dst, src, size));
}

void hero_memcpy_dev2host(HOST_VOID_PTR dst, const DEVICE_VOID_PTR src, uint32_t size) {
  hero_dma_wait(hero_memcpy_dev2host_async(dst, src, size));
}

void hero_dma_wait(hero_dma_job_t id) {
  uint32_t tf_id = id.id & 0x0fffffff;
  uint32_t stream = (id.id & 0xf0000000) >> 28;
  _hero_wait_for_tf_completion(stream, tf_id);
}

DEVICE_VOID_PTR
hero_l1malloc(int32_t size) { return l1malloc(size); }

DEVICE_VOID_PTR
hero_l2malloc(int32_t size) { return l2malloc(size); }

HOST_VOID_PTR
hero_l3malloc(int32_t size) {
  printf("Trying to allocate L3 memory from PULP, which is not defined\n");
  return (HOST_VOID_PTR)0;
}

void hero_l1free(DEVICE_VOID_PTR a) { l1free(a); }

void hero_l2free(DEVICE_VOID_PTR a) { l2free(a); }

void hero_l3free(HOST_VOID_PTR a) {
  printf("Trying to free L3 memory from PULP, which is not defined\n");
  return;
}

int32_t hero_rt_core_id(void) { return rt_core_id(); }

int32_t hero_get_clk_counter(void) { return get_time(); }

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
    case hero_perf_event_stall_load:      return  1;
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

#define __hero_atomic_define(op, type)                                                           \
  type hero_atomic_##op(DEVICE_PTR_CONST ptr, const type val) {                                  \
    /*assert(((uint32_t)ptr & 0x3) == 0);*/ /* only four-byte aligned addresses are supported */ \
    type orig;                                                                                   \
    __asm__ volatile("amo" #op ".w %[orig], %[val], (%[ptr])"                                    \
                     : [orig] "=r"(orig), "+m"(*ptr)                                             \
                     : [val] "r"(val), [ptr] "r"(ptr)                                            \
                     : "memory");                                                                \
    return orig;                                                                                 \
  }

__hero_atomic_define(swap, int32_t)
__hero_atomic_define(add, int32_t)
__hero_atomic_define(and, int32_t)
__hero_atomic_define(or, int32_t)
__hero_atomic_define(xor, int32_t)
__hero_atomic_define(max, int32_t)
__hero_atomic_define(maxu, uint32_t)
__hero_atomic_define(min, int32_t)
__hero_atomic_define(minu, uint32_t)
