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

#include "test.h"
#include <assert.h>
#include <hero-target.h>
#include <string.h>       // memset()

// Mirror definitions from PULP SDK, can be removed as soon as the PULP SDK is accessible through
// Clang.
#include <stdbool.h>
#include <stdint.h>
#define ARCHI_CLUSTER_PERIPHERALS_ADDR  0x10200000
#define ARCHI_MCHAN_EXT_OFFSET          0x00001800
#define DMA_READ(offset) \
  *((volatile uint32_t*)(ARCHI_CLUSTER_PERIPHERALS_ADDR + ARCHI_MCHAN_EXT_OFFSET + (offset)))
#define DMA_WRITE(value, offset) \
  *((volatile uint32_t*)(ARCHI_CLUSTER_PERIPHERALS_ADDR + ARCHI_MCHAN_EXT_OFFSET + (offset))) = value
#define PLP_DMA_SIZE_BIT      00
#define PLP_DMA_TYPE_BIT      17
#define PLP_DMA_INCR_BIT      18
#define PLP_DMA_QUEUE_OFFSET  0x0
#define PLP_DMA_STATUS_OFFSET 0x4
static uint32_t plp_dma_counter_alloc()
{
  return DMA_READ(PLP_DMA_QUEUE_OFFSET);
}
static void plp_dma_cmd_push(uint32_t cmd, uint32_t loc, uint32_t ext)
{
  DMA_WRITE(cmd, PLP_DMA_QUEUE_OFFSET);
  DMA_WRITE(loc, PLP_DMA_QUEUE_OFFSET);
  DMA_WRITE(ext, PLP_DMA_QUEUE_OFFSET);
}
static uint32_t plp_dma_memcpy(uint32_t ext, uint32_t loc, uint16_t size, bool ext2loc)
{
  const uint32_t counter = plp_dma_counter_alloc();
  const uint32_t cmd = (ext2loc << PLP_DMA_TYPE_BIT)
                      | (1 << PLP_DMA_INCR_BIT)
                      | (size << PLP_DMA_SIZE_BIT)
                      // | (trigEvt << PLP_DMA_ELE_BIT) note: dma_wait() will not work without this!
                      // | (trigIrq << PLP_DMA_ILE_BIT)
                      // | (broadcast << PLP_DMA_BLE_BIT)
                      ;
  __asm__ __volatile__("" : : : "memory");
  plp_dma_cmd_push(cmd, loc, ext);
  return counter;
}
static void plp_dma_counter_free(uint32_t counter)
{
  DMA_WRITE(1 << counter, PLP_DMA_STATUS_OFFSET);
}
void rt_time_wait_cycles(const unsigned cycles)
{
  // simplified, the one in PULP SDK is more accurate
  for (unsigned i = 0; i < cycles; ++i) {
    __asm__ volatile ("nop" : : : );
  }
  return;
}

// Regression test for counter overflow in TCDM unit
static bool regression_tcdm_counter_overflow()
{
  const uint32_t l2_addr = 0x1c02a7d4;
  const uint32_t l1_addr = 0x100fbea0;
  const uint32_t size    = 2144;
  if (l2_addr + size >= (uint32_t)pulp_l2_end()) {
   printf("Warning: TCDM counter overflow regression skipped due to L2 size.\n");
   return false;
  }
  if (l1_addr + size >= (uint32_t)pulp_l1_end()) {
   printf("Warning: TCDM counter overflow regression skipped due to L1 size.\n");
   return false;
  }
  const int dma = plp_dma_memcpy(l2_addr, l1_addr, size, true);
  const short unsigned timeout_delta = 256;
  unsigned counter = 256 * timeout_delta;
  bool timeout = false;
  while (DMA_READ(PLP_DMA_STATUS_OFFSET) & (1 << dma)) {
    rt_time_wait_cycles(timeout_delta);
    counter -= timeout_delta;
    timeout = condition_or_printf(counter > 0, "DMA transfer timed out");
    if (timeout) break;
  }
  plp_dma_counter_free(dma);
  return timeout;
}

// Verify transfers to or from L1
static unsigned check_to_or_from_l1(uint32_t* const src, uint32_t* const dst, const size_t n_elem)
{
  // Initialize source memory.
  for (unsigned i = 0; i < n_elem; i++) {
    src[i] = i;
  }
  // Start DMA transfer and wait for its completion.
  const size_t size = n_elem * sizeof(uint32_t);
  hero_dma_job_t dma0 = hero_dma_memcpy_async(dst, src, size);
  hero_dma_wait(dma0);
  // Assert that destination data matches source data.
  unsigned n_errors = 0;
  for (unsigned i = 0; i < n_elem; i++) {
    n_errors += (dst[i] != i);
  }
  condition_or_printf(n_errors == 0, "%d destination elements did not match!\n", n_errors);
  // Reset destination memory.
  memset(dst, 0, size);
  // Return error count.
  return n_errors;
}
static unsigned to_or_from_l1()
{
  const size_t n_elem = 64;
  const size_t size = n_elem * sizeof(uint32_t);
  // Allocate local memory.
  uint32_t* const loc = (uint32_t*)hero_l1malloc(size);
  assert(loc);

  uint32_t* const l3 = (uint32_t*)0x80000000;
  uint32_t* const l2 = (uint32_t*)pulp_l2_end() - 0x1000;
  uint32_t* const other_l1 = (uint32_t*)pulp_cluster_base(1) + 0x1000;
  unsigned n_errors = 0;
  printf("DMA: L3 to L1 ..\n");
  n_errors += check_to_or_from_l1(l3, loc, n_elem);
  printf("DMA: L2 to L1 ..\n");
  n_errors += check_to_or_from_l1(l2, loc, n_elem);
  if (pulp_n_clusters() > 1) {
    printf("DMA: Other L1 to L1 ..\n");
    n_errors += check_to_or_from_l1(other_l1, loc, n_elem);
  } else {
    printf("Warning: DMA from other L1 skipped because only one cluster.\n");
  }
  printf("DMA: L1 to L3 ..\n");
  n_errors += check_to_or_from_l1(loc, l3, n_elem);
  printf("DMA: L1 to L2 ..\n");
  n_errors += check_to_or_from_l1(loc, l2, n_elem);
  if (pulp_n_clusters() > 1) {
    printf("DMA: L1 to other L1 ..\n");
    n_errors += check_to_or_from_l1(loc, other_l1, n_elem);
  } else {
    printf("Warning: DMA to other L1 skipped because only one cluster.\n");
  }

  hero_l1free(loc);
  return n_errors;
}

unsigned test_dma()
{
  unsigned n_errors = 0;

  n_errors += regression_tcdm_counter_overflow();
  n_errors += to_or_from_l1();

  return n_errors;
}
