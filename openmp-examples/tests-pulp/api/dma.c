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

// Verify transfers to or from L1
static unsigned check_to_l1(__host uint32_t* const src, uint32_t* const dst, const size_t n_elem)
{
  // Initialize source memory.
  for (unsigned i = 0; i < n_elem; i++) {
    src[i] = i;
  }
  // Start DMA transfer and wait for its completion.
  const size_t size = n_elem * sizeof(uint32_t);
  hero_dma_job_t dma0 = hero_memcpy_host2dev_async(dst, src, size);
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

// Verify transfers to or from L1
static unsigned check_from_l1(uint32_t* const src, __host uint32_t* const dst, const size_t n_elem)
{
  // Initialize source memory.
  for (unsigned i = 0; i < n_elem; i++) {
    src[i] = i;
  }
  // Start DMA transfer and wait for its completion.
  const size_t size = n_elem * sizeof(uint32_t);
  hero_dma_job_t dma0 = hero_memcpy_dev2host_async(dst, src, size);
  hero_dma_wait(dma0);
  // Assert that destination data matches source data.
  unsigned n_errors = 0;
  for (unsigned i = 0; i < n_elem; i++) {
    n_errors += (dst[i] != i);
  }
  condition_or_printf(n_errors == 0, "%d destination elements did not match!\n", n_errors);
  // Reset destination memory.
  for (int i = 0; i < n_elem; i++) {
    dst[i] = 0;
  }
  // Return error count.
  return n_errors;
}
static unsigned to_or_from_l1()
{
  const size_t n_elem = 64;
  const size_t size = n_elem * sizeof(uint32_t);
  // Allocate local memory.
  uint32_t* const loc = (__device uint32_t*)hero_l1malloc(size);
  assert(loc);

  __host uint32_t* const l3 = (__host uint32_t*)0x80000000;
  uint32_t* const l2 = (__device uint32_t*)pulp_l2_end() - 0x1000;
  uint32_t* const other_l1 = (__device uint32_t*)pulp_cluster_base(1) + 0x1000;
  unsigned n_errors = 0;
  printf("DMA: L3 to L1 ..\n");
  n_errors += check_to_l1(l3, loc, n_elem);
  printf("DMA: L2 to L1 ..\n");
  n_errors += check_to_l1(l2, loc, n_elem);
  if (pulp_n_clusters() > 1) {
    printf("DMA: Other L1 to L1 ..\n");
    n_errors += check_to_l1(other_l1, loc, n_elem);
  } else {
    printf("Warning: DMA from other L1 skipped because only one cluster.\n");
  }
  printf("DMA: L1 to L3 ..\n");
  n_errors += check_from_l1(loc, l3, n_elem);
  printf("DMA: L1 to L2 ..\n");
  n_errors += check_from_l1(loc, l2, n_elem);
  if (pulp_n_clusters() > 1) {
    printf("DMA: L1 to other L1 ..\n");
    n_errors += check_to_l1(loc, other_l1, n_elem);
  } else {
    printf("Warning: DMA to other L1 skipped because only one cluster.\n");
  }

  hero_l1free(loc);
  return n_errors;
}

unsigned test_dma()
{

  if (hero_rt_core_id() != 0) {
    return 0;
  }

  unsigned n_errors = 0;

  n_errors += to_or_from_l1();

  return n_errors;
}
