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

// Mirror definitions from PULP SDK, can be removed as soon as the PULP SDK is accessible through
// Clang.
#include <stdbool.h>
#include <stdint.h>
#define ARCHI_DEMUX_PERIPHERALS_ADDR  0x1B204000
#define ARCHI_MCHAN_DEMUX_OFFSET         0x00400
#define DMA_READ(offset) \
  *((volatile uint32_t*)(ARCHI_DEMUX_PERIPHERALS_ADDR + ARCHI_MCHAN_DEMUX_OFFSET + (offset)))
#define DMA_WRITE(value, offset) \
  *((volatile uint32_t*)(ARCHI_DEMUX_PERIPHERALS_ADDR + ARCHI_MCHAN_DEMUX_OFFSET + (offset))) = value
#define PLP_DMA_SIZE_BIT        0
#define PLP_DMA_TYPE_BIT       16
#define PLP_DMA_INCR_BIT       17
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
  const int dma = plp_dma_memcpy(0x1c02a7d4, 0x100fbea0, 2144, true);
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

unsigned test_dma()
{
  unsigned n_errors = 0;

  n_errors += regression_tcdm_counter_overflow();

  return n_errors;
}
