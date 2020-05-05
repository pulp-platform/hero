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

unsigned test_memory()
{
  unsigned n_errors = 0;

  volatile uint32_t* l1 = (volatile uint32_t*)pulp_l1_base();
  const uint32_t l1_val = *l1;
  l1 = (volatile uint32_t*)pulp_l1_end() - 1;
  *l1 = l1_val;
  n_errors += condition_or_printf(*l1 == l1_val, "Failed to access L1");

  volatile uint32_t* l2 = (volatile uint32_t*)pulp_l2_base();
  const uint32_t l2_val = *l2;
  l2 = (volatile uint32_t*)pulp_l2_end() - 1;
  *l2 = l2_val;
  n_errors += condition_or_printf(*l2 == l2_val, "Failed to access L2");

  volatile uint32_t* const ctrl_periph = (volatile uint32_t*)0x10200000;
  n_errors += condition_or_printf(*ctrl_periph == 0,
      "Load from cluster control (EOC register) failed");

  volatile uint32_t* const timer_periph = (volatile uint32_t*)0x10200400;
  n_errors += condition_or_printf(*timer_periph == 0,
      "Load from cluster timer (CFG_LO register) failed");

  volatile uint32_t* const eu_periph = (volatile uint32_t*)0x10200818;
  n_errors += condition_or_printf(*eu_periph == 1,
      "Load from cluster EU (CLOCK_STATUS_CORE0 register) failed");

  volatile uint32_t* const eu1_periph = (volatile uint32_t*)0x10200F00;
  n_errors += condition_or_printf(*eu1_periph == 0,
      "Load from cluster EU (SOC_PERIPH_EVENT_ID register) failed");

  volatile uint32_t* const icache_ctrl_periph = (volatile uint32_t*)0x10201400;
  n_errors += condition_or_printf(*icache_ctrl_periph & 1 == 1,
      "Load from cluster I$ control (ENABLE register) failed");

  volatile uint32_t* const dma_periph = (volatile uint32_t*)0x10201804;
  n_errors += condition_or_printf(*dma_periph == 0,
      "Load from cluster DMA control (STATUS register) failed");

  volatile uint32_t* const per2axi_periph = (volatile uint32_t*)0x10201C00;
  n_errors += condition_or_printf(*per2axi_periph == 0xBADCAB7E,
      "Direct access to per2axi did not return error");

  volatile uint32_t* const err_periph = (volatile uint32_t*)0x10270000;
  n_errors += condition_or_printf(*err_periph == 0xBADCAB7E,
      "Peripheral out-of-range did not return error");

  volatile uint32_t* const hwpe_periph = (volatile uint32_t*)0x10201000;
  n_errors += condition_or_printf(*hwpe_periph == 0xBADCAB7E,
      "Disabled HWPE did not return error");

  printf("Memory access tests completed.\n");
  return n_errors;
}
