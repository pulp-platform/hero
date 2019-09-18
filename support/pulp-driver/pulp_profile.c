/*
 * This file is part of the PULP device driver.
 *
 * Copyright (C) 2018 ETH Zurich, University of Bologna
 *
 * Author: Koen Wolters <kwolters@student.ethz.ch>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "pulp_profile.h"

#include <asm/io.h>

#include "pulp_module.h"

#ifdef __riscv
static uint64_t clk_cnt_ref = 0;
#endif

uint64_t host_get_clock_counter(void)
{
  uint64_t clk_counter = 0;
#if defined(__riscv)
  asm volatile("csrr %0, cycle" : "=r"(clk_counter));
  return U64_COUNTER_DIFF(clk_cnt_ref, clk_counter);
#elif defined(__arm__)
  asm volatile("mrc p15, 0, %0, c9, c13, 0" : "=r"(clk_counter) :);
  return clk_counter;
#else
  return clk_counter;
#endif
}

void host_reset_clock_counter(void)
{
#if defined(__riscv)
  asm volatile("csrr %0, cycle" : "=r"(clk_cnt_ref));
#elif defined(__arm__)
  asm volatile("mcr p15, 0, %0, c9, c12, 0" ::"r"(0xD));
#endif
}

uint64_t host_get_time(void)
{
  return ktime_to_ns(ktime_get());
}

uint64_t accel_get_clk(void *clusters, int index)
{
  uint64_t time;
  time = ioread32(clusters + CLUSTER_SIZE_B * index + TIMER_GET_TIME_HI_OFFSET_B);
  time <<= 32;
  time |= ioread32(clusters + CLUSTER_SIZE_B * index + TIMER_GET_TIME_LO_OFFSET_B);
  return time;
}

void accel_reset_clk(void *clusters, int index)
{
  iowrite32(0x1, clusters + CLUSTER_SIZE_B * index + TIMER_STOP_OFFSET_B);
  iowrite32(0x1, clusters + CLUSTER_SIZE_B * index + TIMER_RESET_OFFSET_B);
  iowrite32(0x1, clusters + CLUSTER_SIZE_B * index + TIMER_START_OFFSET_B);
}
