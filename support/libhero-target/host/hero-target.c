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
#include <omp.h>
#include <stdlib.h>
#include <string.h>

unsigned int hero_tryread(const unsigned int* const addr)
{
	return (unsigned int)(*(const volatile unsigned *) addr);
}

int
hero_tryread_prefetch(const unsigned int* const addr)
{
	return 0;
}

void
hero_trywrite(unsigned int* const addr, const unsigned int val)
{
	*addr = val;
}

int
hero_trywrite_prefetch(unsigned int* const addr)
{
	return 0;
}

int
hero_handle_rab_misses(void)
{
	return 0;
}

hero_dma_job_t 
hero_dma_memcpy_async(void *dst, void *src, int size)
{
	memcpy(dst, src, size);
	return 0;
}

void
hero_dma_memcpy(void *dst, void *src, int size)
{
	memcpy(dst, src, size);
}

void
hero_dma_wait(hero_dma_job_t id)
{
	return;
}

void *
hero_l1malloc(int size)
{
	return malloc(size);
}
void *
hero_l2malloc(int size)
{
	return malloc(size);
}
void *
hero_l3malloc(int size)
{
  // FIXME: use actual L3 memory
  return malloc(size);
}

void
hero_l1free(void * a)
{
  free(a);
}
void
hero_l2free(void * a)
{
  free(a);
}
void
hero_l3free(void * a)
{
  free(a);
}

int
hero_rt_core_id(void)
{
  return omp_get_thread_num();
}

// FIXME implement clock counters for host
void
hero_reset_clk_counter(void) {
    return;
}

int
hero_get_clk_counter(void) {
    return 0;
}
