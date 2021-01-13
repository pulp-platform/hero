/*
 * HERO DMA Performance Benchmark
 *
 * Copyright 2020 ETH Zurich, University of Bologna
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

#include <omp.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <time.h>
#include <hero-target.h>
//#include "pulp.h"

#define BUF_L3 (void*) 0x80000000

void perform_benchmark(int buf_size_kb) {
    int cyc_31 = 0;
    int cyc_13 = 0;
    int buf_size = buf_size_kb * 1024;

    #pragma omp target device(BIGPULP_MEMCPY) map(to: buf_size) map(from: cyc_13, cyc_31)
    {
        __device uint32_t* buf_l1 = (__device uint32_t*) hero_l1malloc(buf_size);
        if (buf_l1 == NULL){
          printf("ERROR: hero_l1malloc() failed\n");
        }

        // L1 to L3 (RAM) with DMA
        hero_reset_clk_counter();
        hero_memcpy_host2dev(buf_l1, (__host void*) BUF_L3, buf_size);
        cyc_31 = hero_get_clk_counter();

        // L3 (RAM) to L1 with DMA
        hero_reset_clk_counter();
        hero_memcpy_dev2host((__host void*) BUF_L3, buf_l1, buf_size);
        cyc_13 = hero_get_clk_counter();


        hero_l1free(buf_l1);
    }

    double perf_31 = ((double) buf_size) / cyc_31;
    double perf_13 = ((double) buf_size) / cyc_13;
    printf("For buffer size %dkB:\n", buf_size_kb);
    printf("L3 -> L1 DMA:  %f bytes / cycle\n", perf_31);
    printf("L1 -> L3 DMA:  %f bytes / cycle\n", perf_13);
}

int main(int argc, char *argv[]) {
  omp_set_default_device(BIGPULP_SVM);

  //int buffer_sizes[] = {1, 2, 4, 8, 16, 32, 64};
  int buffer_sizes[] = {110};
  for(int i = 0; i < sizeof(buffer_sizes) / sizeof(int); i++) {
    perform_benchmark(buffer_sizes[i]);
  }

  return 0;
}


