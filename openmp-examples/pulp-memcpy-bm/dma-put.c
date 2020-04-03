/*
 * HERO HelloWorld Example Application
 *
 * Copyright 2018 ETH Zurich, University of Bologna
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

//void perform_benchmark(int buf_size_kb) {
//    int cyc_31 = 0, cyc_13 = 0;
//    int buf_size = buf_size_kb * 1024;
//
//    #pragma omp target map(to: buf_size) //map(from: cyc_31, cyc_13)
//    {
//        printf("inside the pragma with %llx\n", buf_size);
//        //void* buf_l1 = hero_l1malloc(buf_size);
//
//        //// L3 (RAM) to L1 with DMA
//        //hero_rt_reset_cycle_cnt();
//        //hero_rt_start_cycle_cnt();
//
//        //hero_dma_memcpy(buf_l1, BUF_L3, buf_size);
//
//        //hero_rt_stop_cycle_cnt();
//        //cyc_31 = hero_rt_get_cycles();
//
//        //// L1 to L3 (RAM) with DMA
//        //hero_rt_reset_cycle_cnt();
//        //hero_rt_start_cycle_cnt();
//
//        //hero_dma_memcpy(BUF_L3, buf_l1, buf_size);
//
//        //hero_rt_stop_cycle_cnt();
//        //cyc_13 = hero_rt_get_cycles();
//    }
//
//    printf("For buffer size %dkB:\n", buf_size_kb);
//    printf("L3 -> L1 DMA:  %d cycles\n", cyc_31);
//    printf("L1 -> L3 DMA:  %d cycles\n", cyc_13);
//}

int main(int argc, char *argv[]) {
  omp_set_default_device(BIGPULP_MEMCPY);

  int buffer_sizes[] = {128};//{1, 2, 4, 8, 16, 32, 64};
  for(int i = 0; i < sizeof(buffer_sizes) / sizeof(int); i++) {
    int cyc_31 = 0, cyc_13 = 0;
    int buf_size = buffer_sizes[i] * 1024;

    #pragma omp target map(to: buf_size) map(from: cyc_31, cyc_13)
    {
      void* buf_l1 = hero_l1malloc(buf_size);

      // L1 to L3 (RAM) with DMA
      hero_reset_clk_counter();
      hero_dma_memcpy(BUF_L3, buf_l1, buf_size);
      cyc_13 = hero_get_clk_counter();
      
      // L3 (RAM) to L1 with DMA
      hero_reset_clk_counter();
      hero_dma_memcpy(buf_l1, BUF_L3, buf_size);
      cyc_31 = hero_get_clk_counter();

      printf("Device: L3 -> L1 DMA:  %d cycles\n", cyc_31);
      printf("Device: L1 -> L3 DMA:  %d cycles\n", cyc_13);
    }
    printf("For buffer size %dkB:\n", buffer_sizes[i]);
    printf("L3 -> L1 DMA:  %d cycles (%f B/cy)\n", cyc_31, (float) (buffer_sizes[i] * 1024) / (float) cyc_31);
    printf("L1 -> L3 DMA:  %d cycles (%f B/cy)\n", cyc_13, (float) (buffer_sizes[i] * 1024) / (float) cyc_13);

  }
  return 0;
}

