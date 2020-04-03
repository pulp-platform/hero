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

void perform_benchmark(int buf_size_kb) {
    int cyc_31d = 0, cyc_12d = 0;
    int cyc_31s = 0, cyc_12s = 0;
    int buf_size = buf_size_kb * 1024;

    #pragma omp target map(to: buf_size) map(from: cyc_31d, cyc_12d, cyc_31s, cyc_12s)
    {
        void* buf_l1 = hero_l1malloc(buf_size);
        void* buf_l2 = hero_l2malloc(buf_size);

        // L3 (RAM) to L1 with DMA
        hero_rt_reset_cycle_cnt();
        hero_rt_start_cycle_cnt();

        hero_dma_memcpy(buf_l1, BUF_L3, buf_size);

        hero_rt_stop_cycle_cnt();
        cyc_31d = hero_rt_get_cycles();

        // L1 to L2 with DMA
        hero_rt_reset_cycle_cnt();
        hero_rt_start_cycle_cnt();

        hero_dma_memcpy(buf_l2, buf_l1, buf_size);

        hero_rt_stop_cycle_cnt();
        cyc_12d = hero_rt_get_cycles();

        // L3 (RAM) to L2 with loop
        hero_rt_reset_cycle_cnt();
        hero_rt_start_cycle_cnt();

        for (int i = 0; i < buf_size / 4; i++)
            ((int*) buf_l1)[i] = ((int*) BUF_L3)[i];

        hero_rt_stop_cycle_cnt();
        cyc_31s = hero_rt_get_cycles();

        // L1 to L2 with loop
        hero_rt_reset_cycle_cnt();
        hero_rt_start_cycle_cnt();

        for (int i = 0; i < buf_size / 4; i++)
            ((int*) buf_l2)[i] = ((int*) buf_l1)[i];

        hero_rt_stop_cycle_cnt();
        cyc_12s = hero_rt_get_cycles();

        hero_l1free(buf_l1);
        hero_l2free(buf_l2);
    }

    double perf_31d = ((double) buf_size) / cyc_31d;
    double perf_12d = ((double) buf_size) / cyc_12d;
    double perf_31s = ((double) buf_size) / cyc_31s;
    double perf_12s = ((double) buf_size) / cyc_12s;
    printf("For buffer size %dkB:\n", buf_size_kb);
    printf("L3 -> L1 DMA:  %f bytes / cycle\n", perf_31d);
    printf("L1 -> L2 DMA:  %f bytes / cycle\n", perf_12d);
    printf("L3 -> L1 loop: %f bytes / cycle\n", perf_31s);
    printf("L1 -> L2 loop: %f bytes / cycle\n", perf_12s);
}

int main(int argc, char *argv[]) {
    omp_set_default_device(BIGPULP_SVM);

    int buffer_sizes[] = {220};//{1, 2, 4, 8, 16, 32, 64};
    for(int i = 0; i < sizeof(buffer_sizes) / sizeof(int); i++) {
        perform_benchmark(buffer_sizes[i]);
    }

    return 0;
}

