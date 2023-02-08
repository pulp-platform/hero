/*
 * HERO Matrix-Matrix Multiplication for Small Matrices Example Application
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

#ifdef __HERO_DEV
#include <dm.h>
#include <printf.h>
#include <snrt.h>
#include <snitch_hero_support.h>
#else
#define snrt_printf(...) printf(__VA_ARGS__)
#define snrt_dma_txid_t uint32_t
#define snrt_l1alloc(size) malloc(size)
#define dm_memcpy_async(a, b, c)
#define dm_wait(x)
#define csleep(x) usleep(x)
#define snrt_memcpy(dst, src, size) memcpy(dst, src, size)
#endif

// #define DTYPE uint32_t
#define DTYPE uint32_t

#include <errno.h>  // for error codes
#include <hero-target.h>
#include <inttypes.h>
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "bench.h"

int main(int argc, char *argv[]) {
  printf("HERO data mapping started.\n");

  uint32_t tmp_0a[16], *tmp_0b;
  uint32_t tmp_0b_len = 16;
  uint32_t tmp_1a = 0x1a1a1a1a, tmp_1b = 0x1b1b1b1b;
  uint32_t tmp_2 = 0x0;

  tmp_0b = malloc(tmp_0b_len * sizeof(uint32_t));

  for (int i = 0; i < 16; i++) {
    tmp_0a[i] = i;
    tmp_0b[i] = i+0xb00;
  }

  printf("\n-----> tmp_0a = %#" PRIx64 " ; &tmp_0a=%#" PRIx64 " ; tmp_0a[0]=%x\n", (uint64_t)tmp_0a,
         (uint64_t)&tmp_0a, tmp_0a[0]);
  printf("-----> tmp_0b = %#" PRIx64 " ; &tmp_0b=%#" PRIx64 " ; tmp_0b[0]=%x\n", (uint64_t)tmp_0b,
         (uint64_t)&tmp_0b, tmp_0b[0]);
  printf("-----> tmp_0b_len = %#x ; &tmp_0b_len=%#" PRIx64 "\n", tmp_0b_len, (uint64_t)&tmp_0b_len);
  printf("-----> tmp1a = %#x ; &tmp1a=%#" PRIx64 "\n", tmp_1a, (uint64_t)&tmp_1a);
  printf("-----> tmp1b = %#x ; &tmp1b=%#" PRIx64 "\n", tmp_1b, (uint64_t)&tmp_1b);
  printf("-----> tmp2 = %#x ; &tmp2=%#" PRIx64 "\n\n", tmp_2, (uint64_t)&tmp_2);

#pragma omp target device(HERODEV_MEMCPY) map(to: tmp_0b_len) map(to : tmp_0a [0:16], tmp_0b[0:tmp_0b_len]) map(to : tmp_1a) map(to : tmp_1b) map(from : tmp_2)
  {

    /* Computations */
    tmp_2 = tmp_1a & tmp_1b;

    /* Prints */
    snrt_printf("\n");
    snrt_printf("-----> [%d/%d] Starting\n", omp_get_thread_num(), omp_get_num_threads());

    // Print tmp_0a
    snrt_printf("-----> [%d/%d] tmp_0a=%#x &tmp_0a=%#x\n----->", omp_get_thread_num(),
                omp_get_num_threads(), tmp_0a, &tmp_0a);
    for (int i = 0; i < 16; i++) snrt_printf("%08x - ", ((uint32_t*) tmp_0a)[i]);
    snrt_printf("\n");

    snrt_printf("\n-----> [%d/%d] tmp_0b_len=%#x &tmp_0b_len=%#x\n", omp_get_thread_num(),
                omp_get_num_threads(), tmp_0b_len, &tmp_0b_len);

    // Print tmp_0b
    snrt_printf("-----> [%d/%d] tmp_0b=%#x &tmp_0b=%#x\n----->", omp_get_thread_num(),
                omp_get_num_threads(), tmp_0b, &tmp_0b);
    for (int i = 0; i < 16; i++) snrt_printf("%08x - ", ((uint32_t*) tmp_0b)[i]);
    snrt_printf("\n");

    // Print tmp_1... and tmp_2
    snrt_printf("-----> [%d/%d] tmp_1a=%#x &tmp_1a=%#x\n", omp_get_thread_num(),
                omp_get_num_threads(), tmp_1a, &tmp_1a);
    
    snrt_printf("-----> [%d/%d] tmp_1b=%#x &tmp_1b=%#x\n", omp_get_thread_num(),
                omp_get_num_threads(), tmp_1b, &tmp_1b);

    snrt_printf("-----> [%d/%d] tmp_2=%#x &tmp_2=%#x\n\n", omp_get_thread_num(),
                omp_get_num_threads(), tmp_2, &tmp_2);

    // Sleep just for the UART buffer
    csleep(10000000);
  }

  // Print tmp_2 result
  printf("-----> tmp2 = %#x ; &tmp2=%#" PRIx64 "\n\n", tmp_2, (uint64_t)&tmp_2);

  #pragma omp target device(HERODEV_MEMCPY) map(tofrom : tmp_2)
  {
    #pragma omp parallel
    {
      tmp_2 = tmp_2++;
      snrt_printf("-----> [%d/%d] tmp_2=%#x &tmp_2=%#x\n\n", omp_get_thread_num(),
                  omp_get_num_threads(), tmp_2, &tmp_2);
      // Sleep just for the UART buffer
      csleep(10000000);
    }
  }

  return 0;
}
