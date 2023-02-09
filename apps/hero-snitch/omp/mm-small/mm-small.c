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
#else
#define snrt_printf(...) printf(__VA_ARGS__)
#define snrt_dma_txid_t uint32_t
#define snrt_l1alloc(size) malloc(size)
#define dm_memcpy_async(dst, src, size) memcpy(dst, src, size)
#define dm_wait(x)
#endif

#define snrt_log(VAR) snrt_printf("-----> [%d/%d] "#VAR"=%#x &"#VAR"=%#x\n", omp_get_thread_num(), omp_get_num_threads(), VAR, &VAR);

// #define DTYPE uint32_t
#define DTYPE double

#include "bench.h"
#include <errno.h> // for error codes
#include <hero-target.h>
#include <inttypes.h>
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int compare_matrices(DTYPE *a, DTYPE *b, uint32_t width, uint32_t height) {
  for (uint32_t i = 0; i < width; i++) {
    for (uint32_t j = 0; j < height; j++) {
      if (a[i * width + j] != b[i * width + j]) {
        printf("ERROR: Result mismatch in Row %u, Column %u!\n", j, i);
        return -1;
      }
    }
  }
  printf("Result match\n");
  return 0;
}

int main(int argc, char *argv[]) {
  printf("HERO matrix multiplication started.\n");

  uint32_t width = 128;
  double time;
  uint32_t error = 0;
  if (argc > 1) {
    width = strtoul(argv[1], NULL, 0);
  }
  if (width > 140) {
    printf("WARNING: widths greater than 140 entries not supported, falling back to 128.\n");
    width = 128;
  }
  uint32_t height = width;

  // Allocate memory
  DTYPE *a = (DTYPE *)malloc(sizeof(DTYPE) * width * height);
  DTYPE *b = (DTYPE *)malloc(sizeof(DTYPE) * width * height);
  DTYPE *c = (DTYPE *)malloc(sizeof(DTYPE) * width * height);
  DTYPE *d = (DTYPE *)malloc(sizeof(DTYPE) * width * height);
  if ((a == NULL) || (b == NULL) || (c == NULL) || (d == NULL)) {
    printf("ERROR: malloc() failed!\n");
    return -ENOMEM;
  }
  printf("width = %u, height = %u, a @ %#" PRIx64 ", b @ %#" PRIx64 ", c @ %#" PRIx64 "\n", width,
         height, (uint64_t)a, (uint64_t)b, (uint64_t)c);

  // Init matrices
  for (uint32_t i = 0; i < width; i++) {
    for (uint32_t j = 0; j < height; j++) {
      a[i * width + j] = (DTYPE)(i * width + j);
      b[i * width + j] = (DTYPE)(i == j ? 2 : 0);
    }
  }
  memset(c, 0, (size_t)(sizeof(DTYPE) * width * height));
  memset(d, 0, (size_t)(sizeof(DTYPE) * width * height));

  /*
   * Execute on host
   */

  printf("\n");
  bench_start("CVA6 Host: Single-threaded");
#pragma omp parallel firstprivate(a, b, d, width, height)
  {
#pragma omp for collapse(2)
    for (uint32_t i = 0; i < width; i++) {
      for (uint32_t j = 0; j < height; j++) {
        DTYPE sum = 0;
        for (uint32_t k = 0; k < width; k++)
          sum = sum + a[i * width + k] * b[k * width + j];
        d[i * width + j] = sum;
      }
    }
  }
  time = bench_stop();
  printf("csv : %u\n", width);
  printf("csv : %i %f\n", error, time);

  /*
   * Execute on Device
   */

  /*
   * Make sure Device is ready - speeds up the first target
   *
   * Actually, we should not use both devices at the same time as it is not safe. OpenMP will
   load
   * or boot both of them. But in reality only one accelerator is there.
   */
  uint32_t tmp_1 = 10;
  uint32_t tmp_2 = 20;

  printf("\n");
  bench_start("HERO Device: Waking up and preparing device");
#pragma omp target device(HERODEV_MEMCPY) map(to : tmp_1) map(from : tmp_2)
  { tmp_2 = tmp_1; }
  tmp_1 = tmp_2;
  bench_stop();

  printf("\n");
  bench_start("HERO Device: Single-threaded, copy-based, no DMA");
#pragma omp target device(HERODEV_MEMCPY)                                                          \
    map(to                                                                                         \
        : a [0:width * height], b [0:width * height], width, height) map(from                      \
                                                                         : c [0:width * height])
  {
    for (uint32_t i = 0; i < width; i++) {
      for (uint32_t j = 0; j < height; j++) {
        DTYPE sum = 0;
        for (uint32_t k = 0; k < width; k++)
          sum = sum + a[i * width + k] * b[k * width + j];
        c[i * width + j] = sum;
      }
    }
  }
  time = bench_stop();
  error = compare_matrices(c, d, width, height);
  printf("csv : %i %f\n", error, time);

  memset(c, 0, (size_t)(sizeof(DTYPE) * width * height));

  // omp_set_num_threads(omp_get_thread_limit());
  printf("\n");
  bench_start("HERO Device: Parallel, copy-based, no DMA");
#pragma omp target device(HERODEV_MEMCPY)                                                          \
    map(to                                                                                         \
        : a [0:width * height], b [0:width * height], width, height) map(from                      \
                                                                         : c [0:width * height])
  {
#pragma omp parallel for collapse(2) firstprivate(width, height)
    for (uint32_t i = 0; i < width; i++) {
      for (uint32_t j = 0; j < height; j++) {
        DTYPE sum = 0;
        for (uint32_t k = 0; k < width; k++)
          sum = sum + a[i * width + k] * b[k * width + j];
        c[i * width + j] = sum;
      }
    }
  }
  time = bench_stop();
  error = compare_matrices(c, d, width, height);
  printf("csv : %i %f\n", error, time);

  memset(c, 0, (size_t)(sizeof(DTYPE) * width * height));

  printf("\n");
  bench_start("HERO Device: Single-threaded, copy-based, DMA");
#pragma omp target device(HERODEV_MEMCPY) map(to                                                   \
                                              : a [0:width * height], b [0:width * height])        \
    map(from                                                                                       \
        : c [0:width * height])
  {
    __device DTYPE *a_local =
        (__device DTYPE *)snrt_l1alloc(width * height * sizeof(DTYPE));
    __device DTYPE *b_local =
        (__device DTYPE *)snrt_l1alloc(width * height * sizeof(DTYPE));
    __device DTYPE *c_local =
        (__device DTYPE *)snrt_l1alloc(width * height * sizeof(DTYPE));
    if ((a_local == NULL) || (b_local == NULL) || (c_local == NULL)) {
      snrt_printf("ERROR: Memory allocation failed!\n");
    }

    dm_memcpy_async(a_local, a, width * height * sizeof(DTYPE));
    dm_memcpy_async(b_local, b, width * height * sizeof(DTYPE));
    dm_wait();

    for (uint32_t i = 0; i < width; i++) {
      for (uint32_t j = 0; j < height; j++) {
        DTYPE sum = 0;
        for (uint32_t k = 0; k < width; k++)
          sum = sum + a_local[i * width + k] * b_local[k * width + j];
        c_local[i * width + j] = sum;
      }
    }

    dm_memcpy_async(c, c_local, width * height * sizeof(DTYPE));
    dm_wait();

  // TODO: This is a hacky fix to free the allocated memory becsue we don't support l1free() yet
#ifdef __HERO_DEV
  snrt_l1alloc_reset(a_local);
#endif

    // snrt_l1free(a_local);
    // snrt_l1free(b_local);
    // snrt_l1free(c_local);
  }
  time = bench_stop();
  error = compare_matrices(c, d, width, height);
  printf("csv : %i %f\n", error, time);

  memset(c, 0, (size_t)(sizeof(DTYPE) * width * height));


  printf("\n");
  bench_start("HERO Device: Parallel, copy-based, DMA");
#pragma omp target device(HERODEV_MEMCPY) map(to                                                   \
                                              : a [0:width * height], b [0:width * height])        \
    map(from                                                                                       \
        : c [0:width * height])
  {
    __device DTYPE *a_local =
        (__device DTYPE *)snrt_l1alloc(width * height * sizeof(DTYPE));
    __device DTYPE *b_local =
        (__device DTYPE *)snrt_l1alloc(width * height * sizeof(DTYPE));
    __device DTYPE *c_local =
        (__device DTYPE *)snrt_l1alloc(width * height * sizeof(DTYPE));
    if ((a_local == NULL) || (b_local == NULL) || (c_local == NULL)) {
      printf("ERROR: Memory allocation failed!\n");
    }

    dm_memcpy_async(a_local, a, width * height * sizeof(DTYPE));
    dm_memcpy_async(b_local, b, width * height * sizeof(DTYPE));
    dm_wait();

#pragma omp parallel for collapse(2) firstprivate(a_local, b_local, c_local)
    for (uint32_t i = 0; i < width; i++) {
      for (uint32_t j = 0; j < height; j++) {
        DTYPE sum = 0;
        for (uint32_t k = 0; k < width; k++)
          sum = sum + a_local[i * width + k] * b_local[k * width + j];
        c_local[i * width + j] = sum;
      }
    }

    dm_memcpy_async(c, c_local, width * height * sizeof(DTYPE));
    dm_wait();
    
// TODO: This is a hacky fix to free the allocated memory becsue we don't support l1free() yet  
#ifdef __HERO_DEV
  snrt_l1alloc_reset(a_local);
#endif

    // snrt_l1free(a_local);
    // snrt_l1free(b_local);
    // snrt_l1free(c_local);
  }
  time = bench_stop();
  error = compare_matrices(c, d, width, height);
  printf("csv : %i %f\n", error, time);

  memset(c, 0, (size_t)(sizeof(DTYPE) * width * height));

  //   // The following code is commented out, as it requires SVM support. This is
  //   // intended to be added in version v0.2 and does not yet function correctly.
  //   if (0 /* Will never be true */) {
  // /*
  //  * Make sure PULP is ready - speeds up the first target
  //  *
  //  * Actually, we should not use both devices at the same time as it is not safe. OpenMP will
  //  load
  //  * or boot both of them. But in reality only one accelerator is there.
  //  */
  // #pragma omp target device(BIGPULP_SVM) map(to : tmp_1) map(from : tmp_2)
  //     { tmp_2 = tmp_1; }
  //     tmp_1 = tmp_2;

  //     bench_start("HERO Device: Parallel, SVM, DMA");
  // #pragma omp target device(BIGPULP_SVM) \
//     map(to \
//         : a [0:width * height], b [0:width * height], width, height) map(from \
//                                                                          : c [0:width *
  //                                                                          height])
  //     {
  //       uint32_t width_local = width;
  //       uint32_t height_local = height;

  //       __device uint32_t *a_local =
  //           (__device uint32_t *)hero_l1malloc(width_local * height_local * sizeof(uint32_t));
  //       __device uint32_t *b_local =
  //           (__device uint32_t *)hero_l1malloc(width_local * height_local * sizeof(uint32_t));
  //       __device uint32_t *c_local =
  //           (__device uint32_t *)hero_l1malloc(width_local * height_local * sizeof(uint32_t));
  //       if ((a_local == NULL) || (b_local == NULL) || (c_local == NULL)) {
  //         printf("ERROR: Memory allocation failed!\n");
  //       }

  //       hero_dma_job_t dma0 =
  //           hero_memcpy_host2dev_async(a_local, a, width_local * height_local *
  //           sizeof(uint32_t));
  //       hero_dma_job_t dma1 =
  //           hero_memcpy_host2dev_async(b_local, b, width_local * height_local *
  //           sizeof(uint32_t));
  //       hero_dma_wait(dma0);
  //       hero_dma_wait(dma1);

  // #pragma omp parallel for collapse(2)                                                               \
//     firstprivate(a_local, b_local, c_local, width_local, height_local)
  //       for (uint32_t i = 0; i < width_local; i++) {
  //         for (uint32_t j = 0; j < height_local; j++) {
  //           uint32_t sum = 0;
  //           for (uint32_t k = 0; k < width_local; k++)
  //             sum = sum + a_local[i * width_local + k] * b_local[k * width_local + j];
  //           c_local[i * width_local + j] = sum;
  //         }
  //       }

  //       hero_memcpy_dev2host(c, c_local, width_local * height_local * sizeof(uint32_t));

  //       hero_l1free(a_local);
  //       hero_l1free(b_local);
  //       hero_l1free(c_local);
  //     } // target
  //     bench_stop();
  //     compare_matrices(c, d, width, height);
  //     memset(c, 0, (size_t)(width * height));
  //   }

exit:

  // free memory
  free(a);
  free(b);
  free(c);
  free(d);

  return 0;
}
