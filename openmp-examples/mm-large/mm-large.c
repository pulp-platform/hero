/*
 * HERO Matrix-Matrix Multiplication with Double Buffering Example Application
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
#include <string.h>
#include <stdint.h>
#include <errno.h>        // for error codes
#include "bench.h"
#include <hero-target.h>

void compare_matrices(uint32_t* a, uint32_t* b, uint32_t width, uint32_t height)
{
  for (uint32_t i=0; i<width; i++) {
    for (uint32_t j=0; j<height; j++) {
      if(a[i*width+j] != b[i*width+j] ) {
        printf("ERROR: Result mismatch in Row %u, Column %u!\n", j, i);
        exit(-1);
      }
    }
  }
}

#pragma omp declare target

//#define TIME_DMA_AND_COMP // measure and print cycles spent on DMA transfers and computations

int double_buf_mm(__host uint32_t * __restrict__ a,
                  __host uint32_t * __restrict__ b,
                  __host uint32_t * __restrict__ c,
                  uint32_t width, uint32_t height, uint32_t stripe_height)
{
  const uint32_t n_stripes = height / stripe_height;
  const uint32_t stripe_size_b = width * stripe_height * sizeof(uint32_t);

  __device uint32_t * a_ptrs[2];
  __device uint32_t * b_ptrs[2];
  __device uint32_t * c_ptrs[2];

  hero_dma_job_t a_dma[2];
  hero_dma_job_t b_dma[2];
  hero_dma_job_t c_dma[2];

  uint32_t a_idx = 0;
  uint32_t c_idx = 0;
  uint32_t b_idx = 0;

  // allocate the buffers
  a_ptrs[0] = (__device uint32_t *)hero_l1malloc(stripe_size_b);
  a_ptrs[1] = (__device uint32_t *)hero_l1malloc(stripe_size_b);
  b_ptrs[0] = (__device uint32_t *)hero_l1malloc(stripe_size_b);
  b_ptrs[1] = (__device uint32_t *)hero_l1malloc(stripe_size_b);
  c_ptrs[0] = (__device uint32_t *)hero_l1malloc(stripe_size_b);
  c_ptrs[1] = (__device uint32_t *)hero_l1malloc(stripe_size_b);

  if ( (a_ptrs[0] == NULL) || (a_ptrs[1] == NULL) ||
       (b_ptrs[0] == NULL) || (b_ptrs[1] == NULL) ||
       (c_ptrs[0] == NULL) || (c_ptrs[1] == NULL) ) {
    printf("ERROR: Memory allocation failed!\n");
    return -ENOMEM;
  }

  #pragma omp parallel \
    firstprivate(a_ptrs, b_ptrs, c_ptrs, width, height, stripe_height) \
    firstprivate(a_dma, b_dma, c_dma) \
    shared(a_idx, b_idx, c_idx) \
    shared(a, b, c) num_threads(8)
  {
    const int thread_id = omp_get_thread_num();

#ifdef TIME_DMA_AND_COMP
    unsigned comp_cycles = 0;
    unsigned dma_setup_cycles = 0;
    unsigned dma_wait_cycles = 0;
#endif

    // get the first stripes
    if (thread_id == 0) {
#ifdef TIME_DMA_AND_COMP
      const unsigned cycles_prev = hero_get_clk_counter();
#endif
      a_dma[a_idx] = hero_memcpy_host2dev_async(a_ptrs[a_idx], a, stripe_size_b);
#ifdef TIME_DMA_AND_COMP
      dma_setup_cycles += hero_get_clk_counter() - cycles_prev;
#endif
    }
    else if (thread_id == 1) {
#ifdef TIME_DMA_AND_COMP
      const unsigned cycles_prev = hero_get_clk_counter();
#endif
      b_dma[b_idx] = hero_memcpy_host2dev_async(b_ptrs[b_idx], b, stripe_size_b);
#ifdef TIME_DMA_AND_COMP
      dma_setup_cycles += hero_get_clk_counter() - cycles_prev;
#endif
    }

    // horizontal a and c stripes
    for (uint32_t s=0; s<n_stripes; s++) {

      if (thread_id == 0) {
        // swap buffer
        a_idx = a_idx ? 0 : 1;

        if (s < n_stripes-1) {
          // determine next DMA XFER
          const uint64_t ext_addr = (uint64_t)a + (s+1)*stripe_size_b;

          // set up DMA XFER
#ifdef TIME_DMA_AND_COMP
          const unsigned cycles_prev = hero_get_clk_counter();
#endif
          a_dma[a_idx] = hero_memcpy_host2dev_async(a_ptrs[a_idx], (__host void *)ext_addr, stripe_size_b);
#ifdef TIME_DMA_AND_COMP
          dma_setup_cycles += hero_get_clk_counter() - cycles_prev;
#endif
        }

        // wait for previous DMA XFER
#ifdef TIME_DMA_AND_COMP
        const unsigned cycles_prev = hero_get_clk_counter();
#endif
        hero_dma_wait(a_dma[!a_idx]);
#ifdef TIME_DMA_AND_COMP
        dma_wait_cycles += hero_get_clk_counter() - cycles_prev;
#endif
      }
      else if ( (thread_id == 2) && (s > 0) ) {
        // swap buffer
        c_idx = c_idx ? 0 : 1;

        // determine next DMA XFER
        const uint64_t ext_addr = (uint64_t)c + (s-1)*stripe_size_b;

        // set up DMA XFER
#ifdef TIME_DMA_AND_COMP
        const unsigned cycles_prev = hero_get_clk_counter();
#endif
        c_dma[!c_idx] = hero_memcpy_dev2host_async((__host void *)ext_addr, c_ptrs[!c_idx], stripe_size_b);
#ifdef TIME_DMA_AND_COMP
        dma_setup_cycles += hero_get_clk_counter() - cycles_prev;
#endif

        // wait for previous DMA XFER
        if (s > 1)
          hero_dma_wait(c_dma[c_idx]);
      }

      // vertical b stripes
      for (uint32_t t=0; t<n_stripes; t++) {

        if ( (thread_id == 1) ) {
          // swap buffer
          b_idx = b_idx ? 0 : 1;

          if (t < n_stripes-1) {
            // determine next DMA XFER
            const uint64_t ext_addr = (uint64_t)b + (t+1)*stripe_size_b;

            // set up DMA XFER
#ifdef TIME_DMA_AND_COMP
            const unsigned cycles_prev = hero_get_clk_counter();
#endif
            b_dma[b_idx] = hero_memcpy_host2dev_async(b_ptrs[b_idx], (__host void *)ext_addr, stripe_size_b);
#ifdef TIME_DMA_AND_COMP
            dma_setup_cycles += hero_get_clk_counter() - cycles_prev;
#endif
          }
          else if (s < n_stripes-1) {
            // determine next DMA XFER
            const uint64_t ext_addr = (uint64_t)b;

            // set up DMA XFER
#ifdef TIME_DMA_AND_COMP
            const unsigned cycles_prev = hero_get_clk_counter();
#endif
            b_dma[b_idx] = hero_memcpy_host2dev_async(b_ptrs[b_idx], (__host void *)ext_addr, stripe_size_b);
#ifdef TIME_DMA_AND_COMP
            dma_setup_cycles += hero_get_clk_counter() - cycles_prev;
#endif
          }

          // wait for previous DMA XFER
#ifdef TIME_DMA_AND_COMP
          const unsigned cycles_prev = hero_get_clk_counter();
#endif
          hero_dma_wait(b_dma[!b_idx]);
#ifdef TIME_DMA_AND_COMP
          dma_wait_cycles += hero_get_clk_counter() - cycles_prev;
#endif
        }

        #pragma omp barrier

#ifdef TIME_DMA_AND_COMP
        const unsigned cycles_prev = hero_get_clk_counter();
#endif

        #pragma omp for collapse(2)

        // horizontal a and c rows
        for (uint32_t i=0; i<stripe_height; i++) {

          // vertical b columns
          for (uint32_t j=0; j<stripe_height; j++) {

            uint32_t sum = 0;
            for (uint32_t k=0; k<width; k++) {
              sum = sum + a_ptrs[!a_idx][i*width+k] * b_ptrs[!b_idx][j*width+k];
            } // k < width
            c_ptrs[c_idx][i*width+t*stripe_height+j] = sum;
          } // j < stripe_height
        } // i < stripe_height

#ifdef TIME_DMA_AND_COMP
        comp_cycles += hero_get_clk_counter() - cycles_prev;
#endif

      } // t < n_stripes

    } // n_stripes

    // wait for second to last c stripe
    if (thread_id == 2) {
#ifdef TIME_DMA_AND_COMP
      const unsigned cycles_prev = hero_get_clk_counter();
#endif
      hero_dma_wait(c_dma[!c_idx]);
#ifdef TIME_DMA_AND_COMP
      dma_wait_cycles += hero_get_clk_counter() - cycles_prev;
#endif
    }

    // copy out last c stripe
    if (thread_id == 2) {
#ifdef TIME_DMA_AND_COMP
      const unsigned cycles_prev = hero_get_clk_counter();
#endif
      hero_memcpy_dev2host((__host void *)((uint64_t)c+(n_stripes-1)*stripe_size_b), c_ptrs[c_idx], stripe_size_b);
#ifdef TIME_DMA_AND_COMP
      dma_setup_cycles += hero_get_clk_counter() - cycles_prev;
#endif
    }

#ifdef TIME_DMA_AND_COMP
    printf("Computation cycles: %d %10d\n", comp_cycles);
    printf("DMA setup cycles:   %d %10d\n", dma_setup_cycles);
    printf("DMA wait cycles:    %d %10d\n", dma_wait_cycles);
#endif

  } // parallel

  hero_l1free(a_ptrs[0]);
  hero_l1free(a_ptrs[1]);
  hero_l1free(b_ptrs[0]);
  hero_l1free(b_ptrs[1]);
  hero_l1free(c_ptrs[0]);
  hero_l1free(c_ptrs[1]);

  return 0;
}

#pragma omp end declare target

int main(int argc, char *argv[])
{
  printf("HERO matrix multiplication started.\n");

  uint32_t height  = 256;
  if( argc > 1 ) {
    height  = strtoul(argv[1], NULL, 0);
  }
  if (height > 512) {
    height = 512;
  }
  if (height < 32) {
    height = 32;
  }

  // Take a height such that:
  // - it is divisible by stripe_height,
  // - the stripe size can actually be allocated in the L1 memory
  uint32_t stripe_height = height/2;
  while (stripe_height*height*sizeof(uint32_t) >= 32*1024) {
    stripe_height = stripe_height/2;
  }
  const uint32_t n_stripes = height/stripe_height;
  height = n_stripes * stripe_height;

  uint32_t width = height;

  // Allocate memory
  __host uint32_t * a = (__host uint32_t *)malloc(sizeof(uint32_t)*width*height);
  __host uint32_t * b = (__host uint32_t *)malloc(sizeof(uint32_t)*width*height);
  __host uint32_t * c = (__host uint32_t *)malloc(sizeof(uint32_t)*width*height);
  __host uint32_t * d = (__host uint32_t *)malloc(sizeof(uint32_t)*width*height);
  if ( (a == NULL) || (b == NULL) || (c == NULL) || (d == NULL) ) {
    printf("ERROR: malloc() failed!\n");
    return -ENOMEM;
  }
  printf("width = %u, height = %u, stripe_height = %u, a @ %p, b @ %p, c @ %p\n",
    width, height, stripe_height, a, b, c);
  printf("Total data size = %.2f KiB\n", 3*(float)(width*height*sizeof(uint32_t))/1024);

  // Init matrices
  for (uint32_t i=0; i<width; i++) {
    for (uint32_t j=0; j<height; j++) {
      a[i*width+j] = i*width+j;
      b[i*width+j] = i == j ? 2 : 0;
    }
  }
  memset(c, 0, (size_t)(width*height));
  memset(d, 0, (size_t)(width*height));

  /*
   * Execute on host
   */

  bench_start("Host");
  #pragma omp parallel firstprivate(a, b, d, width, height) num_threads(1)
  {
    #pragma omp for collapse(2)
    for (uint32_t i=0; i<width; i++) {
      for (uint32_t j=0; j<height; j++) {
        uint32_t sum = 0;
        for (uint32_t k=0; k<width; k++)
          sum = sum + a[i*width+k] * b[j*width+k];
        d[i*width+j] = sum;
      }
    }
  }
  bench_stop();

  /*
   * Excute on PULP
   */

  /*
   * Make sure PULP is ready - speeds up the first target
   *
   * Actually, we should not use both devices at the same time as it is not safe. OpenMP will load
   * or boot both of them. But in reality only one accelerator is there.
   */
  uint32_t tmp_1 = 1;
  uint32_t tmp_2 = 2;
  #pragma omp target device(1) map(to: tmp_1) map(from: tmp_2)
  {
    tmp_2 = tmp_1;
  }
  tmp_1 = tmp_2;

  bench_start("PULP: Execution: Parallel, double-buffered DMA, copy-based");

  #pragma omp target device(1) map(to: a[0:width*height], b[0:width*height], width, height, stripe_height) \
    map(from: c[0:width*height])
  double_buf_mm(a, b, c, width, height, stripe_height);
  bench_stop();
#ifdef TIME_DMA_AND_COMP
  printf("Warning: The time measured on the host is meaningless ");
  printf("because it includes `printf`s on the device.  ");
  printf("Recompile the benchmark without `TIME_DMA_AND_COMP` ");
  printf("to get meaningful timing measurements on the host.\n");
#endif
  compare_matrices(c, d, width, height);
  memset(c, 0, (size_t)(width*height));

  // The following code is commented out, as it requires SVM support. This is
  // intended to be added in version v0.2 and does not yet function correctly.
  if (0 /* Will never be true */) {
    /*
     * Make sure PULP is ready - speeds up the first target
     *
     * Actually, we should not use both devices at the same time as it is not safe. OpenMP will load
     * or boot both of them. But in reality only one accelerator is there.
     */
    #pragma omp target device(0) map(to: tmp_1) map(from: tmp_2)
    {
      tmp_2 = tmp_1;
    }
    tmp_1 = tmp_2;

    bench_start("PULP Execution: Parallel, double-buffered DMA, SVM");
    #pragma omp target device(0) map(to: a[0:width*height], b[0:width*height], width, height, stripe_height) \
      map(from: c[0:width*height])
    double_buf_mm(a, b, c, width, height, stripe_height);
    bench_stop();
    compare_matrices(c, d, width, height);
    memset(c, 0, (size_t)(width*height));
  }

  // free memory
  free(a);
  free(b);
  free(c);
  free(d);

  return 0;
}
