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

void compare_matrices(uint32_t* a, uint32_t* b, unsigned width, unsigned height)
{
  for (unsigned i=0; i<width; i++) {
    for (unsigned j=0; j<height; j++) {
      if(a[i*width+j] != b[i*width+j] ) {
        printf("ERROR: Result mismatch in Row %u, Column %u!\n", j, i);
        exit(-1);
      }
    }
  }
}

#pragma omp declare target

int double_buf_mm(uint32_t * __restrict__ a, uint32_t * __restrict__ b, uint32_t * __restrict__ c, uint32_t width, uint32_t height, uint32_t stripe_height)
{
  const unsigned width_local         = hero_tryread((unsigned int *)&width);
  const unsigned height_local        = hero_tryread((unsigned int *)&height);
  const unsigned stripe_height_local = hero_tryread((unsigned int *)&stripe_height);

  const unsigned n_stripes = height_local / stripe_height_local;
  const unsigned stripe_size_b = width_local * stripe_height_local * sizeof(uint32_t);

  uint32_t * a_ptrs[2];
  uint32_t * b_ptrs[2];
  uint32_t * c_ptrs[2];

  hero_dma_job_t a_dma[2];
  hero_dma_job_t b_dma[2];
  hero_dma_job_t c_dma[2];

  unsigned a_idx = 0;
  unsigned c_idx = 0;
  unsigned b_idx = 0;

  // allocate the buffers
  a_ptrs[0] = (uint32_t *)hero_l1malloc(stripe_size_b);
  a_ptrs[1] = (uint32_t *)hero_l1malloc(stripe_size_b);
  b_ptrs[0] = (uint32_t *)hero_l1malloc(stripe_size_b);
  b_ptrs[1] = (uint32_t *)hero_l1malloc(stripe_size_b);
  c_ptrs[0] = (uint32_t *)hero_l1malloc(stripe_size_b);
  c_ptrs[1] = (uint32_t *)hero_l1malloc(stripe_size_b);

  if ( (a_ptrs[0] == NULL) || (a_ptrs[1] == NULL) ||
       (b_ptrs[0] == NULL) || (b_ptrs[1] == NULL) ||
       (c_ptrs[0] == NULL) || (c_ptrs[1] == NULL) ) {
    printf("ERROR: Memory allocation failed!\n");
    return -ENOMEM;
  }

  #pragma omp parallel \
    firstprivate(a_ptrs, b_ptrs, c_ptrs, width_local, height_local, stripe_height_local) \
    firstprivate(a_dma, b_dma, c_dma) \
    shared(a_idx, b_idx, c_idx) \
    shared(a, b, c)
  {
    const int thread_id = omp_get_thread_num();

    // get the first stripes
    if (thread_id == 0) {
      a_dma[a_idx] = hero_dma_memcpy_async((void *)a_ptrs[a_idx], (void *)a, stripe_size_b);
    }
    else if (thread_id == 1) {
      b_dma[b_idx] = hero_dma_memcpy_async((void *)b_ptrs[b_idx], (void *)b, stripe_size_b);
    }

    // horizontal a and c stripes
    for (unsigned s=0; s<n_stripes; s++) {

      if (thread_id == 0) {
        // swap buffer
        a_idx = a_idx ? 0 : 1;

        if (s < n_stripes-1) {
          // determine next DMA XFER
          const unsigned ext_addr = (unsigned)a + (s+1)*stripe_size_b;

          // set up DMA XFER
          a_dma[a_idx] = hero_dma_memcpy_async((void *)a_ptrs[a_idx], (void *)ext_addr, stripe_size_b);
        }

        // wait for previous DMA XFER
        hero_dma_wait(a_dma[!a_idx]);
      }
      else if ( (thread_id == 2) && (s > 0) ) {
        // swap buffer
        c_idx = c_idx ? 0 : 1;

        // determine next DMA XFER
        const unsigned ext_addr = (unsigned)c + (s-1)*stripe_size_b;

        // set up DMA XFER
        c_dma[!c_idx] = hero_dma_memcpy_async((void *)ext_addr, (void *)c_ptrs[!c_idx], stripe_size_b);

        // wait for previous DMA XFER
        if (s > 1)
          hero_dma_wait(c_dma[c_idx]);
      }

      // vertical b stripes
      for (unsigned t=0; t<n_stripes; t++) {

        if ( (thread_id == 1) ) {
          // swap buffer
          b_idx = b_idx ? 0 : 1;

          if (t < n_stripes-1) {
            // determine next DMA XFER
            const unsigned ext_addr = (unsigned)b + (t+1)*stripe_size_b;

            // set up DMA XFER
            b_dma[b_idx] = hero_dma_memcpy_async((void *)b_ptrs[b_idx], (void *)ext_addr, stripe_size_b);
          }
          else if (s < n_stripes-1) {
            // determine next DMA XFER
            const unsigned ext_addr = (unsigned)b;

            // set up DMA XFER
            b_dma[b_idx] = hero_dma_memcpy_async((void *)b_ptrs[b_idx], (void *)ext_addr, stripe_size_b);
          }

          // wait for previous DMA XFER
          hero_dma_wait(b_dma[!b_idx]);
        }

        #pragma omp barrier

        #pragma omp for collapse(2)

        // horizontal a and c rows
        for (unsigned i=0; i<stripe_height_local; i++) {

          // vertical b columns
          for (unsigned j=0; j<stripe_height_local; j++) {

            uint32_t sum = 0;
            for (unsigned k=0; k<width_local; k++) {
              sum = sum + a_ptrs[!a_idx][i*width_local+k] * b_ptrs[!b_idx][j*width_local+k];
            } // k < width_local
            c_ptrs[c_idx][i*width_local+t*stripe_height_local+j] = sum;
          } // j < stripe_height_local
        } // i < stripe_height_local
      } // t < n_stripes

    } // n_stripes

    // copy out last c stripe
    if (thread_id == 2)
      hero_dma_memcpy((void *)((unsigned)c+(n_stripes-1)*stripe_size_b), (void *)c_ptrs[c_idx], stripe_size_b);

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

  unsigned height  = 128;
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
  unsigned stripe_height = height/2;
  while (stripe_height*height*sizeof(uint32_t) >= 32*1024) {
    stripe_height = stripe_height/2;
  }
  const unsigned n_stripes = height/stripe_height;
  height = n_stripes * stripe_height;

  unsigned width = height;

  // Allocate memory
  uint32_t * a = (uint32_t *)malloc(sizeof(uint32_t)*width*height);
  uint32_t * b = (uint32_t *)malloc(sizeof(uint32_t)*width*height);
  uint32_t * c = (uint32_t *)malloc(sizeof(uint32_t)*width*height);
  uint32_t * d = (uint32_t *)malloc(sizeof(uint32_t)*width*height);
  if ( (a == NULL) || (b == NULL) || (c == NULL) || (d == NULL) ) {
    printf("ERROR: malloc() failed!\n");
    return -ENOMEM;
  }
  printf("width = %u, height = %u, stripe_height = %u, a @ %p, b @ %p, c @ %p\n",
    width, height, stripe_height, a, b, c);
  printf("Total data size = %.2f KiB\n", 3*(float)(width*height*sizeof(uint32_t))/1024);

  // Init matrices
  for (unsigned i=0; i<width; i++) {
    for (unsigned j=0; j<height; j++) {
      a[i*width+j] = i*width+j;
      b[i*width+j] = i == j ? 2 : 0;
    }
  }
  memset((void *)c, 0, (size_t)(width*height));
  memset((void *)d, 0, (size_t)(width*height));

  /*
   * Execute on host
   */

  bench_start("Host");
  #pragma omp parallel firstprivate(a, b, d, width, height) num_threads(1)
  {
    #pragma omp for collapse(2)
    for (unsigned i=0; i<width; i++) {
      for (unsigned j=0; j<height; j++) {
        uint32_t sum = 0;
        for (unsigned k=0; k<width; k++)
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
  unsigned tmp_1 = 1;
  unsigned tmp_2 = 2;
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
  compare_matrices(c, d, width, height);
  memset((void *)c, 0, (size_t)(width*height));

  /*
   * Make sure PULP is ready - speeds up the first target
   *
   * Actually, we should not use both devices at the same time as it is not safe. OpenMP will load
   * or boot both of them. But in reality only one accelerator is there.
   */
  #pragma omp target device(0) map(to: tmp_1) map(from: tmp_2)
  {
    hero_trywrite(&tmp_2, hero_tryread(&tmp_1));
  }
  tmp_1 = tmp_2;

  bench_start("PULP Execution: Parallel, double-buffered DMA, SVM");
  #pragma omp target device(0) map(to: a[0:width*height], b[0:width*height], width, height, stripe_height) \
    map(from: c[0:width*height])
  double_buf_mm(a, b, c, width, height, stripe_height);
  bench_stop();
  compare_matrices(c, d, width, height);
  memset((void *)c, 0, (size_t)(width*height));

  // free memory
  free(a);
  free(b);
  free(c);
  free(d);

  return 0;
}
