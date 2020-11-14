/* POLYBENCH/GPU-OPENACC
 *
 * This file is a part of the Polybench/GPU-OpenACC suite
 *
 * Contact:
 * William Killian <killian@udel.edu>
 *
 * Copyright 2013, The University of Delaware
 */
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <math.h>

/* Include polybench common header. */
#include <polybench.h>

/* Include hero runtime lib. */
#include <hero-target.h>

/* Include benchmark-specific header. */
/* Default data type is double, default size is 4000. */
#include "atax.h"

/* Array initialization. */
static
void init_array (int nx, int ny,
                 DATA_TYPE POLYBENCH_2D(A,NX,NY,nx,ny),
                 DATA_TYPE POLYBENCH_1D(x,NY,ny))
{
  int i, j;

  for (i = 0; i < ny; i++)
      x[i] = i * M_PI;
  for (i = 0; i < nx; i++)
    for (j = 0; j < ny; j++)
      A[i][j] = ((DATA_TYPE) i*(j+1)) / nx;
}


/* DCE code. Must scan the entire live-out data.
   Can be used also to check the correctness of the output. */
static
void print_array(int nx,
                 DATA_TYPE POLYBENCH_1D(y,NX,nx))

{
  int i;

  for (i = 0; i < nx; i++) {
    printf (DATA_PRINTF_MODIFIER, y[i]);
    if (i % 20 == 0) printf ("\n");
  }
  printf ("\n");
}

/* Main computational kernel with DMA. The whole function will be
   timed, including the call and return. */
static
void kernel_atax_dma(int nx, int ny,
                     DATA_TYPE POLYBENCH_2D(A,NX,NY,nx,ny),
                     DATA_TYPE POLYBENCH_1D(x,NY,ny),
                     DATA_TYPE POLYBENCH_1D(y,NY,ny),
                     DATA_TYPE POLYBENCH_1D(tmp,NX,nx))
{
  #pragma omp target data \
    map(to: A[0:NX][0:NY], x[0:NY]) \
    map(alloc: tmp[0:NX]) \
    map(from: y[0:NY])
  {
    #pragma omp target
    {
      int rows_per_chunk = NX; // (SPM_SIZE - NY) / (NY + 1);

      __device DATA_TYPE* x_spm = (__device DATA_TYPE *) hero_l1malloc(NY * sizeof(DATA_TYPE));
      __device DATA_TYPE* tmp_spm = (__device DATA_TYPE *) hero_l1malloc(rows_per_chunk * sizeof(DATA_TYPE));
      __device DATA_TYPE* A_spm = (__device DATA_TYPE *) hero_l1malloc(NY * rows_per_chunk * sizeof(DATA_TYPE));

      hero_memcpy_host2dev(x_spm, ((__host DATA_TYPE*) x), NY * sizeof(DATA_TYPE));

      int row = 0;
      while (row < NX) {
        int chunk_rows = (row + rows_per_chunk < NX) ? rows_per_chunk : (NX - row);
        hero_memcpy_host2dev(A_spm, ((__host DATA_TYPE*) A) + row*NY, chunk_rows*NY * sizeof(DATA_TYPE));

        #pragma omp parallel for num_threads(NUM_THREADS)
        for (int i = 0; i < chunk_rows; i++) {
          tmp_spm[i] = 0;
          for (int j = 0; j < NY; j++) {
            tmp_spm[i] = tmp_spm[i] + A_spm[i*NY+j] * x_spm[j];
          }
        }

        hero_memcpy_dev2host(((__host DATA_TYPE*) tmp) + row, tmp_spm, chunk_rows * sizeof(DATA_TYPE));
        row += rows_per_chunk;
      }

      hero_l1free(A_spm);
      hero_l1free(tmp_spm);
      hero_l1free(x_spm);
    }

    #pragma omp target
    {
      int rows_per_chunk = NX; // (SPM_SIZE - NY) / (NY + 1);

      __device DATA_TYPE* y_spm = (__device DATA_TYPE *) hero_l1malloc(NY * sizeof(DATA_TYPE));
      __device DATA_TYPE* tmp_spm = (__device DATA_TYPE *) hero_l1malloc(rows_per_chunk * sizeof(DATA_TYPE));
      __device DATA_TYPE* A_spm = (__device DATA_TYPE *) hero_l1malloc(NY * rows_per_chunk * sizeof(DATA_TYPE));

      int row = 0;
      while (row < NX) {
        int chunk_rows = (row + rows_per_chunk < NX) ? rows_per_chunk : (NX - row);
        hero_dma_job_t job_A = hero_memcpy_host2dev_async(A_spm, ((__host DATA_TYPE*) A) + row*NY, chunk_rows*NY * sizeof(DATA_TYPE));
        hero_dma_job_t job_tmp = hero_memcpy_host2dev_async(tmp_spm, ((__host DATA_TYPE*) tmp) + row, chunk_rows * sizeof(DATA_TYPE));
        hero_dma_wait(job_A);
        hero_dma_wait(job_tmp);

        #pragma omp parallel for num_threads(NUM_THREADS) firstprivate(chunk_rows)
        for (int i = 0; i < NY; i++) {
          y_spm[i] = 0;
          for (int j = 0; j < chunk_rows; j++)
            y_spm[i] = y_spm[i] + A_spm[j*NY+i] * tmp_spm[j];
        }
        row += rows_per_chunk;
      }

      hero_memcpy_dev2host((__host DATA_TYPE*) y, y_spm, NY * sizeof(DATA_TYPE));

      hero_l1free(A_spm);
      hero_l1free(tmp_spm);
      hero_l1free(y_spm);
    }
  }
}

/* Main computational kernel. The whole function will be timed,
   including the call and return. */
static
void kernel_atax(int nx, int ny,
                 DATA_TYPE POLYBENCH_2D(A,NX,NY,nx,ny),
                 DATA_TYPE POLYBENCH_1D(x,NY,ny),
                 DATA_TYPE POLYBENCH_1D(y,NY,ny),
                 DATA_TYPE POLYBENCH_1D(tmp,NX,nx))
{
  #pragma omp target data \
    map(to: A[0:NX][0:NY], x[0:NY]) \
    map(alloc: tmp[0:NX]) \
    map(from: y[0:NY])
  {
    /* tmp := A*x */
    #pragma omp target
    {
      #pragma omp parallel for num_threads(NUM_THREADS)
      for (int i = 0; i < NX; i++) {
        tmp[i] = 0;
        for (int j = 0; j < NY; j++)
          tmp[i] = tmp[i] + A[i][j] * x[j];
      }
    }
    /* y := t(A)*tmp */
    #pragma omp target
    {
      #pragma omp parallel for num_threads(NUM_THREADS)
      for (int i = 0; i < NY; i++) {
        y[i] = 0;
        for (int j = 0; j < NX; j++)
          y[i] = y[i] + A[j][i] * tmp[j];
      }
    }
  }
}


int main(int argc, char** argv)
{
  omp_set_default_device(BIGPULP_MEMCPY);

  /* Retrieve problem size. */
  int nx = NX;
  int ny = NY;

  /* Variable declaration/allocation. */
  POLYBENCH_2D_ARRAY_DECL(A, DATA_TYPE, NX, NY, nx, ny);
  POLYBENCH_1D_ARRAY_DECL(x, DATA_TYPE, NY, ny);
  POLYBENCH_1D_ARRAY_DECL(y, DATA_TYPE, NY, ny);
  POLYBENCH_1D_ARRAY_DECL(tmp, DATA_TYPE, NX, nx);

  /* Initialize array(s). */
  init_array (nx, ny, POLYBENCH_ARRAY(A), POLYBENCH_ARRAY(x));

  /* Start timer. */
  polybench_start_instruments;

  /* Run kernel. */
#ifdef POLYBENCH_DMA
  kernel_atax_dma (nx, ny,
                   POLYBENCH_ARRAY(A),
                   POLYBENCH_ARRAY(x),
                   POLYBENCH_ARRAY(y),
                   POLYBENCH_ARRAY(tmp));
#else
  kernel_atax (nx, ny,
               POLYBENCH_ARRAY(A),
               POLYBENCH_ARRAY(x),
               POLYBENCH_ARRAY(y),
               POLYBENCH_ARRAY(tmp));
#endif


  /* Stop and print timer. */
  polybench_stop_instruments;
  polybench_print_instruments;

  /* Prevent dead-code elimination. All live-out data must be printed
     by the function call in argument. */
  polybench_prevent_dce(print_array(nx, POLYBENCH_ARRAY(y)));

  /* Be clean. */
  POLYBENCH_FREE_ARRAY(A);
  POLYBENCH_FREE_ARRAY(x);
  POLYBENCH_FREE_ARRAY(y);
  POLYBENCH_FREE_ARRAY(tmp);

  return 0;
}
