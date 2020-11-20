/* POLYBENCH/GPU-OPENMP
 *
 * This file is a part of the Polybench/GPU-OpenMP suite
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
#include "bicg.h"


/* Array initialization. */
static
void init_array (int nx, int ny,
		 DATA_TYPE POLYBENCH_2D(A,NX,NY,nx,ny),
		 DATA_TYPE POLYBENCH_1D(r,NX,nx),
		 DATA_TYPE POLYBENCH_1D(p,NY,ny))
{
  int i, j;

  for (i = 0; i < ny; i++)
    p[i] = i * M_PI;
  for (i = 0; i < nx; i++) {
    r[i] = i * M_PI;
    for (j = 0; j < ny; j++)
      A[i][j] = ((DATA_TYPE) i*(j+1))/nx;
  }
}


/* DCE code. Must scan the entire live-out data.
   Can be used also to check the correctness of the output. */
static
void print_array(int nx, int ny,
		 DATA_TYPE POLYBENCH_1D(s,NY,ny),
		 DATA_TYPE POLYBENCH_1D(q,NX,nx))

{
  int i;

  for (i = 0; i < ny; i++) {
    printf (DATA_PRINTF_MODIFIER, s[i]);
    if (i % 20 == 0) printf ("\n");
  }
  for (i = 0; i < nx; i++) {
    printf (DATA_PRINTF_MODIFIER, q[i]);
    if (i % 20 == 0) printf ("\n");
  }
  printf ("\n");
}


/* Main computational kernel with DMA. The whole function will be
   timed, including the call and return. */
static
void kernel_bicg_dma(int nx, int ny,
                     DATA_TYPE POLYBENCH_2D(A,NX,NY,nx,ny),
                     DATA_TYPE POLYBENCH_1D(s,NY,ny),
                     DATA_TYPE POLYBENCH_1D(q,NX,nx),
                     DATA_TYPE POLYBENCH_1D(p,NY,ny),
                     DATA_TYPE POLYBENCH_1D(r,NX,nx))
{
  #pragma omp target data \
    map(to: A[0:NX][0:NY], r[0:NX], p[0:NY]) \
    map(from: s[0:NY], q[0:NX])
  {
    #pragma omp target
    {
      int rows_per_chunk = NX; //(SPM_SIZE - NY) / (NY + 1);

      __device DATA_TYPE* p_spm = (__device DATA_TYPE *) hero_l1malloc(NY * sizeof(DATA_TYPE));
      __device DATA_TYPE* q_spm = (__device DATA_TYPE *) hero_l1malloc(rows_per_chunk * sizeof(DATA_TYPE));
      __device DATA_TYPE* A_spm = (__device DATA_TYPE *) hero_l1malloc(NY * rows_per_chunk * sizeof(DATA_TYPE));

      hero_memcpy_host2dev(p_spm, ((__host DATA_TYPE*) p), NY * sizeof(DATA_TYPE));

      int row = 0;
      while (row < NX) {
        int chunk_rows = (row + rows_per_chunk < NX) ? rows_per_chunk : (NX - row);
        hero_memcpy_host2dev(A_spm, ((__host DATA_TYPE*) A) + row*NY, chunk_rows*NY * sizeof(DATA_TYPE));

        #pragma omp parallel for num_threads(NUM_THREADS)
        for (int i = 0; i < chunk_rows; i++) {
          q_spm[i] = 0;
          for (int j = 0; j < NY; j++)
            q_spm[i] = q_spm[i] + A_spm[i*NY+j] * p_spm[j];
        }

        hero_memcpy_dev2host(((__host DATA_TYPE*) q) + row, q_spm, chunk_rows * sizeof(DATA_TYPE));
        row += rows_per_chunk;
      }

      hero_l1free(p_spm);
      hero_l1free(q_spm);
      hero_l1free(A_spm);
    }
    #pragma omp target
    {
      int rows_per_chunk = NX; //(SPM_SIZE - NY) / (NY + 1);

      __device DATA_TYPE* s_spm = (__device DATA_TYPE *) hero_l1malloc(NY * sizeof(DATA_TYPE));
      __device DATA_TYPE* r_spm = (__device DATA_TYPE *) hero_l1malloc(rows_per_chunk * sizeof(DATA_TYPE));
      __device DATA_TYPE* A_spm = (__device DATA_TYPE *) hero_l1malloc(NY * rows_per_chunk * sizeof(DATA_TYPE));

      #pragma omp parallel for num_threads(NUM_THREADS)
      for (int i = 0; i < NY; i++)
        s_spm[i] = 0;

      int row = 0;
      while (row < NX) {
        int chunk_rows = (row + rows_per_chunk < NX) ? rows_per_chunk : (NX - row);
        hero_dma_job_t job_A = hero_memcpy_host2dev_async(A_spm, ((__host DATA_TYPE*) A) + row*NY, chunk_rows*NY * sizeof(DATA_TYPE));
        hero_dma_job_t job_r = hero_memcpy_host2dev_async(r_spm, ((__host DATA_TYPE*) r) + row, chunk_rows * sizeof(DATA_TYPE));
        hero_dma_wait(job_A);
        hero_dma_wait(job_r);

        #pragma omp parallel for collapse(2) num_threads(NUM_THREADS)
        for (int j = 0; j < NY; j++) {
          for (int i = 0; i < chunk_rows; i++)
            s_spm[j] = s_spm[j] + r_spm[i] * A_spm[i*NY+j];
        }
        row += rows_per_chunk;
      }

      hero_memcpy_dev2host(((__host DATA_TYPE*) s), s_spm, NY * sizeof(DATA_TYPE));

      hero_l1free(s_spm);
      hero_l1free(r_spm);
      hero_l1free(A_spm);
    }
  }
}

/* Main computational kernel. The whole function will be timed,
   including the call and return. */
static
void kernel_bicg(int nx, int ny,
                 DATA_TYPE POLYBENCH_2D(A,NX,NY,nx,ny),
                 DATA_TYPE POLYBENCH_1D(s,NY,ny),
                 DATA_TYPE POLYBENCH_1D(q,NX,nx),
                 DATA_TYPE POLYBENCH_1D(p,NY,ny),
                 DATA_TYPE POLYBENCH_1D(r,NX,nx))
{
  #pragma scop
  #pragma omp target data \
    map(to: A[0:NX][0:NY], r[0:NX], p[0:NY]) \
    map(from: s[0:NY], q[0:NX])
  {
    #pragma omp target
    {
      #pragma omp parallel for num_threads(NUM_THREADS)
      for (int i = 0; i < _PB_NX; i++)
      {
        q[i] = 0;
        for (int j = 0; j < _PB_NY; j++) {
          q[i] = q[i] + A[i][j] * p[j];
        }
      }
      #pragma omp parallel for num_threads(NUM_THREADS)
      for (int i = 0; i < _PB_NY; i++)
        s[i] = 0;
      #pragma omp parallel for collapse(2) num_threads(NUM_THREADS)
      for (int j = 0; j < _PB_NY; j++)
      {
        for (int i = 0; i < _PB_NX; i++) {
          s[j] = s[j] + r[i] * A[i][j];
        }
      }
    }
  }
  #pragma endscop
}


int main(int argc, char** argv)
{
  omp_set_default_device(BIGPULP_MEMCPY);

  /* Retrieve problem size. */
  int nx = NX;
  int ny = NY;

  /* Variable declaration/allocation. */
  POLYBENCH_2D_ARRAY_DECL(A, DATA_TYPE, NX, NY, nx, ny);
  POLYBENCH_1D_ARRAY_DECL(s, DATA_TYPE, NY, ny);
  POLYBENCH_1D_ARRAY_DECL(q, DATA_TYPE, NX, nx);
  POLYBENCH_1D_ARRAY_DECL(p, DATA_TYPE, NY, ny);
  POLYBENCH_1D_ARRAY_DECL(r, DATA_TYPE, NX, nx);

  /* Initialize array(s). */
  init_array (nx, ny,
	      POLYBENCH_ARRAY(A),
	      POLYBENCH_ARRAY(r),
	      POLYBENCH_ARRAY(p));

  /* Start timer. */
  polybench_start_instruments;

  /* Run kernel. */
#ifdef POLYBENCH_DMA
  kernel_bicg_dma (nx, ny,
                   POLYBENCH_ARRAY(A),
                   POLYBENCH_ARRAY(s),
                   POLYBENCH_ARRAY(q),
                   POLYBENCH_ARRAY(p),
                   POLYBENCH_ARRAY(r));
#else
  kernel_bicg (nx, ny,
               POLYBENCH_ARRAY(A),
               POLYBENCH_ARRAY(s),
               POLYBENCH_ARRAY(q),
               POLYBENCH_ARRAY(p),
               POLYBENCH_ARRAY(r));
#endif

  /* Stop and print timer. */
  polybench_stop_instruments;
  polybench_print_instruments;

  /* Prevent dead-code elimination. All live-out data must be printed
     by the function call in argument. */
  polybench_prevent_dce(print_array(nx, ny, POLYBENCH_ARRAY(s), POLYBENCH_ARRAY(q)));

  /* Be clean. */
  POLYBENCH_FREE_ARRAY(A);
  POLYBENCH_FREE_ARRAY(s);
  POLYBENCH_FREE_ARRAY(q);
  POLYBENCH_FREE_ARRAY(p);
  POLYBENCH_FREE_ARRAY(r);

  return 0;
}
