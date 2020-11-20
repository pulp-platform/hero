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
#include "2mm.h"


/* Array initialization. */
static
void init_array(int ni, int nj, int nk, int nl,
                DATA_TYPE* alpha,
                DATA_TYPE* beta,
                DATA_TYPE POLYBENCH_2D(A,NI,NK,ni,nl),
                DATA_TYPE POLYBENCH_2D(B,NK,NJ,nk,nj),
                DATA_TYPE POLYBENCH_2D(C,NL,NJ,nl,nj),
                DATA_TYPE POLYBENCH_2D(D,NI,NL,ni,nl))
{
  int i, j;

  *alpha = 32412;
  *beta = 2123;
  for (i = 0; i < ni; i++)
    for (j = 0; j < nk; j++)
      A[i][j] = ((DATA_TYPE) i*j) / ni;
  for (i = 0; i < nk; i++)
    for (j = 0; j < nj; j++)
      B[i][j] = ((DATA_TYPE) i*(j+1)) / nj;
  for (i = 0; i < nl; i++)
    for (j = 0; j < nj; j++)
      C[i][j] = ((DATA_TYPE) i*(j+3)) / nl;
  for (i = 0; i < ni; i++)
    for (j = 0; j < nl; j++)
      D[i][j] = ((DATA_TYPE) i*(j+2)) / nk;
}


/* DCE code. Must scan the entire live-out data.
   Can be used also to check the correctness of the output. */
static
void print_array(int ni, int nl,
		 DATA_TYPE POLYBENCH_2D(D,NI,NL,ni,nl))
{
  int i, j;

  for (i = 0; i < ni; i++)
    for (j = 0; j < nl; j++) {
    printf (DATA_PRINTF_MODIFIER, D[i][j]);
    if ((i * ni + j) % 20 == 0) printf ("\n");
    }
  printf ("\n");
}

/* Main computational kernel with DMA. The whole function will be
   timed, including the call and return. */
static
void kernel_2mm_dma(int ni, int nj, int nk, int nl,
                    DATA_TYPE alpha,
                    DATA_TYPE beta,
                    DATA_TYPE POLYBENCH_2D(tmp,NI,NJ,ni,nj),
                    DATA_TYPE POLYBENCH_2D(A,NI,NK,ni,nk),
                    DATA_TYPE POLYBENCH_2D(B,NK,NJ,nk,nj),
                    DATA_TYPE POLYBENCH_2D(C,NL,NJ,nl,nj),
                    DATA_TYPE POLYBENCH_2D(D,NI,NL,ni,nl))
{
  #pragma omp target data \
    map(to: A[0:NI][0:NK], B[0:NK][0:NJ], C[0:NL][0:NJ]) \
    map(alloc: tmp[0:NI][0:NJ]) \
    map(tofrom: D[0:NI][0:NL])
  {
    #pragma omp target
    {
      int rows_per_chunk = NI;

      __device DATA_TYPE* B_spm = (__device DATA_TYPE*) hero_l1malloc(NJ * NK * sizeof(DATA_TYPE));
      __device DATA_TYPE* A_spm = (__device DATA_TYPE*) hero_l1malloc(NK * rows_per_chunk * sizeof(DATA_TYPE));
      __device DATA_TYPE* tmp_spm = (__device DATA_TYPE*) hero_l1malloc(NK * rows_per_chunk * sizeof(DATA_TYPE));

      hero_memcpy_host2dev(B_spm, (__host DATA_TYPE*) B, NJ*NK * sizeof(DATA_TYPE));

      int row = 0;
      while (row < NI) {
        int chunk_rows = (rows_per_chunk < NI - row) ? rows_per_chunk : (NI - row);

        hero_memcpy_host2dev(A_spm, ((__host DATA_TYPE*) A) + row*NK, chunk_rows*NK * sizeof(DATA_TYPE));

        #pragma omp parallel for collapse(2) num_threads(NUM_THREADS) firstprivate(alpha)
        for (int i = 0; i < rows_per_chunk; i++) {
          for (int j = 0; j < NJ; j++) {
            tmp_spm[i*NJ+j] = 0;
            for (int k = 0; k < NK; ++k)
              tmp_spm[i*NJ+j] += alpha * A_spm[i*NK+k] * B_spm[k*NJ+j];
          }
        }

        hero_memcpy_dev2host(((__host DATA_TYPE*) tmp) + row*NJ, tmp_spm, chunk_rows*NJ * sizeof(DATA_TYPE));
        row += rows_per_chunk;
      }

      hero_l1free(tmp_spm);
      hero_l1free(A_spm);
      hero_l1free(B_spm);
    }

    #pragma omp target
    {
      int rows_per_chunk = NI; // (SPM_SIZE - NJ*NK) / (NJ+NK);

      __device DATA_TYPE* C_spm = (__device DATA_TYPE*) hero_l1malloc(NJ * NK * sizeof(DATA_TYPE));
      __device DATA_TYPE* D_spm = (__device DATA_TYPE*) hero_l1malloc(NK * rows_per_chunk * sizeof(DATA_TYPE));
      __device DATA_TYPE* tmp_spm = (__device DATA_TYPE*) hero_l1malloc(NK * rows_per_chunk * sizeof(DATA_TYPE));

      hero_memcpy_host2dev(C_spm, ((__host DATA_TYPE*) C), NJ*NK * sizeof(DATA_TYPE));

      int row = 0;
      while (row < NI) {
        int chunk_rows = (rows_per_chunk < NI - row) ? rows_per_chunk : (NI - row);

        hero_dma_job_t job_tmp = hero_memcpy_host2dev_async(tmp_spm, ((__host DATA_TYPE*) tmp) + row*NK, chunk_rows*NK * sizeof(DATA_TYPE));
        hero_dma_job_t job_D = hero_memcpy_host2dev_async(D_spm, ((__host DATA_TYPE*) D) + row*NK, chunk_rows*NK * sizeof(DATA_TYPE));
        hero_dma_wait(job_tmp);
        hero_dma_wait(job_D);

        #pragma omp parallel for collapse(2) num_threads(NUM_THREADS) firstprivate(beta)
        for (int i = 0; i < chunk_rows; i++) {
          for (int j = 0; j < NL; j++) {
            D_spm[i*NL+j] *= beta;
            for (int k = 0; k < NJ; ++k)
              D_spm[i*NL+j] += tmp_spm[i*NJ+k] * C_spm[k*NJ+j];
          }
        }

        hero_memcpy_dev2host(((__host DATA_TYPE*) D) + row*NJ, D_spm, chunk_rows*NJ * sizeof(DATA_TYPE));
        row += rows_per_chunk;
      }

      hero_l1free(tmp_spm);
      hero_l1free(D_spm);
      hero_l1free(C_spm);
    }
  }
}

/* Main computational kernel. The whole function will be timed,
   including the call and return. */
static
void kernel_2mm(int ni, int nj, int nk, int nl,
                DATA_TYPE alpha,
                DATA_TYPE beta,
                DATA_TYPE POLYBENCH_2D(tmp,NI,NJ,ni,nj),
                DATA_TYPE POLYBENCH_2D(A,NI,NK,ni,nk),
                DATA_TYPE POLYBENCH_2D(B,NK,NJ,nk,nj),
                DATA_TYPE POLYBENCH_2D(C,NL,NJ,nl,nj),
                DATA_TYPE POLYBENCH_2D(D,NI,NL,ni,nl))
{
  #pragma scop
  /* D := alpha*A*B*C + beta*D */
  #pragma omp target data \
    map(tofrom: A[0:NI][0:NK], B[0:NK][0:NJ], C[0:NL][0:NJ]) \
    map(tofrom: tmp[0:NI][0:NJ]) \
    map(tofrom: D[0:NI][0:NL])
  {
    #pragma omp target
    {
      #pragma omp parallel for collapse(2) num_threads(NUM_THREADS)
      for (int i = 0; i < _PB_NI; i++)
        for (int j = 0; j < _PB_NJ; j++)
        {
          tmp[i][j] = 0;
          for (int k = 0; k < _PB_NK; ++k)
            tmp[i][j] += alpha * A[i][k] * B[k][j];
        }

    }
    #pragma omp target
    {
      #pragma omp parallel for collapse(2) num_threads(NUM_THREADS)
      for (int i = 0; i < _PB_NI; i++)
        for (int j = 0; j < _PB_NL; j++)
        {
          D[i][j] *= beta;
          for (int k = 0; k < _PB_NJ; ++k)
            D[i][j] += tmp[i][k] * C[k][j];
        }
    }
  }
  #pragma endscop
}


int main(int argc, char** argv)
{
  omp_set_default_device(BIGPULP_MEMCPY);

  /* Retrieve problem size. */
  int ni = NI;
  int nj = NJ;
  int nk = NK;
  int nl = NL;

  /* Variable declaration/allocation. */
  DATA_TYPE alpha;
  DATA_TYPE beta;
  POLYBENCH_2D_ARRAY_DECL(tmp,DATA_TYPE,NI,NJ,ni,nj);
  POLYBENCH_2D_ARRAY_DECL(A,DATA_TYPE,NI,NK,ni,nk);
  POLYBENCH_2D_ARRAY_DECL(B,DATA_TYPE,NK,NJ,nk,nj);
  POLYBENCH_2D_ARRAY_DECL(C,DATA_TYPE,NL,NJ,nl,nj);
  POLYBENCH_2D_ARRAY_DECL(D,DATA_TYPE,NI,NL,ni,nl);

  /* Initialize array(s). */
  init_array (ni, nj, nk, nl, &alpha, &beta,
	      POLYBENCH_ARRAY(A),
	      POLYBENCH_ARRAY(B),
	      POLYBENCH_ARRAY(C),
	      POLYBENCH_ARRAY(D));

  /* Start timer. */
  polybench_start_instruments;

  /* Run kernel. */
#ifdef POLYBENCH_DMA
  kernel_2mm_dma (ni, nj, nk, nl,
	      alpha, beta,
	      POLYBENCH_ARRAY(tmp),
	      POLYBENCH_ARRAY(A),
	      POLYBENCH_ARRAY(B),
	      POLYBENCH_ARRAY(C),
	      POLYBENCH_ARRAY(D));
#else
  kernel_2mm (ni, nj, nk, nl,
	      alpha, beta,
	      POLYBENCH_ARRAY(tmp),
	      POLYBENCH_ARRAY(A),
	      POLYBENCH_ARRAY(B),
	      POLYBENCH_ARRAY(C),
	      POLYBENCH_ARRAY(D));
#endif

  /* Stop and print timer. */
  polybench_stop_instruments;
  polybench_print_instruments;

  /* Prevent dead-code elimination. All live-out data must be printed
     by the function call in argument. */
  polybench_prevent_dce(print_array(ni, nl,  POLYBENCH_ARRAY(D)));

  /* Be clean. */
  POLYBENCH_FREE_ARRAY(tmp);
  POLYBENCH_FREE_ARRAY(A);
  POLYBENCH_FREE_ARRAY(B);
  POLYBENCH_FREE_ARRAY(C);
  POLYBENCH_FREE_ARRAY(D);

  return 0;
}
