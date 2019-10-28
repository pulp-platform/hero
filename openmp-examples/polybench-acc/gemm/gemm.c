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

/* Include dma lib. */
#include <dmatransfer.h>

/* Include benchmark-specific header. */
/* Default data type is double, default size is 4000. */
#include "gemm.h"


/* Array initialization. */
static
void init_array(int ni, int nj, int nk,
                DATA_TYPE *alpha,
                DATA_TYPE *beta,
                DATA_TYPE POLYBENCH_2D(C,NI,NJ,ni,nj),
                DATA_TYPE POLYBENCH_2D(A,NI,NK,ni,nk),
                DATA_TYPE POLYBENCH_2D(B,NK,NJ,nk,nj))
{
  int i, j;

  *alpha = 32412;
  *beta = 2123;
  for (i = 0; i < ni; i++)
    for (j = 0; j < nj; j++)
      C[i][j] = ((DATA_TYPE) i*j) / ni;
  for (i = 0; i < ni; i++)
    for (j = 0; j < nk; j++)
      A[i][j] = ((DATA_TYPE) i*j) / ni;
  for (i = 0; i < nk; i++)
    for (j = 0; j < nj; j++)
      B[i][j] = ((DATA_TYPE) i*j) / ni;
}


/* DCE code. Must scan the entire live-out data.
   Can be used also to check the correctness of the output. */
static
void print_array(int ni, int nj,
		 DATA_TYPE POLYBENCH_2D(C,NI,NJ,ni,nj))
{
  int i, j;

  for (i = 0; i < ni; i++)
    for (j = 0; j < nj; j++) {
      printf (DATA_PRINTF_MODIFIER, C[i][j]);
      if ((i * ni + j) % 20 == 0) printf ("\n");
    }
  printf ("\n");
}

/* Main computational kernel with DMA. The whole function will be
   timed, including the call and return. */
static
void kernel_gemm_dma(int ni, int nj, int nk,
                     DATA_TYPE alpha,
                     DATA_TYPE beta,
                     DATA_TYPE POLYBENCH_2D(C,NI,NJ,ni,nj),
                     DATA_TYPE POLYBENCH_2D(A,NI,NK,ni,nk),
                     DATA_TYPE POLYBENCH_2D(B,NK,NJ,nk,nj))
{
  #pragma omp target data map(tofrom: C[0:NI][0:NJ]) map(to: A[0:NI][0:NK], B[0:NK][0:NJ])
  {
    #pragma omp target
    {
      DATA_TYPE* spm = alloc_spm();
      int rows_per_chunk = NI; // (SPM_SIZE - NJ*NK) / (NJ+NK);

      DATA_TYPE* B_spm = spm;
      DATA_TYPE* A_spm = spm + NJ*NK;
      DATA_TYPE* C_spm = spm + NJ*NK + NK*rows_per_chunk;

      memcpy_to_spm(B_spm, ((DATA_TYPE*) B), NJ*NK);

      /* C := alpha*A*B + beta*C */
      int row = 0;
      while (row < NI) {
        int chunk_rows = (rows_per_chunk < NI - row) ? rows_per_chunk : (NI - row);
        memcpy_to_spm(A_spm, ((DATA_TYPE*) A) + row*NK, chunk_rows*NK);
        memcpy_to_spm(C_spm, ((DATA_TYPE*) C) + row*NJ, chunk_rows*NJ);
        dma_flush();

        #pragma omp parallel for collapse(2) num_threads(NUM_THREADS) firstprivate(alpha, beta)
        for (int i = 0; i < chunk_rows; i++) {
          for (int j = 0; j < NJ; j++) {
            C_spm[i*NJ+j] *= beta;
            for (int k = 0; k < NK; ++k) {
              C_spm[i*NJ+j] += alpha * A_spm[i*NK+k] * B_spm[k*NJ+j];
            }
          }
        }

        memcpy_from_spm(((DATA_TYPE*) C) + row*NJ, C_spm, chunk_rows*NJ);
        dma_flush();
        row += rows_per_chunk;
      }

      dealloc_spm(spm);
    }
  }
}


/* Main computational kernel. The whole function will be timed,
   including the call and return. */
static
void kernel_gemm(int ni, int nj, int nk,
                 DATA_TYPE alpha,
                 DATA_TYPE beta,
                 DATA_TYPE POLYBENCH_2D(C,NI,NJ,ni,nj),
                 DATA_TYPE POLYBENCH_2D(A,NI,NK,ni,nk),
                 DATA_TYPE POLYBENCH_2D(B,NK,NJ,nk,nj))
{
  #pragma scop
  #pragma omp target data map(tofrom: C[0:NI][0:NJ]) map(to: A[0:NI][0:NK], B[0:NK][0:NJ])
  {
    #pragma omp target
    {
      /* C := alpha*A*B + beta*C */
      #pragma omp parallel for collapse(2) num_threads(NUM_THREADS)
      for (int i = 0; i < _PB_NI; i++)
        for (int j = 0; j < _PB_NJ; j++)
        {
          C[i][j] *= beta;
          for (int k = 0; k < _PB_NK; ++k)
            C[i][j] += alpha * A[i][k] * B[k][j];
        }
    }
  }
  #pragma endscop
}


int main(int argc, char** argv)
{
  /* Retrieve problem size. */
  int ni = NI;
  int nj = NJ;
  int nk = NK;

  /* Variable declaration/allocation. */
  DATA_TYPE alpha;
  DATA_TYPE beta;
  POLYBENCH_2D_ARRAY_DECL(C,DATA_TYPE,NI,NJ,ni,nj);
  POLYBENCH_2D_ARRAY_DECL(A,DATA_TYPE,NI,NK,ni,nk);
  POLYBENCH_2D_ARRAY_DECL(B,DATA_TYPE,NK,NJ,nk,nj);

  /* Initialize array(s). */
  init_array (ni, nj, nk, &alpha, &beta,
	      POLYBENCH_ARRAY(C),
	      POLYBENCH_ARRAY(A),
	      POLYBENCH_ARRAY(B));

  /* Start timer. */
  polybench_start_instruments;

  /* Run kernel. */
#ifdef POLYBENCH_DMA
  kernel_gemm_dma (ni, nj, nk,
                   alpha, beta,
                   POLYBENCH_ARRAY(C),
                   POLYBENCH_ARRAY(A),
                   POLYBENCH_ARRAY(B));
#else
  kernel_gemm (ni, nj, nk,
               alpha, beta,
               POLYBENCH_ARRAY(C),
               POLYBENCH_ARRAY(A),
               POLYBENCH_ARRAY(B));
#endif

  /* Stop and print timer. */
  polybench_stop_instruments;
  polybench_print_instruments;

  /* Prevent dead-code elimination. All live-out data must be printed
     by the function call in argument. */
  polybench_prevent_dce(print_array(ni, nj,  POLYBENCH_ARRAY(C)));

  /* Be clean. */
  POLYBENCH_FREE_ARRAY(C);
  POLYBENCH_FREE_ARRAY(A);
  POLYBENCH_FREE_ARRAY(B);

  return 0;
}
