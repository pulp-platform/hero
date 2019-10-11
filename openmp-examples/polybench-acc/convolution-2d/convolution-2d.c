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
/* Default data type is double, default size is 4096x4096. */
#include "convolution-2d.h"


/* Array initialization. */
static
void init_array (int ni, int nj,
		 DATA_TYPE POLYBENCH_2D(A,NI,NJ,ni,nj))
{
  int i, j;

  for (i = 0; i < ni; i++)
    for (j = 0; j < nj; j++)
    {
      A[i][j] = ((DATA_TYPE) (i + j) / nj);
    }
}


/* DCE code. Must scan the entire live-out data.
   Can be used also to check the correctness of the output. */
static
void print_array(int ni, int nj,
		         DATA_TYPE POLYBENCH_2D(B,NI,NJ,ni,nj))
{
  int i, j;

  for (i = 0; i < ni; i++)
    for (j = 0; j < nj; j++) {
      printf(DATA_PRINTF_MODIFIER, B[i][j]);
      if ((i * NJ + j) % 20 == 0) printf("\n");
    }
  printf("\n");
}


/* Main computational kernel with DMA. The whole function will be
   timed, including the call and return. */
static
void kernel_conv2d_dma(int ni,
                       int nj,
                       DATA_TYPE POLYBENCH_2D(A,NI,NJ,ni,nj),
                       DATA_TYPE POLYBENCH_2D(B,NI,NJ,ni,nj))
{
  #pragma omp target data map(to: A[0:NI][0:NJ]) map(from: B[0:NI][0:NJ])
  {
    #pragma omp target
    {
      DMA_DATA_TYPE spm = alloc_spm();
      // Divide SPM between A and B
      int rows_per_chunk = NI; //(SPM_SIZE - 2*NJ) / (2*NJ);

      DMA_DATA_TYPE A_spm = spm;
      DMA_DATA_TYPE B_spm = spm + (rows_per_chunk+2) * NJ;

      int row = 0;
      while (row < NI - 2) {
        int chunk_rows = rows_per_chunk < (NI - 2 - row) ? rows_per_chunk : (NI - 2 - row);
        memcpy_to_spm(A_spm, ((int*) A) + row*NJ, (chunk_rows+2)*NJ);
        dma_flush();

        #pragma omp parallel for collapse(2) num_threads(NUM_THREADS)
        for (int i = 0; i < chunk_rows; ++i) {
          for (int j = 1; j < NJ - 1; ++j) {
            B_spm[i*NJ+j]
              =  2 * A_spm[( i )*NJ+j-1] + 5 * A_spm[( i )*NJ+j] + -8 * A_spm[( i )*NJ+j+1]
              + -3 * A_spm[(i+1)*NJ+j-1] + 6 * A_spm[(i+1)*NJ+j] + -9 * A_spm[(i+1)*NJ+j+1]
              +  4 * A_spm[(i+2)*NJ+j-1] + 7 * A_spm[(i+2)*NJ+j] +  1 * A_spm[(i+2)*NJ+j+1];
          }
        }

        memcpy_from_spm(((int*) B) + (row+1)*NJ, B_spm, chunk_rows*NJ);
        dma_flush();
        row += rows_per_chunk;
      }
    }
  }
}

/* Main computational kernel. The whole function will be timed,
   including the call and return. */
static
void kernel_conv2d(int ni,
		   int nj,
		   DATA_TYPE POLYBENCH_2D(A,NI,NJ,ni,nj),
		   DATA_TYPE POLYBENCH_2D(B,NI,NJ,ni,nj))
{
  #pragma scop
  #pragma omp target data map(to: A[0:NI][0:NJ]) map(from: B[0:NI][0:NJ])
  {
    #pragma omp target
    {
      #pragma omp parallel for collapse(2) num_threads(NUM_THREADS)
      for (int i = 1; i < _PB_NI - 1; ++i)
      {
        for (int j = 1; j < _PB_NJ - 1; ++j) {
          B[i][j]
            =  2 * A[i-1][j-1] + 5 * A[i-1][j] + -8 * A[i-1][j+1]
            + -3 * A[ i ][j-1] + 6 * A[ i ][j] + -9 * A[ i ][j+1]
            +  4 * A[i+1][j-1] + 7 * A[i+1][j] +  1 * A[i+1][j+1];
        }
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

  /* Variable declaration/allocation. */
  POLYBENCH_2D_ARRAY_DECL(A, DATA_TYPE, NI, NJ, ni, nj);
  POLYBENCH_2D_ARRAY_DECL(B, DATA_TYPE, NI, NJ, ni, nj);

  /* Initialize array(s). */
  init_array (ni, nj, POLYBENCH_ARRAY(A));

  /* Start timer. */
  polybench_start_instruments;

  /* Run kernel. */
#ifdef POLYBENCH_DMA
  kernel_conv2d_dma (ni, nj, POLYBENCH_ARRAY(A), POLYBENCH_ARRAY(B));
#else
  kernel_conv2d (ni, nj, POLYBENCH_ARRAY(A), POLYBENCH_ARRAY(B));
#endif

  /* Stop and print timer. */
  polybench_stop_instruments;
  polybench_print_instruments;

  /* Prevent dead-code elimination. All live-out data must be printed
     by the function call in argument. */
  polybench_prevent_dce(print_array(ni, nj, POLYBENCH_ARRAY(B)));

  /* Be clean. */
  POLYBENCH_FREE_ARRAY(A);
  POLYBENCH_FREE_ARRAY(B);

  return 0;
}
