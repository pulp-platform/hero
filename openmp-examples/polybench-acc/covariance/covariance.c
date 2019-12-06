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
#include "covariance.h"


/* Array initialization. */
static
void init_array (int m, int n,
    DATA_TYPE *float_n,
    DATA_TYPE POLYBENCH_2D(data,M,N,m,n))
{
  int i, j;

  *float_n = 1.2;

  for (i = 0; i < M; i++)
    for (j = 0; j < N; j++)
      data[i][j] = ((DATA_TYPE) i*j) / M;
}


/* DCE code. Must scan the entire live-out data.
   Can be used also to check the correctness of the output. */
static
void print_array(int m,
    DATA_TYPE POLYBENCH_2D(symmat,M,M,m,m))

{
  int i, j;

  for (i = 0; i < m; i++)
    for (j = 0; j < m; j++) {
      printf (DATA_PRINTF_MODIFIER, symmat[i][j]);
      if ((i * m + j) % 20 == 0) printf ("\n");
    }
  printf ("\n");
}


/* Main computational kernel. The whole function will be timed,
   including the call and return. */
static
void kernel_covariance(int m, int n,
    DATA_TYPE float_n,
    DATA_TYPE POLYBENCH_2D(data,M,N,m,n),
    DATA_TYPE POLYBENCH_2D(symmat,M,M,m,m),
    DATA_TYPE POLYBENCH_1D(mean,M,m))
{
  #pragma scop
  #pragma omp target \
    map(to: data[0:M][0:N], float_n) \
    map(alloc: mean[0:M]) \
    map(from: symmat[0:M][0:M])
  {
    /* Determine mean of column vectors of input data matrix */
    #pragma omp parallel num_threads(NUM_THREADS)
    {
      #pragma omp for
      for (int j = 0; j < _PB_M; j++) {
        mean[j] = 0.0;
        for (int i = 0; i < _PB_N; i++)
          mean[j] += data[i][j];
        mean[j] /= float_n;
      }

      /* Center the column vectors. */
      #pragma omp for
      for (int i = 0; i < _PB_N; i++)
        for (int j = 0; j < _PB_M; j++)
          data[i][j] -= mean[j];

      /* Calculate the m * m covariance matrix. */
      #pragma omp for
      for (int j1 = 0; j1 < _PB_M; j1++)
        for (int j2 = j1; j2 < _PB_M; j2++) {
          symmat[j1][j2] = 0.0;
          for (int i = 0; i < _PB_N; i++)
            symmat[j1][j2] += data[i][j1] * data[i][j2];
          symmat[j2][j1] = symmat[j1][j2];
        }
    }
  }
  #pragma endscop
}

int main(int argc, char** argv)
{
  /* Retrieve problem size. */
  int n = N;
  int m = M;

  /* Variable declaration/allocation. */
  DATA_TYPE float_n;
  POLYBENCH_2D_ARRAY_DECL(data,DATA_TYPE,M,N,m,n);
  POLYBENCH_2D_ARRAY_DECL(symmat,DATA_TYPE,M,M,m,m);
  POLYBENCH_1D_ARRAY_DECL(mean,DATA_TYPE,M,m);

  /* Initialize array(s). */
  init_array (m, n, &float_n, POLYBENCH_ARRAY(data));

  /* Start timer. */
  polybench_start_instruments;

  /* Run kernel. */
  kernel_covariance (m, n, float_n,
      POLYBENCH_ARRAY(data),
      POLYBENCH_ARRAY(symmat),
      POLYBENCH_ARRAY(mean));

  /* Stop and print timer. */
  polybench_stop_instruments;
  polybench_print_instruments;

  /* Prevent dead-code elimination. All live-out data must be printed
     by the function call in argument. */
  polybench_prevent_dce(print_array(m, POLYBENCH_ARRAY(symmat)));

  /* Be clean. */
  POLYBENCH_FREE_ARRAY(data);
  POLYBENCH_FREE_ARRAY(symmat);
  POLYBENCH_FREE_ARRAY(mean);

  return 0;
}
