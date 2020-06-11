/* POLYBENCH/GPU-OPENACC
 *
 * This file is a part of the Polybench/GPU-OpenACC suite
 *
 * Contact:
 * William Killian <killian@udel.edu>
 *
 * Copyright 2013, The University of Delaware
 */
#include <math.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

/* Include common header. */
#include <polybench.h>

#ifdef PREM
#include <cmux.c>
#endif
/* Include benchmark-specific header. */
/* Default data type is double, default size is 4000. */
#include "gemm.h"


/* Array initialization. */
static void init_array(int n, DATA_TYPE *alpha, DATA_TYPE *beta,
                       DATA_TYPE POLYBENCH_1D(y, N, n),
                       DATA_TYPE POLYBENCH_2D(A, N, N, n, n),
                       DATA_TYPE POLYBENCH_1D(x, N, n)) {
  int i, j;

  *alpha = 32412;
  *beta = 2123;
  for (i = 0; i < N; i++) {
    x[i] = ((DATA_TYPE)i) / N;
    y[i] = ((DATA_TYPE)i) / N;
    for (j = 0; j < N; j++)
      A[i][j] = ((DATA_TYPE)i * j) / N;
  }
}

/* DCE code. Must scan the entire live-out data.
   Can be used also to check the correctness of the output. */
static void print_array(int n, DATA_TYPE POLYBENCH_1D(y, N, n)) {
  int i;

  for (i = 0; i < N; i++) {
    fprintf(stderr, DATA_PRINTF_MODIFIER, y[i]);
    if ((i * n) % 20 == 0)
      fprintf(stderr, "\n");
  }
  fprintf(stderr, "\n");
}

/* Main computational kernel. The whole function will be timed,
   including the call and return. */
static void kernel_gemv(int n, DATA_TYPE alpha, DATA_TYPE beta,
                        DATA_TYPE POLYBENCH_1D(y, N, n),
                        DATA_TYPE POLYBENCH_2D(A, N, N, n, n),
                        DATA_TYPE POLYBENCH_1D(x, N, n)) {
//  int i, j, k;
#pragma omp target data map(tofrom : y[0 : N]) map(to : A[0 : N], x[0 : N])
#pragma omp target teams distribute parallel for schedule(                     \
    static, 1) num_teams(NUM_TEAMS) num_threads(NUM_THREADS)
    for (int j = 0; j < N; j++) {
      // y[j] *= beta;
      for (int i = 0; i < N; i++) {
        y[j] += alpha * A[j][i] * x[i];
      }
    }
  }

int main(int argc, char **argv) {
  /* Retrieve problem size. */
  int n = N;

  /* Variable declaration/allocation. */
  DATA_TYPE alpha;
  DATA_TYPE beta;
  POLYBENCH_1D_ARRAY_DECL(y, DATA_TYPE, N, n);
  POLYBENCH_2D_ARRAY_DECL(A, DATA_TYPE, N, N, n, n);
  POLYBENCH_1D_ARRAY_DECL(x, DATA_TYPE, N, n);

  /* Initialize array(s). */
  init_array(n, &alpha, &beta, POLYBENCH_ARRAY(x), POLYBENCH_ARRAY(A),
             POLYBENCH_ARRAY(y));

  // Start timer.
  polybench_start_instruments;

  // Run kernel.
#ifdef LOOPFOREVER
  for(int i=0;i<1;i=0){
#else
	#ifdef TIMEKERN
  clock_gettime(CLOCK_MONOTONIC_RAW, &KernStrt);
	#endif
#endif


  /* Run kernel. */
  kernel_gemv(n, alpha, beta, POLYBENCH_ARRAY(y), POLYBENCH_ARRAY(A),
              POLYBENCH_ARRAY(x));
#ifdef LOOPFOREVER
	}
#else
	#ifdef TIMEKERN
  	clock_gettime(CLOCK_MONOTONIC_RAW, &KernStop);
	#endif
#endif
  /* Stop and print timer. */
  polybench_stop_instruments;
  polybench_print_instruments;


  /* Prevent dead-code elimination. All live-out data must be printed
     by the function call in argument. */
  polybench_prevent_dce(print_array(n, POLYBENCH_ARRAY(y)));

  /* Be clean. */
  POLYBENCH_FREE_ARRAY(y);
  POLYBENCH_FREE_ARRAY(A);
  POLYBENCH_FREE_ARRAY(x);

#ifdef TIMEKERN
	eval_kern_time(KernStrt, KernStop);
#endif

  return 0;
}
