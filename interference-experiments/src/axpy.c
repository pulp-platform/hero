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
// Include polybench common header.
#include <polybench.h>

#ifdef PREM
#include <cmux.c>
#endif

// Include benchmark-specific header.
// Default data type is double, default size is 4000.

#include "axpy.h"



// Array initialization.
static void init_array(int n, DATA_TYPE *alpha, DATA_TYPE POLYBENCH_1D(Y, N, n),
                       DATA_TYPE POLYBENCH_1D(X, N, n)) {
  int i, j;

  *alpha = 10000;
  for (i = 0; i < N; i++)
    Y[i] = (DATA_TYPE)i;

  for (i = 0; i < N; i++)
    X[i] = (DATA_TYPE)i;
}

// DCE code. Must scan the entire live-out data.
// Can be used also to check the correctness of the output.
static void print_array(int n, DATA_TYPE POLYBENCH_1D(Y, N, n)) {
  int i;

  for (i = 0; i < N; i++) {
    fprintf(stderr, DATA_PRINTF_MODIFIER, Y[i]);
  }
  fprintf(stderr, "\n");
}

// Main computational kernel. The whole function will be timed,
// including the call and return.
static void kernel_axpy(int n, DATA_TYPE alpha, DATA_TYPE POLYBENCH_1D(Y, N, n),
                        DATA_TYPE POLYBENCH_1D(X, N, n)) {
  int i;
  #pragma omp target data map(tofrom: Y[0:N]) map(to: X[0:N])
  #pragma omp target
  for (i = 0; i < N; i++) {
    Y[i] += alpha * X[i];
  }
}

int main(int argc, char **argv) {
  // Set to high prio
  int prio = -20;
  if(nice(prio) != prio) {
    perror("Could not set priority\n");
  }

  // Retrieve problem size.
  int n = N;

  // Variable declaration/allocation.
  DATA_TYPE alpha;
  DATA_TYPE beta;
  POLYBENCH_1D_ARRAY_DECL(Y, DATA_TYPE, N, n);
  POLYBENCH_1D_ARRAY_DECL(X, DATA_TYPE, N, n);

  // Initialize array(s).
  init_array(n, &alpha, POLYBENCH_ARRAY(Y), POLYBENCH_ARRAY(X));

  // Start timer.
  polybench_start_instruments;

#ifdef USEFLAG
  increment_flag(1);
#endif

#ifdef LOOPFOREVER
  for(int i=0;i<1;i=0){
#else
	#ifdef TIMEKERN
  clock_gettime(CLOCK_MONOTONIC_RAW, &KernStrt);
	#endif
#endif

	//for(int i=0;i<N;i++){;}
	//Run Kernel
  kernel_axpy(n, alpha, POLYBENCH_ARRAY(Y), POLYBENCH_ARRAY(X));
#ifdef LOOPFOREVER
	}
#else
	#ifdef TIMEKERN
  	clock_gettime(CLOCK_MONOTONIC_RAW, &KernStop);
	#endif
#endif

	// Stop and print timer.
  polybench_stop_instruments;
  polybench_print_instruments;

  // Prevent dead-code elimination. All live-out data must be printed by the function call in argument.
  polybench_prevent_dce(print_array(n, POLYBENCH_ARRAY(Y)));

  // Be clean.
  POLYBENCH_FREE_ARRAY(Y);
  POLYBENCH_FREE_ARRAY(X);

#ifdef TIMEKERN
	eval_kern_time(KernStrt, KernStop);
#endif
#ifdef USEFLAG
  increment_flag(-1);
#endif
  return 0;
}

