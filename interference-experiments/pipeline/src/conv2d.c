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

/* Include benchmark-specific header. */
/* Default data type is double, default size is 4096x4096. */
#include "conv2d.h"


/* Array initialization. */
static
void init_array (int ni, int nj,
		 DATA_TYPE POLYBENCH_2D(A,NI,NJ,ni,nj))
{
  int i, j;

  for (i = 0; i < ni; i++)
    for (j = 0; j < nj; j++)
      {
	A[i][j] = ((DATA_TYPE) 10000 * i + j);
      }
}


/* DCE code. Must scan the entire live-out data.
   Can be used also to check the correctness of the output. */
static
void print_array(int ni, int nj,
		 DATA_TYPE POLYBENCH_2D(B,NI,NJ,ni,nj))

{
  int i, j;

  for (i = 1; i < ni-1; i++)
    for (j = 1; j < nj-1; j++) {
      fprintf(stderr, DATA_PRINTF_MODIFIER, B[i][j]);
      if ((i * NJ + j) % 20 == 0) fprintf(stderr, "\n");
    }
  fprintf(stderr, "\n");
}


/* Main computational kernel. The whole function will be timed,
   including the call and return. */
    static
void kernel_conv2d(int ni,
        int nj,
        DATA_TYPE POLYBENCH_2D(A,NI,NJ,ni,nj),
        DATA_TYPE POLYBENCH_2D(B,NI,NJ,ni,nj))
{
    int i, j;
    //#pragma scop
    #pragma omp target data map(to: A[0:NI][0:NJ]) map(from: B[0:NI][0:NJ]) //acc data copyin (A) copyout (B)
    {
        //#pragma acc parallel
        {
            #pragma omp target
            for (i = 1; i < NI - 1; ++i)
            //#pragma acc loop
                for (j = 1; j < NJ - 1; ++j)
                {
                    B[i][j]
                        =  2 * A[i-1][j-1] + 5 * A[i-1][j] + -8 * A[i-1][j+1]
                        + -3 * A[ i ][j-1] + 6 * A[ i ][j] + -9 * A[ i ][j+1]
                        +  4 * A[i+1][j-1] + 7 * A[i+1][j] +  1 * A[i+1][j+1];
                }
        }
    }
    //#pragma endscop
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
#ifdef LOOPFOREVER
	set_the_flag();
	while(1){
#else
	// Initialize counters to 0 
	wait_for_the_flag();	
	reset_perfcounters();
	#ifdef TIMEKERN
  clock_gettime(CLOCK_MONOTONIC_RAW, &KernStrt);
	#endif
#endif

  /* Run kernel. */
  kernel_conv2d (ni, nj, POLYBENCH_ARRAY(A), POLYBENCH_ARRAY(B));
#ifdef LOOPFOREVER
	}
#else
	#ifdef TIMEKERN
  	clock_gettime(CLOCK_MONOTONIC_RAW, &KernStop);
	#endif
  // Get counters 
	get_data_cache_misses();
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
#ifdef TIMEKERN
	eval_kern_time(KernStrt, KernStop);
#endif

  return 0;
}
