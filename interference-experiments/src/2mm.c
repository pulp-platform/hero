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
//#include <cmux.c>
#ifdef PREM
#include <cmux.c>
#endif

/* Include benchmark-specific header. */
/* Default data type is double, default size is 4000. */
#include "2mm.h"


/* Array initialization. */
static
void init_array(int ni, int nj, int nk, int nl,
		DATA_TYPE *alpha,
		DATA_TYPE *beta,
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
	fprintf (stderr, DATA_PRINTF_MODIFIER, D[i][j]);
	if ((i * ni + j) % 20 == 0) fprintf (stderr, "\n");
    }
  fprintf (stderr, "\n");
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
  int i, j, k;
  /* D := alpha*A*B*C + beta*D */
  //#pragma acc data copyin(A,B,C) create(tmp) copyout (D)

  #pragma omp target data \
    map(to: A[0:NI][0:NK], B[0:NK][0:NJ], C[0:NL][0:NJ]) \
    map(alloc: tmp[0:NI][0:NJ]) \
    map(tofrom: D[0:NI][0:NL])

  {
    //#pragma acc parallel present_or_copyin(A,B) present_or_copyout(A,B,tmp) \
                         num_gangs[0](nj/8) num_gangs[1](ni/8) \
                         num_workers[0](8) num_workers[1](8)
    #pragma omp target
    {
      //#pragma acc loop gang[1] worker[1]

      for (j = 0; j < NJ; j++) {
        //#pragma acc loop gang[0] worker[0]
        for (i = 0; i < NI; i++) {
          tmp[i][j] = 0;
          //#pragma acc loop seq
          for (k = 0; k < NK; ++k)
             tmp[i][j] += alpha * A[i][k] * B[k][j];
        }
      }

    }

    //#pragma acc parallel present_or_copyin(C,tmp) present_or_copy(D) \
                         num_gangs[0](ni/8) num_gangs[1](nl/8) \
                         num_workers[0](8) num_workers[1](8)

    #pragma omp target
    {
      //#pragma acc loop gang[1] worker[1]
      for (j = 0; j < NL; j++) {
        //#pragma acc loop gang[0] worker[0]
        for (i = 0; i < NI; i++) {
          D[i][j] *= beta;
          //#pragma acc loop seq
          for (k = 0; k < NJ; ++k)
            D[i][j] += tmp[i][k] * C[k][j];
        }
      }
    }

  }
}


int main(int argc, char** argv)
{
  // Set to high prio
  int prio = -20;
  if(nice(prio) != prio) {
    perror("Could not set priority\n");
  }


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
#ifdef USEFLAG
  increment_flag(1);
#endif

  // Start timer.
  polybench_start_instruments;

  // Run kernel.
#ifdef LOOPFOREVER
  for(int i=0;i<1;i=0){
#else
	// Initialize counters to 0
	#ifdef TIMEKERN
  clock_gettime(CLOCK_MONOTONIC_RAW, &KernStrt);
	#endif
#endif

  /* Run kernel. */
	//printf("\n+++++++++++++++++++++++++++++++++++++++++\n");
	//printf("Function pointer address: %p", kernel_2mm);
	//printf("\n+++++++++++++++++++++++++++++++++++++++++\n\n");
  kernel_2mm (ni, nj, nk, nl,
	      alpha, beta,
	      POLYBENCH_ARRAY(tmp),
	      POLYBENCH_ARRAY(A),
	      POLYBENCH_ARRAY(B),
	      POLYBENCH_ARRAY(C),
	      POLYBENCH_ARRAY(D));
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
  polybench_prevent_dce(print_array(ni, nl,  POLYBENCH_ARRAY(D)));

  /* Be clean. */
  POLYBENCH_FREE_ARRAY(tmp);
  POLYBENCH_FREE_ARRAY(A);
  POLYBENCH_FREE_ARRAY(B);
  POLYBENCH_FREE_ARRAY(C);
  POLYBENCH_FREE_ARRAY(D);
#ifdef TIMEKERN
	eval_kern_time(KernStrt, KernStop);
#endif
#ifdef USEFLAG
  increment_flag(-1);
#endif

  return 0;
}
