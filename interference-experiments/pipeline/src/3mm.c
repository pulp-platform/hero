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
/* Default data type is double, default size is 4000. */
#include "3mm.h"


/* Array initialization. */
static
void init_array(int ni, int nj, int nk, int nl, int nm,
                DATA_TYPE POLYBENCH_2D(A,NI,NK,ni,nk),
                DATA_TYPE POLYBENCH_2D(B,NK,NJ,nk,nj),
                DATA_TYPE POLYBENCH_2D(C,NJ,NM,nj,nm),
                DATA_TYPE POLYBENCH_2D(D,NM,NL,nm,nl))
{
  int i, j;

  for (i = 0; i < ni; i++)
    for (j = 0; j < nk; j++)
      A[i][j] = ((DATA_TYPE) i*j) / ni;
  for (i = 0; i < nk; i++)
    for (j = 0; j < nj; j++)
      B[i][j] = ((DATA_TYPE) i*(j+1)) / nj;
  for (i = 0; i < nj; i++)
    for (j = 0; j < nm; j++)
      C[i][j] = ((DATA_TYPE) i*(j+3)) / nl;
  for (i = 0; i < nm; i++)
    for (j = 0; j < nl; j++)
      D[i][j] = ((DATA_TYPE) i*(j+2)) / nk;
}


/* DCE code. Must scan the entire live-out data.
   Can be used also to check the correctness of the output. */
static
void print_array(int ni, int nl,
                 DATA_TYPE POLYBENCH_2D(G,NI,NL,ni,nl))
{
  int i, j;

  for (i = 0; i < ni; i++)
    for (j = 0; j < nl; j++) {
        fprintf (stderr, DATA_PRINTF_MODIFIER, G[i][j]);
        if ((i * ni + j) % 20 == 0) fprintf (stderr, "\n");
    }
  fprintf (stderr, "\n");
}


/* Main computational kernel. The whole function will be timed,
   including the call and return. */
static
void kernel_3mm(int ni, int nj, int nk, int nl, int nm,
                DATA_TYPE POLYBENCH_2D(E,NI,NJ,ni,nj),
                DATA_TYPE POLYBENCH_2D(A,NI,NK,ni,nk),
                DATA_TYPE POLYBENCH_2D(B,NK,NJ,nk,nj),
                DATA_TYPE POLYBENCH_2D(F,NJ,NL,nj,nl),
                DATA_TYPE POLYBENCH_2D(C,NJ,NM,nj,nm),
                DATA_TYPE POLYBENCH_2D(D,NM,NL,nm,nl),
                DATA_TYPE POLYBENCH_2D(G,NI,NL,ni,nl))
{
  int i, j, k;

  //#pragma acc data copyin(A,B,C,D) create(E,F) copyout(G)
  #pragma omp target data \
    map(to: A[0:NI][0:NK], B[0:NK][0:NJ], C[0:NJ][0:NM], D[0:NM][0:NL]) \
    map(from: E[0:NI][0:NJ], F[0:NJ][0:NL], G[0:NI][0:NL])
  {
    /* E := A*B */
    //#pragma acc parallel present(E,A,B) \
                         num_gangs[0](nj/8) num_gangs[1](ni/8) \
                         num_workers[0](8) num_workers[1](8)
    {
      //#pragma acc loop gang[1] worker[1]
      #pragma omp target
      for (j = 0; j < NJ; j++) {
        //#pragma acc loop gang[0] worker[0]
        for (i = 0; i < NJ; i++) {
          E[i][j] = 0;
          //#pragma acc loop seq
          for (k = 0; k < NK; ++k)
              E[i][j] += A[i][k] * B[k][j];
        }
      }
    }
    /* F := C*D */
    //#pragma acc parallel present(F,C,D) \
                         num_gangs[0](nl/8) num_gangs[1](nj/8) \
                         num_workers[0](8) num_workers[1](8)
    {
      //#pragma acc loop gang[1] worker[1]
      #pragma omp target
      for (j = 0; j < NL; j++) {
        for (i = 0; i < NJ; i++) {
        //#pragma acc loop gang[0] worker[0]
          F[i][j] = 0;
          //#pragma acc loop seq
          for (k = 0; k < NM; ++k)
            F[i][j] += C[i][k] * D[k][j];
        }
      }
    }
    /* G := E*F */
    //#pragma acc parallel present(G,E,F) \
                         num_gangs[0](nl/8) num_gangs[1](ni/8) \
                         num_workers[0](8) num_workers[1](8)
    {
      //#pragma acc loop gang[1] worker[1]
      #pragma omp target
      for (j = 0; j < NL; j++) {
        for (i = 0; i < NI; i++) {
        //#pragma acc loop gang[0] worker[0]
          G[i][j] = 0;
          //#pragma acc loop seq
          for (k = 0; k < NJ; ++k)
            G[i][j] += E[i][k] * F[k][j];
        }
      }
    }
  }
}

int main(int argc, char** argv)
{
  /* Retrieve problem size. */
  int ni = NI;
  int nj = NJ;
  int nk = NK;
  int nl = NL;
  int nm = NM;

  /* Variable declaration/allocation. */
  POLYBENCH_2D_ARRAY_DECL(E, DATA_TYPE, NI, NJ, ni, nj);
  POLYBENCH_2D_ARRAY_DECL(A, DATA_TYPE, NI, NK, ni, nk);
  POLYBENCH_2D_ARRAY_DECL(B, DATA_TYPE, NK, NJ, nk, nj);
  POLYBENCH_2D_ARRAY_DECL(F, DATA_TYPE, NJ, NL, nj, nl);
  POLYBENCH_2D_ARRAY_DECL(C, DATA_TYPE, NJ, NM, nj, nm);
  POLYBENCH_2D_ARRAY_DECL(D, DATA_TYPE, NM, NL, nm, nl);
  POLYBENCH_2D_ARRAY_DECL(G, DATA_TYPE, NI, NL, ni, nl);

  /* Initialize array(s). */
  init_array (ni, nj, nk, nl, nm,
              POLYBENCH_ARRAY(A),
              POLYBENCH_ARRAY(B),
              POLYBENCH_ARRAY(C),
              POLYBENCH_ARRAY(D));


  // Start timer. 
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
  kernel_3mm (ni, nj, nk, nl, nm,
              POLYBENCH_ARRAY(E),
              POLYBENCH_ARRAY(A),
              POLYBENCH_ARRAY(B),
              POLYBENCH_ARRAY(F),
              POLYBENCH_ARRAY(C),
              POLYBENCH_ARRAY(D),
              POLYBENCH_ARRAY(G));
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
  polybench_prevent_dce(print_array(ni, nl,  POLYBENCH_ARRAY(G)));

  /* Be clean. */
  POLYBENCH_FREE_ARRAY(E);
  POLYBENCH_FREE_ARRAY(A);
  POLYBENCH_FREE_ARRAY(B);
  POLYBENCH_FREE_ARRAY(F);
  POLYBENCH_FREE_ARRAY(C);
  POLYBENCH_FREE_ARRAY(D);
  POLYBENCH_FREE_ARRAY(G);
#ifdef TIMEKERN
	eval_kern_time(KernStrt, KernStop);
#endif

  return 0;
}
