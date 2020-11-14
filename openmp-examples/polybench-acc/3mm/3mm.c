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

/* Include hero runtime lib. */
#include <hero-target.h>

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
        printf (DATA_PRINTF_MODIFIER, G[i][j]);
        if ((i * ni + j) % 20 == 0) printf ("\n");
    }
  printf ("\n");
}


/* Main computational kernel with DMA. The whole function will be
   timed, including the call and return. */
static
void kernel_3mm_dma(int ni, int nj, int nk, int nl, int nm,
                    DATA_TYPE POLYBENCH_2D(E,NI,NJ,ni,nj),
                    DATA_TYPE POLYBENCH_2D(A,NI,NK,ni,nk),
                    DATA_TYPE POLYBENCH_2D(B,NK,NJ,nk,nj),
                    DATA_TYPE POLYBENCH_2D(F,NJ,NL,nj,nl),
                    DATA_TYPE POLYBENCH_2D(C,NJ,NM,nj,nm),
                    DATA_TYPE POLYBENCH_2D(D,NM,NL,nm,nl),
                    DATA_TYPE POLYBENCH_2D(G,NI,NL,ni,nl))
{
  #pragma omp target data \
    map(to: A[0:NI][0:NK], B[0:NK][0:NJ], C[0:NJ][0:NM], D[0:NM][0:NL]) \
    map(from: E[0:NI][0:NJ], F[0:NJ][0:NL], G[0:NI][0:NL])
  {
    /* E := A*B */
    #pragma omp target
    {
      int rows_per_chunk = NI; // (SPM_SIZE - NJ*NK) / (NJ+NK);

      __device DATA_TYPE* B_spm = (__device DATA_TYPE *) hero_l1malloc(NJ * NK * sizeof(DATA_TYPE));
      __device DATA_TYPE* A_spm = (__device DATA_TYPE *) hero_l1malloc(NK * rows_per_chunk * sizeof(DATA_TYPE));
      __device DATA_TYPE* E_spm = (__device DATA_TYPE *) hero_l1malloc(NK * rows_per_chunk * sizeof(DATA_TYPE));

      hero_memcpy_host2dev(B_spm, ((__host DATA_TYPE*) B), NJ*NK * sizeof(DATA_TYPE));

      int row = 0;
      while (row < NI) {
        int chunk_rows = (rows_per_chunk < NI - row) ? rows_per_chunk : (NI - row);

        hero_memcpy_host2dev(A_spm, ((__host DATA_TYPE*) A) + row*NK, chunk_rows*NK * sizeof(DATA_TYPE));

        #pragma omp parallel for collapse(2) num_threads(NUM_THREADS)
        for (int i = 0; i < chunk_rows; i++) {
          for (int j = 0; j < NJ; j++) {
            E_spm[i*NK+j] = 0;
            for (int k = 0; k < NK; ++k)
                E_spm[i*NK+j] += A_spm[i*NK+k] * B_spm[k*NK+j];
          }
        }

        hero_memcpy_dev2host(((__host DATA_TYPE*) E) + row*NJ, E_spm, chunk_rows*NJ * sizeof(DATA_TYPE));
        row += rows_per_chunk;
      }

      hero_l1free(E_spm);
      hero_l1free(A_spm);
      hero_l1free(B_spm);
    }
    /* F := C*D */
    #pragma omp target
    {
      int rows_per_chunk = NI; // (SPM_SIZE - NJ*NK) / (NJ+NK);

      __device DATA_TYPE* D_spm = (__device DATA_TYPE *) hero_l1malloc(NJ * NK * sizeof(DATA_TYPE));
      __device DATA_TYPE* C_spm = (__device DATA_TYPE *) hero_l1malloc(NK * rows_per_chunk * sizeof(DATA_TYPE));
      __device DATA_TYPE* F_spm = (__device DATA_TYPE *) hero_l1malloc(NK * rows_per_chunk * sizeof(DATA_TYPE));

      hero_memcpy_host2dev(D_spm, ((__host DATA_TYPE*) D), NJ*NK * sizeof(DATA_TYPE));

      int row = 0;
      while (row < NI) {
        int chunk_rows = (rows_per_chunk < NI - row) ? rows_per_chunk : (NI - row);

        hero_memcpy_host2dev(C_spm, ((__host DATA_TYPE*) C) + row*NK, chunk_rows*NK * sizeof(DATA_TYPE));

        #pragma omp parallel for collapse(2) num_threads(NUM_THREADS)
        for (int i = 0; i < chunk_rows; i++) {
          for (int j = 0; j < NL; j++) {
            F_spm[i*NK+j] = 0;
            for (int k = 0; k < NM; ++k)
              F_spm[i*NK+j] += C_spm[i*NK+k] * D_spm[k*NK+j];
          }
        }

        hero_memcpy_dev2host(((__host DATA_TYPE*) F) + row*NJ, F_spm, chunk_rows*NJ * sizeof(DATA_TYPE));
        row += rows_per_chunk;
      }

      hero_l1free(F_spm);
      hero_l1free(C_spm);
      hero_l1free(D_spm);
    }
    /* G := E*F */
    #pragma omp target
    {
      int rows_per_chunk = NI; // (SPM_SIZE - NJ*NK) / (NJ+NK);

      __device DATA_TYPE* F_spm = (__device DATA_TYPE *) hero_l1malloc(NJ * NK * sizeof(DATA_TYPE));
      __device DATA_TYPE* G_spm = (__device DATA_TYPE *) hero_l1malloc(NK * rows_per_chunk * sizeof(DATA_TYPE));
      __device DATA_TYPE* E_spm = (__device DATA_TYPE *) hero_l1malloc(NK * rows_per_chunk * sizeof(DATA_TYPE));

      hero_memcpy_host2dev(F_spm, ((__host DATA_TYPE*) F), NJ*NK * sizeof(DATA_TYPE));

      int row = 0;
      while (row < NI) {
        int chunk_rows = (rows_per_chunk < NI - row) ? rows_per_chunk : (NI - row);

        hero_memcpy_host2dev(E_spm, ((__host DATA_TYPE*) E) + row*NK, chunk_rows*NK * sizeof(DATA_TYPE));

        #pragma omp parallel for collapse(2) num_threads(NUM_THREADS)
        for (int i = 0; i < chunk_rows; i++) {
          for (int j = 0; j < NL; j++) {
            G_spm[i*NK+j] = 0;
            for (int k = 0; k < NJ; ++k)
              G_spm[i*NK+j] += E_spm[i*NK+k] * F_spm[k*NK+j];
          }
        }

        hero_memcpy_dev2host(((__host DATA_TYPE*) G) + row*NJ, G_spm, chunk_rows*NJ * sizeof(DATA_TYPE));
        row += rows_per_chunk;
      }

      hero_l1free(E_spm);
      hero_l1free(G_spm);
      hero_l1free(F_spm);
    }
  }
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
  #pragma omp target data \
    map(to: A[0:NI][0:NK], B[0:NK][0:NJ], C[0:NJ][0:NM], D[0:NM][0:NL]) \
    map(from: E[0:NI][0:NJ], F[0:NJ][0:NL], G[0:NI][0:NL])
  {
    /* E := A*B */
    #pragma omp target
    {
      #pragma omp parallel for collapse(2) num_threads(NUM_THREADS)
      for (int j = 0; j < NJ; j++) {
        for (int i = 0; i < NJ; i++) {
          E[i][j] = 0;
          for (int k = 0; k < NK; ++k)
              E[i][j] += A[i][k] * B[k][j];
        }
      }
    }
    /* F := C*D */
    #pragma omp target
    {
      #pragma omp parallel for collapse(2) num_threads(NUM_THREADS)
      for (int j = 0; j < NL; j++) {
        for (int i = 0; i < NJ; i++) {
          F[i][j] = 0;
          for (int k = 0; k < NM; ++k)
            F[i][j] += C[i][k] * D[k][j];
        }
      }
    }
    /* G := E*F */
    #pragma omp target
    {
      #pragma omp parallel for collapse(2) num_threads(NUM_THREADS)
      for (int j = 0; j < NL; j++) {
        for (int i = 0; i < NI; i++) {
          G[i][j] = 0;
          for (int k = 0; k < NJ; ++k)
            G[i][j] += E[i][k] * F[k][j];
        }
      }
    }
  }
}

int main(int argc, char** argv)
{
  omp_set_default_device(BIGPULP_MEMCPY);

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


  /* Start timer. */
  polybench_start_instruments;

  /* Run kernel. */
#ifdef POLYBENCH_DMA
  kernel_3mm_dma (ni, nj, nk, nl, nm,
                  POLYBENCH_ARRAY(E),
                  POLYBENCH_ARRAY(A),
                  POLYBENCH_ARRAY(B),
                  POLYBENCH_ARRAY(F),
                  POLYBENCH_ARRAY(C),
                  POLYBENCH_ARRAY(D),
                  POLYBENCH_ARRAY(G));
#else
  kernel_3mm (ni, nj, nk, nl, nm,
              POLYBENCH_ARRAY(E),
              POLYBENCH_ARRAY(A),
              POLYBENCH_ARRAY(B),
              POLYBENCH_ARRAY(F),
              POLYBENCH_ARRAY(C),
              POLYBENCH_ARRAY(D),
              POLYBENCH_ARRAY(G));
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

  return 0;
}
