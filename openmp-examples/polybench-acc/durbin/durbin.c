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
#include "durbin.h"


/* Array initialization. */
static
void init_array (int n,
    DATA_TYPE POLYBENCH_2D(y,N,N,n,n),
    DATA_TYPE POLYBENCH_2D(sum,N,N,n,n),
    DATA_TYPE POLYBENCH_1D(alpha,N,n),
    DATA_TYPE POLYBENCH_1D(beta,N,n),
    DATA_TYPE POLYBENCH_1D(r,N,n))
{
  int i, j;

  for (i = 0; i < n; i++)
    {
      alpha[i] = i;
      beta[i] = (i+1);
      r[i] = (i+1);
      for (j = 0; j < n; j++) {
        y[i][j] = ((DATA_TYPE) i*j);
        sum[i][j] = ((DATA_TYPE) i*j);
      }
    }
}


/* DCE code. Must scan the entire live-out data.
   Can be used also to check the correctness of the output. */
static
void print_array(int n,
    DATA_TYPE POLYBENCH_1D(out,N,n))

{
  int i;

  for (i = 0; i < n; i++) {
    printf (DATA_PRINTF_MODIFIER, out[i]);
    if (i % 20 == 0) printf ("\n");
  }
  printf ("\n");
}

/* Main computational kernel with DMA. The whole function will be
   timed, including the call and return. */
// This kernel only works if the all data fit into the memory of
// the acceleartor.  FIXME: Tile this benchmark.
static
void kernel_durbin_dma(int n,
    DATA_TYPE POLYBENCH_2D(y,N,N,n,n),
    DATA_TYPE POLYBENCH_2D(sum,N,N,n,n),
    DATA_TYPE POLYBENCH_1D(alpha,N,n),
    DATA_TYPE POLYBENCH_1D(beta,N,n),
    DATA_TYPE POLYBENCH_1D(r,N,n),
    DATA_TYPE POLYBENCH_1D(out,N,n))
{
  #pragma omp target \
    map(to: alpha[0:N], beta[0:N], r[0:N], sum[0:N][0:N], y[0:N][0:N]) \
    map(from: out[0:N])
  {
    DATA_TYPE* const spm = (DATA_TYPE*)alloc_spm();
    DATA_TYPE* const y_spm = spm;
    DATA_TYPE* const sum_spm = (y_spm + N*N);
    DATA_TYPE* const alpha_spm = (sum_spm + N*N);
    DATA_TYPE* const beta_spm = (alpha_spm + N);
    DATA_TYPE* const r_spm = (beta_spm + N);
    DATA_TYPE* const out_spm = (r_spm + N);

    memcpy_to_spm(y_spm, ((DATA_TYPE*)y), N*N);
    memcpy_to_spm(sum_spm, ((DATA_TYPE*)sum), N*N);
    memcpy_to_spm(alpha_spm, ((DATA_TYPE*)alpha), N);
    memcpy_to_spm(beta_spm, ((DATA_TYPE*)beta), N);
    memcpy_to_spm(r_spm, ((DATA_TYPE*)r), N);
    dma_flush();

    y_spm[0] = r_spm[0];
    beta_spm[0] = 1;
    alpha_spm[0] = r_spm[0];
    #pragma omp parallel num_threads(NUM_THREADS)
    {
      #pragma omp for
      for (int k = 1; k < _PB_N; k++)
      {
        beta_spm[k] = beta_spm[k-1] -
          alpha_spm[k-1] * alpha_spm[k-1] * beta_spm[k-1];
        sum_spm[k] = r_spm[k];
        for (int i = 0; i <= k - 1; i++)
          sum_spm[(i+1)*N+k] = sum_spm[i*N+k] + r_spm[k-i-1] * y_spm[i*N+k-1];
        alpha_spm[k] = -sum_spm[k*N+k] * beta_spm[k];
        for (int i = 0; i <= k-1; i++)
          y_spm[i*N+k] = y_spm[i*N+k-1] + alpha_spm[k] * y_spm[(k-i-1)*N+k-1];
        y_spm[k*N+k] = alpha_spm[k];
      }
      #pragma omp for
      for (int i = 0; i < _PB_N; i++)
        out_spm[i] = y_spm[i*N+_PB_N-1];
    }

    memcpy_from_spm(((DATA_TYPE*)out), out_spm, N);
    dma_flush();

    dealloc_spm(spm);
  }
}

/* Main computational kernel. The whole function will be timed,
   including the call and return. */
static
void kernel_durbin(int n,
    DATA_TYPE POLYBENCH_2D(y,N,N,n,n),
    DATA_TYPE POLYBENCH_2D(sum,N,N,n,n),
    DATA_TYPE POLYBENCH_1D(alpha,N,n),
    DATA_TYPE POLYBENCH_1D(beta,N,n),
    DATA_TYPE POLYBENCH_1D(r,N,n),
    DATA_TYPE POLYBENCH_1D(out,N,n))
{
  #pragma scop
  #pragma omp target \
    map(to: alpha[0:N], beta[0:N], r[0:N], sum[0:N][0:N], y[0:N][0:N]) \
    map(from: out[0:N])
  {
    y[0][0] = r[0];
    beta[0] = 1;
    alpha[0] = r[0];
    #pragma omp parallel num_threads(NUM_THREADS)
    {
      #pragma omp for
      for (int k = 1; k < _PB_N; k++)
      {
        beta[k] = beta[k-1] - alpha[k-1] * alpha[k-1] * beta[k-1];
        sum[0][k] = r[k];
        for (int i = 0; i <= k - 1; i++)
          sum[i+1][k] = sum[i][k] + r[k-i-1] * y[i][k-1];
        alpha[k] = -sum[k][k] * beta[k];
        for (int i = 0; i <= k-1; i++)
          y[i][k] = y[i][k-1] + alpha[k] * y[k-i-1][k-1];
        y[k][k] = alpha[k];
      }
      #pragma omp for
      for (int i = 0; i < _PB_N; i++)
        out[i] = y[i][_PB_N-1];
    }
  }
  #pragma endscop
}


int main(int argc, char** argv)
{
  /* Retrieve problem size. */
  int n = N;

  /* Variable declaration/allocation. */
  POLYBENCH_2D_ARRAY_DECL(y, DATA_TYPE, N, N, n, n);
  POLYBENCH_2D_ARRAY_DECL(sum, DATA_TYPE, N, N, n, n);
  POLYBENCH_1D_ARRAY_DECL(alpha, DATA_TYPE, N, n);
  POLYBENCH_1D_ARRAY_DECL(beta, DATA_TYPE, N, n);
  POLYBENCH_1D_ARRAY_DECL(r, DATA_TYPE, N, n);
  POLYBENCH_1D_ARRAY_DECL(out, DATA_TYPE, N, n);


  /* Initialize array(s). */
  init_array (n,
    POLYBENCH_ARRAY(y),
    POLYBENCH_ARRAY(sum),
    POLYBENCH_ARRAY(alpha),
    POLYBENCH_ARRAY(beta),
    POLYBENCH_ARRAY(r));

  /* Start timer. */
  polybench_start_instruments;

  /* Run kernel. */
#ifdef POLYBENCH_DMA
  kernel_durbin_dma
#else
  kernel_durbin
#endif
    (n,
    POLYBENCH_ARRAY(y),
    POLYBENCH_ARRAY(sum),
    POLYBENCH_ARRAY(alpha),
    POLYBENCH_ARRAY(beta),
    POLYBENCH_ARRAY(r),
    POLYBENCH_ARRAY(out));

  /* Stop and print timer. */
  polybench_stop_instruments;
  polybench_print_instruments;

  /* Prevent dead-code elimination. All live-out data must be printed
     by the function call in argument. */
  polybench_prevent_dce(print_array(n, POLYBENCH_ARRAY(out)));

  /* Be clean. */
  POLYBENCH_FREE_ARRAY(y);
  POLYBENCH_FREE_ARRAY(sum);
  POLYBENCH_FREE_ARRAY(alpha);
  POLYBENCH_FREE_ARRAY(beta);
  POLYBENCH_FREE_ARRAY(r);
  POLYBENCH_FREE_ARRAY(out);

  return 0;
}
