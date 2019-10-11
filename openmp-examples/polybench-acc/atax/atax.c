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

/* Include dma lib. */
#include <dmatransfer.h>

/* Include benchmark-specific header. */
/* Default data type is double, default size is 4000. */
#include "atax.h"


/* Array initialization. */
static
void init_array (int nx, int ny,
                 DATA_TYPE POLYBENCH_2D(A,NX,NY,nx,ny),
                 DATA_TYPE POLYBENCH_1D(x,NY,ny))
{
  int i, j;

  for (i = 0; i < ny; i++)
      x[i] = i * M_PI;
  for (i = 0; i < nx; i++)
    for (j = 0; j < ny; j++)
      A[i][j] = ((DATA_TYPE) i*(j+1)) / nx;
}


/* DCE code. Must scan the entire live-out data.
   Can be used also to check the correctness of the output. */
static
void print_array(int nx,
                 DATA_TYPE POLYBENCH_1D(y,NX,nx))

{
  int i;

  for (i = 0; i < nx; i++) {
    printf (DATA_PRINTF_MODIFIER, y[i]);
    if (i % 20 == 0) printf ("\n");
  }
  printf ("\n");
}

/* Main computational kernel with DMA. The whole function will be
   timed, including the call and return. */
static
void kernel_atax_dma(int nx, int ny,
                     DATA_TYPE POLYBENCH_2D(A,NX,NY,nx,ny),
                     DATA_TYPE POLYBENCH_1D(x,NY,ny),
                     DATA_TYPE POLYBENCH_1D(y,NY,ny),
                     DATA_TYPE POLYBENCH_1D(tmp,NX,nx))
{
  int i, j;

  #pragma omp target data \
    map(to: A[0:NX][0:NY], x[0:NY]) \
    map(alloc: tmp[0:NX]) \
    map(from: y[0:NY])
  {
    #pragma omp target
    {
      DMA_DATA_TYPE spm = alloc_spm();
      int rows_per_chunk = NX; // (SPM_SIZE - NY) / (NY + 1);

      DMA_DATA_TYPE x_spm = spm;
      DMA_DATA_TYPE tmp_spm = spm + NY;
      DMA_DATA_TYPE A_spm = spm + NY + rows_per_chunk;

      memcpy_to_spm(x_spm, ((int*) x), NY);

      int row = 0;
      while (row < NX) {
        int chunk_rows = (row + rows_per_chunk < NX) ? rows_per_chunk : (NX - row);
        memcpy_to_spm(A_spm, ((int*) A) + row*NY, chunk_rows*NY);
        dma_flush();

        #pragma omp parallel for num_threads(NUM_THREADS)
        for (i = 0; i < chunk_rows; i++) {
          tmp_spm[i] = 0;
          for (j = 0; j < NY; j++){
            tmp_spm[i] = tmp_spm[i] + A_spm[i*NY+j] * x_spm[j];
          }
        }

        memcpy_from_spm(((int*) tmp) + row, tmp_spm, chunk_rows);
        dma_flush();
        row += rows_per_chunk;
      }
    }

    #pragma omp target
    {
      DMA_DATA_TYPE spm = alloc_spm();
      int rows_per_chunk = NX; // (SPM_SIZE - NY) / (NY + 1);

      DMA_DATA_TYPE y_spm = spm;
      DMA_DATA_TYPE tmp_spm = spm + NY;
      DMA_DATA_TYPE A_spm = spm + NY + rows_per_chunk;

      int row = 0;
      while (row < NX) {
        int chunk_rows = (row + rows_per_chunk < NX) ? rows_per_chunk : (NX - row);
        memcpy_to_spm(A_spm, ((int*) A) + row*NY, chunk_rows*NY);
        memcpy_to_spm(tmp_spm, ((int*) tmp) + row, chunk_rows);
        dma_flush();

        #pragma omp parallel for num_threads(NUM_THREADS)
        for (i = 0; i < NY; i++) {
          y_spm[i] = 0;
          for (j = 0; j < chunk_rows; j++)
            y_spm[i] = y_spm[i] + A_spm[j*NY+i] * tmp_spm[j];
        }
        row += rows_per_chunk;
      }

      memcpy_from_spm(((int*) y), y_spm, NY);
      dma_flush();
    }
  }
}

/* Main computational kernel. The whole function will be timed,
   including the call and return. */
static
void kernel_atax(int nx, int ny,
                 DATA_TYPE POLYBENCH_2D(A,NX,NY,nx,ny),
                 DATA_TYPE POLYBENCH_1D(x,NY,ny),
                 DATA_TYPE POLYBENCH_1D(y,NY,ny),
                 DATA_TYPE POLYBENCH_1D(tmp,NX,nx))
{
  #pragma omp target data \
    map(to: A[0:NX][0:NY], x[0:NY]) \
    map(alloc: tmp[0:NX]) \
    map(from: y[0:NY])
  {
    /* tmp := A*x */
    #pragma omp target
    {
      #pragma omp parallel for num_threads(NUM_THREADS)
      for (int i = 0; i < NX; i++) {
        tmp[i] = 0;
        for (int j = 0; j < NY; j++)
          tmp[i] = tmp[i] + A[i][j] * x[j];
      }
    }
    /* y := t(A)*tmp */
    #pragma omp target
    {
      #pragma omp parallel for num_threads(NUM_THREADS)
      for (int i = 0; i < NY; i++) {
        y[i] = 0;
        for (int j = 0; j < NX; j++)
          y[i] = y[i] + A[j][i] * tmp[j];
      }
    }
  }
}


int main(int argc, char** argv)
{
  /* Retrieve problem size. */
  int nx = NX;
  int ny = NY;

  /* Variable declaration/allocation. */
  POLYBENCH_2D_ARRAY_DECL(A, DATA_TYPE, NX, NY, nx, ny);
  POLYBENCH_1D_ARRAY_DECL(x, DATA_TYPE, NY, ny);
  POLYBENCH_1D_ARRAY_DECL(y, DATA_TYPE, NY, ny);
  POLYBENCH_1D_ARRAY_DECL(tmp, DATA_TYPE, NX, nx);

  /* Initialize array(s). */
  init_array (nx, ny, POLYBENCH_ARRAY(A), POLYBENCH_ARRAY(x));

  /* Start timer. */
  polybench_start_instruments;

  /* Run kernel. */
#ifdef POLYBENCH_DMA
  kernel_atax_dma (nx, ny,
                   POLYBENCH_ARRAY(A),
                   POLYBENCH_ARRAY(x),
                   POLYBENCH_ARRAY(y),
                   POLYBENCH_ARRAY(tmp));
#else
  kernel_atax (nx, ny,
               POLYBENCH_ARRAY(A),
               POLYBENCH_ARRAY(x),
               POLYBENCH_ARRAY(y),
               POLYBENCH_ARRAY(tmp));
#endif


  /* Stop and print timer. */
  polybench_stop_instruments;
  polybench_print_instruments;

  /* Prevent dead-code elimination. All live-out data must be printed
     by the function call in argument. */
  polybench_prevent_dce(print_array(nx, POLYBENCH_ARRAY(y)));

  /* Be clean. */
  POLYBENCH_FREE_ARRAY(A);
  POLYBENCH_FREE_ARRAY(x);
  POLYBENCH_FREE_ARRAY(y);
  POLYBENCH_FREE_ARRAY(tmp);

  return 0;
}
