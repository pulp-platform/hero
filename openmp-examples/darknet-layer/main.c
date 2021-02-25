// Copyright (c) 2020 ETH Zurich and University of Bologna
// Licensed under the Apache License, Version 2.0; see LICENSE.Apache-2.0 for details.
// SPDX-License-Identifier: Apache-2.0

#include "gemm.h"
#include "gemm_layers.h"
#include<stdio.h>
#include<stdlib.h>
#include<math.h>
#include <time.h>

#define BILLION 1E9

double timediff(struct timespec start, struct timespec stop) {
  double diff = (stop.tv_sec - start.tv_sec) + (stop.tv_nsec - start.tv_nsec) / BILLION;
  return diff;
}

int main(int argc, char *argv[]) {
  if (argc != 2){
    printf("Please provide the layer to be tested\n");
    return 0;
  }

  int LAYER_COUNTER = atoi(argv[1]);
  float ALPHA = 1.0;
  int M, N, K;
  if (LAYER_COUNTER == 0) {
      M = 16, N = 173056, K = 27;
    } else if (LAYER_COUNTER == 2) {
      M = 32, N = 43264, K = 144;
    } else if (LAYER_COUNTER == 4) {
      M = 64, N = 10816, K = 288;
    } else if (LAYER_COUNTER == 6) {
      M = 128, N = 2704, K = 576;
    } else if (LAYER_COUNTER == 8) {
      M = 256, N = 676, K = 1152;
    } else if (LAYER_COUNTER == 10) {
      M = 512, N = 169, K = 2304;
    } else if (LAYER_COUNTER == 12) {
      M = 1024, N = 169, K = 4608;
    } else if (LAYER_COUNTER == 13) {
      M = 256, N = 169, K = 1024;
    } else if (LAYER_COUNTER == 14) {
      M = 512, N = 169, K = 2304;
    } else if (LAYER_COUNTER == 15) {
      M = 255, N = 169, K = 512;
    } else if (LAYER_COUNTER == 18) {
      M = 128, N = 169, K = 256;
    } else if (LAYER_COUNTER == 21) {
      M = 256, N = 676, K = 3456;
    } else if (LAYER_COUNTER == 22) {
      M = 255, N = 676, K = 256;
    } else {
      printf("layer not recognized, using smallest size!\n");
      return 1;
    }

  float* A = (float*)malloc(M*K*sizeof(float));
  float* B = (float*)malloc(K*N*sizeof(float));
  float* C = (float*)malloc(M*N*sizeof(float));
  float* E = (float*)malloc(M*N*sizeof(float));

  for (int m = 0; m < M; m++) {
    for (int k = 0; k < K; k++) {
      //A[m*K+k] = 1.0;
      A[m*K+k] = ((m+1.0)*(k+1.0))/((M+1.0)*(K+1.0));
    }
  }

  for (int k = 0; k < K; k++) {
    for (int n = 0; n < N; n++) {
      //B[k*N+n] = 1.0;
      B[k*N+n] = ((k+1.0)*(n+1.0))/((K+1.0)*(N+1.0));
    }
  }

  for (int m = 0; m < M; m++) {
    for (int n = 0; n < N; n++) {
      E[m*N+n] = 0.0;
      C[m*N+n] = 0.0;
      for (int k = 0; k < K; k++) {
        E[m*N+n] += A[m*K+k]*B[k*N+n];
      }
    }
  }

  printf("Calling gemm layer %i\n", LAYER_COUNTER);


#define TIME_LAYERS
#ifdef TIME_LAYERS
  printf("\nLayer %i\n========\n", LAYER_COUNTER);
  struct timespec tic, toc;
  clock_gettime(CLOCK_REALTIME, &tic);
#endif // TIME_LAYERS

  // Hack to call the manual layer (non-PREM only!)
  // LAYER_COUNTER = -1;

  if (LAYER_COUNTER == 0) {
      gemm_0(ALPHA, A, B, C);
    } else if (LAYER_COUNTER == 2) {
      gemm_2(ALPHA, A, B, C);
    } else if (LAYER_COUNTER == 4) {
      gemm_4(ALPHA, A, B, C);
    } else if (LAYER_COUNTER == 6) {
      gemm_6(ALPHA, A, B, C);
    } else if (LAYER_COUNTER == 8) {
      gemm_8(ALPHA, A, B, C);
    } else if (LAYER_COUNTER == 10) {
      gemm_10(ALPHA, A, B, C);
    } else if (LAYER_COUNTER == 12) {
      gemm_12(ALPHA, A, B, C);
    } else if (LAYER_COUNTER == 13) {
      gemm_13(ALPHA, A, B, C);
    } else if (LAYER_COUNTER == 14) {
      gemm_14(ALPHA, A, B, C);
    } else if (LAYER_COUNTER == 15) {
      gemm_15(ALPHA, A, B, C);
    } else if (LAYER_COUNTER == 18) {
      gemm_18(ALPHA, A, B, C);
    } else if (LAYER_COUNTER == 21) {
      gemm_21(ALPHA, A, B, C);
    } else if (LAYER_COUNTER == 22) {
      gemm_22(ALPHA, A, B, C);
    } else if (LAYER_COUNTER > 0) {
      printf("layer not recognized!\n");
      return 1;
    } else {
      // Call manual layer
      gemm_nn_tiled(M, N, K, ALPHA, A, 0, B, 0, C, 0);
    }

#ifdef TIME_LAYERS
  clock_gettime(CLOCK_REALTIME, &toc);
  printf("execution time: %lf\n", timediff(tic, toc));
#endif // TIME_LAYERS


  int errors = 0;
  int same = 0;
  for (int i = 0; i < M; i++) {
    for (int j = 0; j < N; j++) {
      if (fabs(C[i*N+j] - E[i*N+j]) > 0.00001) {
        //printf("ERROR at C[%6d][%6d]: Output: %f, expected: %f\n", i, j, C[i*N+j], E[i*N+j]);
        errors++;
      } else {
        same++;
      }
    }
  }
  if (!errors) {
    printf("Computation successful!\n");
  }
  printf("Had %d errors and %d matches!\n", errors, same);

  free(A);
  free(B);
  free(C);
  free(E);

  return 0;
}
