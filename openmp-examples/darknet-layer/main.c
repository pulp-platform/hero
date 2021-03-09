// Copyright (c) 2020 ETH Zurich and University of Bologna
// Licensed under the Apache License, Version 2.0; see LICENSE.Apache-2.0 for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <hero-target.h> // BIGPULP_MEMCPY
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#include "gemm.h"
#include "gemm_layers.h"

int LAYER_COUNTER;

int main(int argc, char* argv[]) {
  if (argc != 2) {
    printf("Please provide the layer to be tested\n");
    return 0;
  }

  LAYER_COUNTER = atoi(argv[1]);
  if (LAYER_COUNTER >= sizeof(LAYER_NEXT) / sizeof(unsigned) || LAYER_NEXT[LAYER_COUNTER] == -1) {
    printf("layer not recognized!\n");
    return 1;
  }

  const float ALPHA = 1.0;
  const int M = LAYER_M[LAYER_COUNTER];
  const int N = LAYER_N[LAYER_COUNTER];
  const int K = LAYER_K[LAYER_COUNTER];

  float* A = (float*)malloc(M * K * sizeof(float));
  float* B = (float*)malloc(K * N * sizeof(float));
  float* C = (float*)malloc(M * N * sizeof(float));
  float* E = (float*)malloc(M * N * sizeof(float));

  for (int m = 0; m < M; m++) {
    for (int k = 0; k < K; k++) {
      A[m * K + k] = ((m + 1.0) * (k + 1.0)) / ((M + 1.0) * (K + 1.0));
    }
  }

  for (int k = 0; k < K; k++) {
    for (int n = 0; n < N; n++) {
      B[k * N + n] = ((k + 1.0) * (n + 1.0)) / ((K + 1.0) * (N + 1.0));
    }
  }

  for (int m = 0; m < M; m++) {
    for (int n = 0; n < N; n++) {
      E[m * N + n] = 0.0;
      C[m * N + n] = 0.0;
      for (int k = 0; k < K; k++) {
        E[m * N + n] += A[m * K + k] * B[k * N + n];
      }
    }
  }

  // Initialize accelerator with a first "dummy" offload.  This ensures that the slight runtime
  // overhead of initializing the accelerator offload manager does not incur on the first measured
  // offload.
  printf("Initializing accelerator with a \"dummy\" offload.\n");
  uint32_t dummy = 0;
#pragma omp target device(BIGPULP_MEMCPY) map(tofrom: dummy)
  {
    dummy = 1;
  }
  assert(dummy == 1);
  printf("\n");

  printf("Calling gemm layer %i\n", LAYER_COUNTER);

  gemm_cpu(0, 0, M, N, K, ALPHA, A, 0, B, 0, 1, C, 0);

  int errors = 0;
  int same = 0;
  for (int i = 0; i < M; i++) {
    for (int j = 0; j < N; j++) {
      if (fabs(C[i * N + j] - E[i * N + j]) > 0.00001) {
        // printf("ERROR at C[%6d][%6d]: Output: %f, expected: %f\n", i, j, C[i*N+j], E[i*N+j]);
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
