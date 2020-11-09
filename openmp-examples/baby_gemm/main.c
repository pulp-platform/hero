#include "gemm.h"
#include<stdio.h>
#include<stdlib.h>

int main(int argc, char *argv[]) {
  int M = 16;
  int N = 173056;
  int K = 27;

  float* A = (float*)malloc(M*K*sizeof(float));
  float* B = (float*)malloc(K*N*sizeof(float));
  float* C = (float*)malloc(M*N*sizeof(float));
  float* E = (float*)malloc(M*N*sizeof(float));

  for (int m = 0; m < M; m++) {
    for (int k = 0; k < K; k++) {
      A[m*K+k] = (m+1)/(k+1);
    }
  }

  for (int k = 0; k < K; k++) {
    for (int n = 0; n < N; n++) {
      B[k*N+k] = (k+1)/(n+1);
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


  gemm(0, 0, M, N, K, 1.0, A, M, B, K, 1.0, C, M);

  int errors = 0;
  int same = 0;
  for (int i = 0; i < M * N; i++) {
    // printf("Output: %d, expected: %d\n", C_flt[i], E[i]);
    if (fabs(C[i] - E[i]) > 0.00001) {
      // printf("ERROR: Output: %f, expected: %f\n", C[i], E[i]);
      errors++;
    } else {
      same++;
    }
  }
  if (!errors) {
    printf("Computation successful!\n");
  } else {
    printf("Had %d errors and %d matches!\n", errors, same);
  }

  free(A);
  free(B);
  free(C);
  free(E);

  return 0;
}
