#include "gemm.h"

#include <dmatransfer.h>
#include <hero-target.h>
#include <cmux.h>
#include <cmux.c>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

//#include "cuda.h"
//#include "hero_perf.h"
//#include "utils.h"

#define BILLION 1E9
//#define TIME_DMA_AND_COMP

int LAYER_COUNTER=0;

void gemm_bin(int M, int N, int K, float ALPHA, char *A, int lda, float *B, int ldb, float *C,
              int ldc) {
  int i, j, k;
  for (i = 0; i < M; ++i) {
    for (k = 0; k < K; ++k) {
      char A_PART = A[i * lda + k];
      if (A_PART) {
        for (j = 0; j < N; ++j) {
          C[i * ldc + j] += B[k * ldb + j];
        }
      } else {
        for (j = 0; j < N; ++j) {
          C[i * ldc + j] -= B[k * ldb + j];
        }
      }
    }
  }
}

float *random_matrix(int rows, int cols) {
  int i;
  float *m = calloc(rows * cols, sizeof(float));
  for (i = 0; i < rows * cols; ++i) {
    m[i] = (float)rand() / RAND_MAX;
  }
  return m;
}

void time_random_matrix(int TA, int TB, int m, int k, int n) {
  float *a;
  if (!TA)
    a = random_matrix(m, k);
  else
    a = random_matrix(k, m);
  int lda = (!TA) ? k : m;
  float *b;
  if (!TB)
    b = random_matrix(k, n);
  else
    b = random_matrix(n, k);
  int ldb = (!TB) ? n : k;

  float *c = random_matrix(m, n);
  int i;
  clock_t start = clock(), end;
  for (i = 0; i < 10; ++i) {
    gemm_cpu(TA, TB, m, n, k, 1, a, lda, b, ldb, 1, c, n);
  }
  end = clock();
  printf("Matrix Multiplication %dx%d * %dx%d, TA=%d, TB=%d: %lf ms\n", m, k, k, n, TA, TB,
         (float)(end - start) / CLOCKS_PER_SEC);
  free(a);
  free(b);
  free(c);
}

void gemm(int TA, int TB, int M, int N, int K, float ALPHA, float *A, int lda, float *B, int ldb,
          float BETA, float *C, int ldc) {
  gemm_cpu(TA, TB, M, N, K, ALPHA, A, lda, B, ldb, BETA, C, ldc);
}

#pragma omp declare target
int inline my_min(int a, int b) {
  if (a < b) {
    return a;
  } else {
    return b;
  }
}
#pragma omp end declare target

void gemm_nn(int M, int N, int K, float ALPHA,
        float *A, int lda,
        float *B, int ldb,
        float *C, int ldc)
{
    int i,j,k;
    #pragma omp parallel for
    for(i = 0; i < M; ++i){
        for(k = 0; k < K; ++k){
            register float A_PART = ALPHA*A[i*lda+k];
            for(j = 0; j < N; ++j){
                C[i*ldc+j] += A_PART*B[k*ldb+j];
            }
        }
    }
}

void gemm_zero(float ALPHA, float *A, float *B, float *C)
{
  const int M = 16;
  const int N = 173056;
  const int K = 27;

  int m,n,k;
  float (*matA)[K] = (float(*)[K]) A;
  float (*matB)[N] = (float(*)[N]) B;
  float (*matC)[N] = (float(*)[N]) C;
  float temp;

  #pragma omp target data device(BIGPULP_MEMCPY) map(to: matB[0:27][0:173056])
  {
  #pragma omp target data device(BIGPULP_MEMCPY) map(to: matA[0:16][0:27])
  {
  #pragma omp target device(BIGPULP_MEMCPY) map(tofrom: matC[0:16][0:173056])
//  #pragma omp target device(BIGPULP_MEMCPY) map(tofrom: matC[0:M][0:N]) map(to: matA[0:M][0:K], matB[0:K][0:N])
  //map(to: matA[0:M][0:K], matB[0:K][0:N])
    {
//    #pragma omp parallel for private(m, n, k, temp) num_threads(8)
//    #pragma omp for collapse(2) private(m, n, k, temp)
    for(m = 0; m < M; ++m){
      for(k = 0; k < K; ++k){
        temp = ALPHA*matA[m][k];
        for(n = 0; n < N; ++n){
          matC[m][n] +=temp*matB[k][n];
        }
      }
    }
  }
  }
  }
    LAYER_COUNTER=2;
}
//#pragma omp end declare target

// gemm kernel offloaded, with manual DMA transactions
/*
void gemm_nn_manual_DMA(int M, int N, int K, float ALPHA,
        float *A, int lda,
        float *B, int ldb,
        float *C, int ldc) {
  // For correctness check
//#define TIMELAYERS
//#define CORRECTNESS
#ifdef CORRECTNESS
  float *E_flt = (float *)malloc(M * N * sizeof(float));
  for (int m = 0; m < M; m++) {
    for (int n = 0; n < N; n++) {
      E_flt[m * N + n] = 0.0;
      for (int k = 0; k < K; k++) {
        E_flt[m * N + n] += A[m * K + k] * B[k * N + n];
      }
    }
  }

#endif
#ifdef TIMELAYERS
  struct timespec requestStart, requestEnd;
  clock_gettime(CLOCK_REALTIME, &requestStart);
#endif
#ifdef TIME_DMA_AND_COMP
  unsigned int dma_cycles = 0;
  unsigned int comp_cycles = 0;
  unsigned int ld_stalls = 0;
#endif

// clang-format off
#ifdef TIME_DMA_AND_COMP
#pragma omp target device(BIGPULP_MEMCPY) \
    map(tofrom: C [0:M * N], dma_cycles, comp_cycles, ld_stalls) \
    map(to: A [0:M * K], B [0:K * N])
#else
#pragma omp target device(BIGPULP_MEMCPY) \
    map(tofrom: C [0:M * N]) \
    map(to: A [0:M * K], B [0:K * N])
#endif
// clang-format on
  {
#ifdef TIME_DMA_AND_COMP
    hero_perf_enable(CYCLES);
    hero_perf_enable(STALLS_LOAD);
#endif

    // Compute memory allocation block sizes
    const int L1_b = 80 * 1024;
    const int L1_flt = L1_b / sizeof(float);
    const int blockSize = sqrt(L1_flt / 3);

    // Allocate memory in L3
    int *spm = alloc_spm();
    float *A_spm = spm;
    float *B_spm = A_spm + blockSize * blockSize;
    float *C_spm = B_spm + blockSize * blockSize;

    // Compute kernel
#pragma omp parallel num_threads(8)
    {
      const uint32_t ld_stalls_before = hero_perf_get(STALLS_LOAD);  // per core
      for (int bn = 0; bn < N && N - bn - 1 != 0; bn += my_min(N - bn - 1, blockSize)) {
        for (int bk = 0; bk < K && K - bk - 1 != 0; bk += my_min(K - bk - 1, blockSize)) {
#pragma omp single
          {
#ifdef TIME_DMA_AND_COMP
            const uint32_t cycles_before = hero_perf_get(CYCLES);
#endif
            for (int r = 0; r < blockSize; r++) {
              // Copy in B with K rows of length N
              memcpy_to_spm(B_spm + r * blockSize, B + (bk + r) * N + bn, blockSize);
            }
#ifdef TIME_DMA_AND_COMP
            dma_cycles += hero_perf_get(CYCLES) - cycles_before;
#endif
          }
          for (int bm = 0; bm < M && M - bm - 1 != 0; bm += my_min(M - bm - 1, blockSize)) {
#pragma omp single
            {
#ifdef TIME_DMA_AND_COMP
              const uint32_t cycles_before = hero_perf_get(CYCLES);
#endif
              for (int r = 0; r < blockSize; r++) {
                // Copy in A, with M rows of length K
                memcpy_to_spm(A_spm + r * blockSize, A + (bm + r) * K + bk, blockSize);
                // Copy in C with M rows of length N
                memcpy_to_spm(C_spm + r * blockSize, C + (bm + r) * N + bn, blockSize);
              }
              dma_flush();
#ifdef TIME_DMA_AND_COMP
              dma_cycles += hero_perf_get(CYCLES) - cycles_before;
#endif
            }

            int limitM = my_min(M - bm, blockSize);
            int limitN = my_min(N - bn, blockSize);
            int limitK = my_min(K - bk, blockSize);

#ifdef TIME_DMA_AND_COMP
            uint32_t cycles_before = 0;
#pragma omp master
            cycles_before = hero_perf_get(CYCLES);
#endif
#pragma omp for collapse(2)
            for (int m = 0; m < limitM; m++) {
              for (int n = 0; n < limitN; n++) {
                for (int k = 0; k < limitK; k++) {
                  C_spm[m * blockSize + n] += A_spm[m * blockSize + k] * B_spm[k * blockSize + n];
                }
              }
            }
#ifdef TIME_DMA_AND_COMP
#pragma omp master
            comp_cycles += hero_perf_get(CYCLES) - cycles_before;
#endif

#pragma omp single
            {
#ifdef TIME_DMA_AND_COMP
              const uint32_t cycles_before = hero_perf_get(CYCLES);
#endif
              // Copy out C with M rows of length N
              for (int r = 0; r < blockSize; r++) {
                memcpy_from_spm(C + (bm + r) * N + bn, C_spm + r * blockSize, blockSize);
              }
              dma_flush();
#ifdef TIME_DMA_AND_COMP
              dma_cycles += hero_perf_get(CYCLES) - cycles_before;
#endif
            }
          }
        }
      }

#ifdef TIME_DMA_AND_COMP
#pragma omp single
      // TODO: this should be `atomic update` to take all cores into account, but that freezes
      // execution
      { ld_stalls += hero_perf_get(STALLS_LOAD) - ld_stalls_before; }
#endif
    }

    dealloc_spm(spm);
  }
#ifdef TIME_DMA_AND_COMP
  printf("DMA cycles:  %u\n", dma_cycles);
  printf("Computation: %u\n", comp_cycles);
  printf("Load stalls: %u\n", ld_stalls);
#endif

#ifdef TIMELAYERS
  clock_gettime(CLOCK_REALTIME, &requestEnd);
  double accum = (requestEnd.tv_sec - requestStart.tv_sec) +
                 (requestEnd.tv_nsec - requestStart.tv_nsec) / BILLION;
  printf("Time spent on layer: %lf\n", accum);
#endif

#ifdef CORRECTNESS
  // Compare correctness.
  int errors = 0;
  int same = 0;
  for (int i = 0; i < M * N; i++) {
    // printf("Output: %d, expected: %d\n", C_flt[i], E_flt[i]);
    if (fabs(C[i] - E_flt[i]) > 0.00001) {
      // printf("ERROR: Output: %f, expected: %f\n", C[i], E_flt[i]);
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
  free(E_flt);
#endif
}


// gemm kernel offloaded to PULP without manual DMA
void gemm_nn_noDMA(int M, int N, int K, float ALPHA, float *A, int lda, float *B, int ldb, float *C,
             int ldc) {
  // For correctness check
//#define TIMELAYERS
//#define CORRECTNESS
//#define BLOCKEDMM
//#define SEPARATE_SCOPE
#ifdef CORRECTNESS
  float *E_flt = (float *)malloc(M * N * sizeof(float));
  for (int m = 0; m < M; m++) {
    for (int n = 0; n < N; n++) {
      E_flt[m * N + n] = 0.0;
      for (int k = 0; k < K; k++) {
        E_flt[m * N + n] += A[m * K + k] * B[k * N + n];
      }
    }
  }
#endif

#ifdef TIMELAYERS
  struct timespec requestStart, requestEnd;
  clock_gettime(CLOCK_REALTIME, &requestStart);
#endif

// Control granularity: map matrices individually or all at once
#ifdef SEPARATE_SCOPE
#pragma omp target data device(BIGPULP_MEMCPY) map(to: B [0:K * N])
{
#pragma omp target data device(BIGPULP_MEMCPY) map(tofrom: C [0:M * N])
{
#pragma omp target device(BIGPULP_MEMCPY) map(to: A [0:M * K])
#else
#pragma omp target device(BIGPULP_MEMCPY) map(tofrom: C [0:M * N]) map(to: A [0:M * K], B [0:K * N])
#endif
// clang-format on
  {
    // Compute memory allocation block sizes if required
    int i, m, n, k;
    float temp;
#ifdef BLOCKEDMM
    const int L1_b = 80 * 1024;
    const int L1_flt = L1_b / sizeof(float);
    const int blockSize = sqrt(L1_flt / 3);
    int limitM, limitN, limitK;
    int bm, bn, bk;
#else
    int bm=0, bn=0, bk=0;
    int limitM=M, limitN=N, limitK=K;
#endif


//#pragma omp parallel for num_threads(8) private(bn, bk, bm, m, n, k)
//#pragma omp parallel num_threads(8)
  {
#ifdef BLOCKEDMM
    for(bn=0; bn<N && N-bn-1 != 0; bn+=my_min(N-bn-1, blockSize)) {
      for(bk=0; bk<K && K-bk-1 != 0; bk+=my_min(K-bk-1, blockSize)) {
        for (bm=0; bm<M && M-bm-1 != 0; bm+=my_min(M-bm-1, blockSize)) {
          limitM = my_min(M-bm, blockSize);
          limitN = my_min(N-bn, blockSize);
          limitK = my_min(K-bk, blockSize);
#endif
#pragma omp parallel for collapse(2) private(m, n, k) num_threads(8)
          for(m=bm; m<bm+limitM; m++){
            for(n=bn; n<bn+limitN; n++){
              for(k=bk; k<bk+limitK; k++){
                C[m*N+n] += A[m*K+k]*B[k*N+n];
              }
            }
          }
#ifdef BLOCKEDMM
        }
      }
    }
#endif
  }
  }

#ifdef SEPARATE_SCOPE
}
}
#endif
#ifdef TIMELAYERS
  clock_gettime(CLOCK_REALTIME, &requestEnd);
  double accum = (requestEnd.tv_sec - requestStart.tv_sec) +
                 (requestEnd.tv_nsec - requestStart.tv_nsec) / BILLION;
  printf("Time spent on layer: %lf\n", accum);
#endif

#ifdef CORRECTNESS
  // Compare correctness.
  int errors = 0;
  int same = 0;
  for (int i = 0; i < M * N; i++) {
    if (fabs(C[i] - E_flt[i]) > 0.00001) {
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
  free(E_flt);
#endif
}

*/
void gemm_nt(int M, int N, int K, float ALPHA, float *A, int lda, float *B, int ldb, float *C,
             int ldc) {
  int i, j, k;
  //#pragma omp parallel for
  for (i = 0; i < M; ++i) {
    for (j = 0; j < N; ++j) {
      register float sum = 0;
      for (k = 0; k < K; ++k) {
        sum += ALPHA * A[i * lda + k] * B[j * ldb + k];
      }
      C[i * ldc + j] += sum;
    }
  }
}

void gemm_tn(int M, int N, int K, float ALPHA, float *A, int lda, float *B, int ldb, float *C,
             int ldc) {
  int i, j, k;
  //#pragma omp parallel for
  for (i = 0; i < M; ++i) {
    for (k = 0; k < K; ++k) {
      register float A_PART = ALPHA * A[k * lda + i];
      for (j = 0; j < N; ++j) {
        C[i * ldc + j] += A_PART * B[k * ldb + j];
      }
    }
  }
}

void gemm_tt(int M, int N, int K, float ALPHA, float *A, int lda, float *B, int ldb, float *C,
             int ldc) {
  int i, j, k;
  //#pragma omp parallel for
  for (i = 0; i < M; ++i) {
    for (j = 0; j < N; ++j) {
      register float sum = 0;
      for (k = 0; k < K; ++k) {
        sum += ALPHA * A[i + k * lda] * B[k + j * ldb];
      }
      C[i * ldc + j] += sum;
    }
  }
}

void gemm_cpu(int TA, int TB, int M, int N, int K, float ALPHA, float *A, int lda, float *B,
              int ldb, float BETA, float *C, int ldc) {
  // printf("cpu: TA=%d, TB=%d, M=%d, N=%d, K=%d, alpha=%f, lda=%d, ldb=%d, beta=%f, ldc=%d\n",TA,
  // TB, M, N, K, ALPHA, lda, ldb, BETA, ldc); printf("M*K+K*N+M*N=%d\n", M*K+K*N+M*N);
  int i, j;
  for (i = 0; i < M; ++i) {
    for (j = 0; j < N; ++j) {
      C[i * ldc + j] *= BETA;
    }
  }
  printf("Layer counter is set to %i\n", LAYER_COUNTER);
  if (!TA && !TB){
    if (LAYER_COUNTER == 0){
      gemm_zero(ALPHA, A, B, C);
    }
    else{
      gemm_nn(M, N, K, ALPHA, A, lda, B, ldb, C, ldc);
    }
  }
  else if (TA && !TB)
    gemm_tn(M, N, K, ALPHA, A, lda, B, ldb, C, ldc);
  else if (!TA && TB)
    gemm_nt(M, N, K, ALPHA, A, lda, B, ldb, C, ldc);
  else
    gemm_tt(M, N, K, ALPHA, A, lda, B, ldb, C, ldc);
}

#ifdef GPU

#include <math.h>

void gemm_gpu(int TA, int TB, int M, int N, int K, float ALPHA, float *A_gpu, int lda, float *B_gpu,
              int ldb, float BETA, float *C_gpu, int ldc) {
  cublasHandle_t handle = blas_handle();
  cudaError_t status =
      cublasSgemm(handle, (TB ? CUBLAS_OP_T : CUBLAS_OP_N), (TA ? CUBLAS_OP_T : CUBLAS_OP_N), N, M,
                  K, &ALPHA, B_gpu, ldb, A_gpu, lda, &BETA, C_gpu, ldc);
  check_error(status);
}

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

void time_gpu_random_matrix(int TA, int TB, int m, int k, int n) {
  float *a;
  if (!TA)
    a = random_matrix(m, k);
  else
    a = random_matrix(k, m);
  int lda = (!TA) ? k : m;
  float *b;
  if (!TB)
    b = random_matrix(k, n);
  else
    b = random_matrix(n, k);
  int ldb = (!TB) ? n : k;

  float *c = random_matrix(m, n);
  int i;
  clock_t start = clock(), end;
  for (i = 0; i < 32; ++i) {
    gemm_gpu(TA, TB, m, n, k, 1, a, lda, b, ldb, 1, c, n);
  }
  end = clock();
  printf("Matrix Multiplication %dx%d * %dx%d, TA=%d, TB=%d: %lf s\n", m, k, k, n, TA, TB,
         (float)(end - start) / CLOCKS_PER_SEC);
  free(a);
  free(b);
  free(c);
}

void time_gpu(int TA, int TB, int m, int k, int n) {
  int iter = 10;
  float *a = random_matrix(m, k);
  float *b = random_matrix(k, n);

  int lda = (!TA) ? k : m;
  int ldb = (!TB) ? n : k;

  float *c = random_matrix(m, n);

  float *a_cl = cuda_make_array(a, m * k);
  float *b_cl = cuda_make_array(b, k * n);
  float *c_cl = cuda_make_array(c, m * n);

  int i;
  clock_t start = clock(), end;
  for (i = 0; i < iter; ++i) {
    gemm_gpu(TA, TB, m, n, k, 1, a_cl, lda, b_cl, ldb, 1, c_cl, n);
    cudaThreadSynchronize();
  }
  double flop = ((double)m) * n * (2. * k + 2.) * iter;
  double gflop = flop / pow(10., 9);
  end = clock();
  double seconds = sec(end - start);
  printf("Matrix Multiplication %dx%d * %dx%d, TA=%d, TB=%d: %lf s, %lf GFLOPS\n", m, k, k, n, TA,
         TB, seconds, gflop / seconds);
  cuda_free(a_cl);
  cuda_free(b_cl);
  cuda_free(c_cl);
  free(a);
  free(b);
  free(c);
}

void test_gpu_accuracy(int TA, int TB, int m, int k, int n) {
  srand(0);
  float *a;
  if (!TA)
    a = random_matrix(m, k);
  else
    a = random_matrix(k, m);
  int lda = (!TA) ? k : m;
  float *b;
  if (!TB)
    b = random_matrix(k, n);
  else
    b = random_matrix(n, k);
  int ldb = (!TB) ? n : k;

  float *c = random_matrix(m, n);
  float *c_gpu = random_matrix(m, n);
  memset(c, 0, m * n * sizeof(float));
  memset(c_gpu, 0, m * n * sizeof(float));
  int i;
  // pm(m,k,b);
  gemm_gpu(TA, TB, m, n, k, 1, a, lda, b, ldb, 1, c_gpu, n);
  // printf("GPU\n");
  // pm(m, n, c_gpu);

  gemm_cpu(TA, TB, m, n, k, 1, a, lda, b, ldb, 1, c, n);
  // printf("\n\nCPU\n");
  // pm(m, n, c);
  double sse = 0;
  for (i = 0; i < m * n; ++i) {
    // printf("%f %f\n", c[i], c_gpu[i]);
    sse += pow(c[i] - c_gpu[i], 2);
  }
  printf("Matrix Multiplication %dx%d * %dx%d, TA=%d, TB=%d: %g SSE\n", m, k, k, n, TA, TB,
         sse / (m * n));
  free(a);
  free(b);
  free(c);
  free(c_gpu);
}

int test_gpu_blas() {
  /*
     test_gpu_accuracy(0,0,10,576,75);

     test_gpu_accuracy(0,0,17,10,10);
     test_gpu_accuracy(1,0,17,10,10);
     test_gpu_accuracy(0,1,17,10,10);
     test_gpu_accuracy(1,1,17,10,10);

     test_gpu_accuracy(0,0,1000,10,100);
     test_gpu_accuracy(1,0,1000,10,100);
     test_gpu_accuracy(0,1,1000,10,100);
     test_gpu_accuracy(1,1,1000,10,100);

     test_gpu_accuracy(0,0,10,10,10);

     time_gpu(0,0,64,2916,363);
     time_gpu(0,0,64,2916,363);
     time_gpu(0,0,64,2916,363);
     time_gpu(0,0,192,729,1600);
     time_gpu(0,0,384,196,1728);
     time_gpu(0,0,256,196,3456);
     time_gpu(0,0,256,196,2304);
     time_gpu(0,0,128,4096,12544);
     time_gpu(0,0,128,4096,4096);
   */
  time_gpu(0, 0, 64, 75, 12544);
  time_gpu(0, 0, 64, 75, 12544);
  time_gpu(0, 0, 64, 75, 12544);
  time_gpu(0, 0, 64, 576, 12544);
  time_gpu(0, 0, 256, 2304, 784);
  time_gpu(1, 1, 2304, 256, 784);
  time_gpu(0, 0, 512, 4608, 196);
  time_gpu(1, 1, 4608, 512, 196);

  return 0;
}
#endif
