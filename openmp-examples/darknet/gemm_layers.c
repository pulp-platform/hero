void gemm_0(float ALPHA, float *A, float *B, float *C){
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
      {
        //#pragma omp parallel for private(m, n, k, temp) num_threads(8) schedule(static, 1)
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


void gemm_2(float ALPHA, float *A, float *B, float *C){
  const int M = 32;
  const int N = 43264;
  const int K = 144;
  int m,n,k;
  float (*matA)[K] = (float(*)[K]) A;
  float (*matB)[N] = (float(*)[N]) B;
  float (*matC)[N] = (float(*)[N]) C;
  float temp;
  #pragma omp target data device(BIGPULP_MEMCPY) map(to: matB[0:144][0:43264])
  {
    #pragma omp target data device(BIGPULP_MEMCPY) map(to: matA[0:32][0:144])
    {
      #pragma omp target device(BIGPULP_MEMCPY) map(tofrom: matC[0:32][0:43264])
      {
        //#pragma omp parallel for private(m, n, k, temp) num_threads(8) schedule(static, 1)
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
  LAYER_COUNTER=4;
}


void gemm_4(float ALPHA, float *A, float *B, float *C){
  const int M = 64;
  const int N = 10816;
  const int K = 288;
  int m,n,k;
  float (*matA)[K] = (float(*)[K]) A;
  float (*matB)[N] = (float(*)[N]) B;
  float (*matC)[N] = (float(*)[N]) C;
  float temp;
  #pragma omp target data device(BIGPULP_MEMCPY) map(to: matB[0:288][0:10816])
  {
    #pragma omp target data device(BIGPULP_MEMCPY) map(to: matA[0:64][0:288])
    {
      #pragma omp target device(BIGPULP_MEMCPY) map(tofrom: matC[0:64][0:10816])
      {
        //#pragma omp parallel for private(m, n, k, temp) num_threads(8) schedule(static, 1)
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
  LAYER_COUNTER=6;
}


void gemm_6(float ALPHA, float *A, float *B, float *C){
  const int M = 128;
  const int N = 2704;
  const int K = 576;
  int m,n,k;
  float (*matA)[K] = (float(*)[K]) A;
  float (*matB)[N] = (float(*)[N]) B;
  float (*matC)[N] = (float(*)[N]) C;
  float temp;
  #pragma omp target data device(BIGPULP_MEMCPY) map(to: matB[0:576][0:2704])
  {
    #pragma omp target data device(BIGPULP_MEMCPY) map(to: matA[0:128][0:576])
    {
      #pragma omp target device(BIGPULP_MEMCPY) map(tofrom: matC[0:128][0:2704])
      {
        //#pragma omp parallel for private(m, n, k, temp) num_threads(8) schedule(static, 1)
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
  LAYER_COUNTER=8;
}


void gemm_8(float ALPHA, float *A, float *B, float *C){
  const int M = 256;
  const int N = 676;
  const int K = 1152;
  int m,n,k;
  float (*matA)[K] = (float(*)[K]) A;
  float (*matB)[N] = (float(*)[N]) B;
  float (*matC)[N] = (float(*)[N]) C;
  float temp;
  #pragma omp target data device(BIGPULP_MEMCPY) map(to: matB[0:1152][0:676])
  {
    #pragma omp target data device(BIGPULP_MEMCPY) map(to: matA[0:256][0:1152])
    {
      #pragma omp target device(BIGPULP_MEMCPY) map(tofrom: matC[0:256][0:676])
      {
        //#pragma omp parallel for private(m, n, k, temp) num_threads(8) schedule(static, 1)
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
  LAYER_COUNTER=10;
}


void gemm_10(float ALPHA, float *A, float *B, float *C){
  const int M = 512;
  const int N = 169;
  const int K = 2304;
  int m,n,k;
  float (*matA)[K] = (float(*)[K]) A;
  float (*matB)[N] = (float(*)[N]) B;
  float (*matC)[N] = (float(*)[N]) C;
  float temp;
  #pragma omp target data device(BIGPULP_MEMCPY) map(to: matB[0:2304][0:169])
  {
    #pragma omp target data device(BIGPULP_MEMCPY) map(to: matA[0:512][0:2304])
    {
      #pragma omp target device(BIGPULP_MEMCPY) map(tofrom: matC[0:512][0:169])
      {
        //#pragma omp parallel for private(m, n, k, temp) num_threads(8) schedule(static, 1)
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
  LAYER_COUNTER=12;
}


void gemm_12(float ALPHA, float *A, float *B, float *C){
  const int M = 1024;
  const int N = 169;
  const int K = 4608;
  int m,n,k;
  float (*matA)[K] = (float(*)[K]) A;
  float (*matB)[N] = (float(*)[N]) B;
  float (*matC)[N] = (float(*)[N]) C;
  float temp;
  #pragma omp target data device(BIGPULP_MEMCPY) map(to: matB[0:4608][0:169])
  {
    #pragma omp target data device(BIGPULP_MEMCPY) map(to: matA[0:1024][0:4608])
    {
      #pragma omp target device(BIGPULP_MEMCPY) map(tofrom: matC[0:1024][0:169])
      {
        //#pragma omp parallel for private(m, n, k, temp) num_threads(8) schedule(static, 1)
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
  LAYER_COUNTER=13;
}


void gemm_13(float ALPHA, float *A, float *B, float *C){
  const int M = 256;
  const int N = 169;
  const int K = 1024;
  int m,n,k;
  float (*matA)[K] = (float(*)[K]) A;
  float (*matB)[N] = (float(*)[N]) B;
  float (*matC)[N] = (float(*)[N]) C;
  float temp;
  #pragma omp target data device(BIGPULP_MEMCPY) map(to: matB[0:1024][0:169])
  {
    #pragma omp target data device(BIGPULP_MEMCPY) map(to: matA[0:256][0:1024])
    {
      #pragma omp target device(BIGPULP_MEMCPY) map(tofrom: matC[0:256][0:169])
      {
        //#pragma omp parallel for private(m, n, k, temp) num_threads(8) schedule(static, 1)
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
  LAYER_COUNTER=14;
}


void gemm_14(float ALPHA, float *A, float *B, float *C){
  const int M = 512;
  const int N = 169;
  const int K = 2304;
  int m,n,k;
  float (*matA)[K] = (float(*)[K]) A;
  float (*matB)[N] = (float(*)[N]) B;
  float (*matC)[N] = (float(*)[N]) C;
  float temp;
  #pragma omp target data device(BIGPULP_MEMCPY) map(to: matB[0:2304][0:169])
  {
    #pragma omp target data device(BIGPULP_MEMCPY) map(to: matA[0:512][0:2304])
    {
      #pragma omp target device(BIGPULP_MEMCPY) map(tofrom: matC[0:512][0:169])
      {
        //#pragma omp parallel for private(m, n, k, temp) num_threads(8) schedule(static, 1)
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
  LAYER_COUNTER=15;
}


void gemm_15(float ALPHA, float *A, float *B, float *C){
  const int M = 255;
  const int N = 169;
  const int K = 512;
  int m,n,k;
  float (*matA)[K] = (float(*)[K]) A;
  float (*matB)[N] = (float(*)[N]) B;
  float (*matC)[N] = (float(*)[N]) C;
  float temp;
  #pragma omp target data device(BIGPULP_MEMCPY) map(to: matB[0:512][0:169])
  {
    #pragma omp target data device(BIGPULP_MEMCPY) map(to: matA[0:255][0:512])
    {
      #pragma omp target device(BIGPULP_MEMCPY) map(tofrom: matC[0:255][0:169])
      {
        //#pragma omp parallel for private(m, n, k, temp) num_threads(8) schedule(static, 1)
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
  LAYER_COUNTER=18;
}


void gemm_18(float ALPHA, float *A, float *B, float *C){
  const int M = 128;
  const int N = 169;
  const int K = 256;
  int m,n,k;
  float (*matA)[K] = (float(*)[K]) A;
  float (*matB)[N] = (float(*)[N]) B;
  float (*matC)[N] = (float(*)[N]) C;
  float temp;
  #pragma omp target data device(BIGPULP_MEMCPY) map(to: matB[0:256][0:169])
  {
    #pragma omp target data device(BIGPULP_MEMCPY) map(to: matA[0:128][0:256])
    {
      #pragma omp target device(BIGPULP_MEMCPY) map(tofrom: matC[0:128][0:169])
      {
        //#pragma omp parallel for private(m, n, k, temp) num_threads(8) schedule(static, 1)
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
  LAYER_COUNTER=21;
}


void gemm_21(float ALPHA, float *A, float *B, float *C){
  const int M = 256;
  const int N = 676;
  const int K = 3456;
  int m,n,k;
  float (*matA)[K] = (float(*)[K]) A;
  float (*matB)[N] = (float(*)[N]) B;
  float (*matC)[N] = (float(*)[N]) C;
  float temp;
  #pragma omp target data device(BIGPULP_MEMCPY) map(to: matB[0:3456][0:676])
  {
    #pragma omp target data device(BIGPULP_MEMCPY) map(to: matA[0:256][0:3456])
    {
      #pragma omp target device(BIGPULP_MEMCPY) map(tofrom: matC[0:256][0:676])
      {
        //#pragma omp parallel for private(m, n, k, temp) num_threads(8) schedule(static, 1)
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
  LAYER_COUNTER=22;
}


void gemm_22(float ALPHA, float *A, float *B, float *C){
  const int M = 255;
  const int N = 676;
  const int K = 256;
  int m,n,k;
  float (*matA)[K] = (float(*)[K]) A;
  float (*matB)[N] = (float(*)[N]) B;
  float (*matC)[N] = (float(*)[N]) C;
  float temp;
  #pragma omp target data device(BIGPULP_MEMCPY) map(to: matB[0:256][0:676])
  {
    #pragma omp target data device(BIGPULP_MEMCPY) map(to: matA[0:255][0:256])
    {
      #pragma omp target device(BIGPULP_MEMCPY) map(tofrom: matC[0:255][0:676])
      {
        //#pragma omp parallel for private(m, n, k, temp) num_threads(8) schedule(static, 1)
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
  LAYER_COUNTER=0;
}


