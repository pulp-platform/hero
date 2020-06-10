#include "gemm.h"
#include "utils.h"
#include "cuda.h"
#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <hero-target.h>
#include <time.h>
#include <dmatransfer.h>

#define BILLION 1E9

void gemm_bin(int M, int N, int K, float ALPHA, 
        char  *A, int lda, 
        float *B, int ldb,
        float *C, int ldc)
{
    int i,j,k;
    for(i = 0; i < M; ++i){
        for(k = 0; k < K; ++k){
            char A_PART = A[i*lda+k];
            if(A_PART){
                for(j = 0; j < N; ++j){
                    C[i*ldc+j] += B[k*ldb+j];
                }
            } else {
                for(j = 0; j < N; ++j){
                    C[i*ldc+j] -= B[k*ldb+j];
                }
            }
        }
    }
}

float *random_matrix(int rows, int cols)
{
    int i;
    float *m = calloc(rows*cols, sizeof(float));
    for(i = 0; i < rows*cols; ++i){
        m[i] = (float)rand()/RAND_MAX;
    }
    return m;
}

void time_random_matrix(int TA, int TB, int m, int k, int n)
{
    float *a;
    if(!TA) a = random_matrix(m,k);
    else a = random_matrix(k,m);
    int lda = (!TA)?k:m;
    float *b;
    if(!TB) b = random_matrix(k,n);
    else b = random_matrix(n,k);
    int ldb = (!TB)?n:k;

    float *c = random_matrix(m,n);
    int i;
    clock_t start = clock(), end;
    for(i = 0; i<10; ++i){
        gemm_cpu(TA,TB,m,n,k,1,a,lda,b,ldb,1,c,n);
    }
    end = clock();
    printf("Matrix Multiplication %dx%d * %dx%d, TA=%d, TB=%d: %lf ms\n",m,k,k,n, TA, TB, (float)(end-start)/CLOCKS_PER_SEC);
    free(a);
    free(b);
    free(c);
}


void gemm(int TA, int TB, int M, int N, int K, float ALPHA, 
        float *A, int lda, 
        float *B, int ldb,
        float BETA,
        float *C, int ldc)
{
    gemm_cpu( TA,  TB,  M, N, K, ALPHA,A,lda, B, ldb,BETA,C,ldc);
}

void gemm_nn(int M, int N, int K, float ALPHA, 
        float *A, int lda, 
        float *B, int ldb,
        float *C, int ldc)
{
    int i,j,k;
		//printf("%i,%i,%i\n",M,N,K);
		if(0)
		//if((M==16)&&(N==173056)&&(K=27))	// 00
		//if((M==32)&&(N==43264)&&(K=144))	// 02
		//if((M==64)&&(N==10816)&&(K=288))	// 04
		//if((M==128)&&(N==2704)&&(K=576))	// 06
		//if((M==256)&&(N==676)&&(K=1152))	// 08
		//if((M==512)&&(N==169)&&(K=2304))	// 10/14
		//if((M==1024)&&(N==169)&&(K=4608))	// 12
		//if((M==256)&&(N==169)&&(K=1024))	// 13
		//if((M==255)&&(N==169)&&(K=512))		// 15
		//if((M==128)&&(N==169)&&(K=256))		// 18
		//if((M==256)&&(N==676)&&(K=3456))	// 21
		//if((M==255)&&(N==676)&&(K=256))		// 22
		//if(((M==255)&&(N==169)&&(K=512))||((M==128)&&(N==169)&&(K=256)))		// 15 and 18
		//if(((M==255)&&(N==169)&&(K=512))||((M==255)&&(N==676)&&(K=256)))		// 15 and 22
		//if(((M==128)&&(N==169)&&(K=256))||((M==255)&&(N==676)&&(K=256)))		// 18 and 22
		//if(((M==128)&&(N==169)&&(K=256))||((M==255)&&(N==676)&&(K=256)||((M==255)&&(N==169)&&(K=512))))		// 15, 18 and 22
		{
      // Offloading
			printf("Accelerating Layer\n");
			printf("Address of C is %p\n", C);
			printf("Sum is %i\n", M*N+M*K+K*N);
			struct timespec requestStart, requestEnd;
			clock_gettime(CLOCK_REALTIME, &requestStart);

      //#pragma omp target device(BIGPULP_MEMCPY) map(tofrom: C[0:M*N]) map(to: A[0:M*K], B[0:K*N], ALPHA, i, j, k) 
      #pragma omp target data map(tofrom: C[0:M*N]) map(to: A[0:M*K], B[0:K*N]) 
			{
      #pragma omp target //device(BIGPULP_MEMCPY)
			{
			float* spm = alloc_spm();
			if(spm == NULL){
				printf("SPM allocation failed!\n");
			}
			else{
				printf("SPM at address %p\n", spm);
			}
			int rows_per_chunk = M;

			float* B_spm = spm;
			float* A_spm = spm + K*N;
			float* C_spm = spm + K*N + K*rows_per_chunk;
			/*
			if(spm + K*N + M*K + M*N > 0x10020000){
				printf("Memory allocation larger than L1!\n");
			}
			else{
				printf("Highest address is at %p\n", spm + K*N + M*K + M*N);
			}
			*/

			memcpy_to_spm(B_spm, ((float*) B), K*N);

			int row = 0;
			
			while (row < M) {         
			//while (row < 1) {         
				int chunk_rows = (rows_per_chunk < M - row) ? rows_per_chunk : (M - row);         
				memcpy_to_spm(A_spm, ((float*) A) + row*K, chunk_rows*K);         
				memcpy_to_spm(C_spm, ((float*) C) + row*N, chunk_rows*N);         
				dma_flush();

				#pragma omp parallel for collapse(2) num_threads(8) firstprivate(ALPHA) private(i, j, k)
				for (i = 0; i < chunk_rows; i++) {
					for (j = 0; j < N; j++) {
						for (k = 0; k < K; ++k) {
							C_spm[i*N+j] += ALPHA * A_spm[i*K+k] * B_spm[k*N+j];
						}
					}
				}

				memcpy_from_spm(((float*) C) + row*N, C_spm, chunk_rows*N);
				dma_flush();
				row += rows_per_chunk;
			}

			dealloc_spm(spm);
			}
			}


			
			/*
#pragma omp parallel for num_threads(8) private(i,j,k)
			for(i = 0; i < M; ++i){
				for(k = 0; k < K; ++k){
					register float A_PART = ALPHA*A[i*lda+k];
					for(j = 0; j < N; ++j){
			  			C[i*ldc+j] += A_PART*B[k*ldb+j];
			  		}
			  	}    
			  }
			}

			*/

			clock_gettime(CLOCK_REALTIME, &requestEnd);
			double accum = ( requestEnd.tv_sec - requestStart.tv_sec )
				  + ( requestEnd.tv_nsec - requestStart.tv_nsec )
					  / BILLION;
			printf( "Time spent on layer: %lf\n", accum );
      // Store the output of C in case we want to compare correctness.
			FILE *fp = fopen("C_dump", "w+");
			for(i=0;i<M*N;i++){
				fprintf(fp, "%f\n", C[i]);
			}
			fclose(fp);
			
		} 

		else if(0&&(M==128)&&(N==169)&&(K=256)){		// Layer 18 float check

			int i, len=16;

			float a[len];
			float b[len];
			float c[len];
			float r[len];

			for(i = 0; i < len; i++)
			{	
				a[i] = i + 0.5;
				b[i] = i + 1.5;
				c[i] = i + 2.5;
				r[i] = a[i]*b[i] + c[i];
			}

      #pragma omp target device(BIGPULP_MEMCPY) map(tofrom: c[0:len]) map(to: a[0:len], b[0:len], i, len)
		 	{
				float* spm = alloc_spm();
				float* a_spm = spm;
				float* b_spm = a_spm + len;
			  float* c_spm = b_spm + len;

				memcpy_to_spm(a_spm, a, len);
				memcpy_to_spm(b_spm, b, len);
				memcpy_to_spm(c_spm, c, len);
				dma_flush();
				
				#pragma omp parallel for num_threads(8) private(i)
				for(i = 0; i < len; i++){
					c_spm[i] += a_spm[i]*b_spm[i];
				}

				memcpy_from_spm(c, c_spm, len);
				dma_flush();

				dealloc_spm(spm);
			}	

		for(i = 0; i < len; i++){
			printf("c[%d] is %f, expected: %f\n", i, c[i], r[i]);
			if(c[i] != r[i]){
				printf("\n\n\n!!!ERROR DETECTED!!!\n\n\n");
			}
		}


		}
		else if((M==128)&&(N==169)&&(K=256)){		// Layer 18 rewrite matrices
			printf("Layer 18!\n");
			
			/*	
			M = 1;
			K = 2;
			N = 6;
			int A_flt[M*K], B_flt[K*N], C_flt[M*N], E_flt[M*N];

			printf("A_flt:\n");
			for(int m = 0; m < M; m++){
				for(int k = 0; k < K; k++){
					A_flt[m*K+k] = m*K+k;
					printf("%d,",A_flt[m*K+k]);
				}
				printf("\n");
			}

			printf("B_flt:\n");
			for(int k = 0; k < K; k++){
				for(int n = 0; n < N; n++){
					B_flt[k*N+n] = k*N+n;
					printf("%d,",B_flt[k*N+n]);
				}
				printf("\n");
			}


			printf("C_flt:\n");
			for(int m = 0; m < M; m++){
				for(int n = 0; n < N; n++){
					C_flt[m*N+n] = 0.0;
					printf("%d,",C_flt[m*N+n]);
					E_flt[m*N+n] = 0.0;
				}
				printf("\n");
			}
			
			
			*/
			float* E_flt= (float*) malloc(M*N*sizeof(float));
			for(int m = 0; m < M; m++){
				for(int n = 0; n < N; n++){
					E_flt[m*N+n] = 0.0;
					for(int k = 0; k < K; k++){
						E_flt[m*N+n] += A[m*K+k]*B[k*N+n];
					}
				}
			}





			int l1 = 80;
			//int col = l1*256/(2*K+1);
			int col = (l1*256-K)/(K+1);

			int used_mem = K*sizeof(float)+col*K*sizeof(float)+col*sizeof(float);
			printf("Used memory: %d\n", used_mem);

			int exp_iter = M*N/col;
			printf("Expected iterations: %d\n", exp_iter);
			

			struct timespec requestStart, requestEnd;
			clock_gettime(CLOCK_REALTIME, &requestStart);
      #pragma omp target device(BIGPULP_MEMCPY) map(tofrom: C[0:M*N]) map(to: A[0:M*K], B[0:K*N]) 
			{

			int n, lim;
			int* spm = alloc_spm();

			float* A_spm = spm;
			float* B_spm = A_spm + K;
			float* C_spm;


			// Load one row of A and multiple columns of B and write the partial results in C
			for(int m = 0; m < M; m++){

				// Initiate DMA transfer for one row of A
				memcpy_to_spm(A_spm, A+m*K, K);
						
				// Check amount of columns in order not to overshoot B
				n = 0;
				while(n < N){
					if(N < n+col){
						lim = N - n;
					}
					else{
						lim = col;
					}
					
					// DMA transfers for columns in B and entries in C
					C_spm = B_spm + lim*K;
					memcpy_to_spm(C_spm, C+m*N+n, lim);
					for(k = 0; k < K; k++){
						memcpy_to_spm(B_spm+k*lim, B+k*N+n, lim);
					}
					dma_flush();

	
					
					/*
					printf("Address of A_spm: %p %p\n", A_spm);
					printf("Address of B_spm: %p %p\n", B_spm);

					printf("A_spm:\n");
					for(int i = 0; i < M; i++){
						for(int j = 0; j < K; j++){
							printf("%d %d,", A_spm[i*K+j]);
						}
						printf("\n");
					}
					printf("\n");



					printf("B_spm:\n");
					for(int i = 0; i < K; i++){
						for(int j = 0; j < lim; j++){
							printf("%d %d,", B_spm[i*lim+j]);
						}
						printf("\n");
					}
					printf("\n");
					*/
					

					// Do the computation
					#pragma omp parallel for collapse(2) num_threads(8) 
					for(int c = 0; c < lim; c++){
						for(int k = 0; k < K; k++){
							C_spm[c] += A_spm[k]*B_spm[k*lim+c];
						}
					}

					// Transfer back the entries of C
					memcpy_from_spm(C+m*N+n, C_spm, lim);
					dma_flush();
					
					n += lim;
				}
			}
			dma_flush();
			dealloc_spm(spm);
			}
			clock_gettime(CLOCK_REALTIME, &requestEnd);
			double accum = ( requestEnd.tv_sec - requestStart.tv_sec )
				  + ( requestEnd.tv_nsec - requestStart.tv_nsec )
					  / BILLION;
			printf( "Time spent on layer: %lf\n", accum );
		
			// Compare correctness.
			int error = 0;
			for(i=0;i<M*N;i++){
				//printf("Output: %d, expected: %d\n", C_flt[i], E_flt[i]);
				if(fabs(C[i] - E_flt[i]) > 0.00001){
					printf("ERROR: Output: %f, expected: %f\n", C[i], E_flt[i]);
					error = 1;
				}
			}
			if(!error){
				printf("Computation successful!\n");
			}
			free(E_flt);

			// Store the output of C in case we want to compare correctness.
			FILE *fp = fopen("18_C_current_dump", "w+");
			for(i=0;i<M*N;i++){
				fprintf(fp, "%f\n", C[i]);
			}
			fclose(fp);

			printf("After dumping C\n");


		}	
		else if(0&&(M==128)&&(N==169)&&(K=256)){		// 18
			// No offloading
			for(i = 0; i < M; ++i){
				for(k = 0; k < K; ++k){
					register float A_PART = ALPHA*A[i*lda+k];
					for(j = 0; j < N; ++j){
						C[i*ldc+j] += A_PART*B[k*ldb+j];
					}
				}   
			}
			// Store the output of C in case we want to compare correctness.
			FILE *fp = fopen("18_C_gold_dump", "w+");
			for(i=0;i<M*N;i++){
				fprintf(fp, "%f\n", C[i]);
			}
			fclose(fp);

		}
		else if(0&&(M==128)&&(N==169)&&(K=256)){		// Layer 18
			printf("Layer 18!\n");
			int l1 = 128;
			int col = l1*256/(2*K+1);

			int c, m, n, k, lim;
      #pragma omp target device(BIGPULP_MEMCPY) map(tofrom: C[0:M*N]) map(to: A[0:M*K], B[0:K*N], c, m, n, k, lim) 
			{

			float* spm = alloc_spm();

			float* A_spm = spm;
			float* B_spm = A_spm + M;
			float* C_spm;

			// Load one row of A and multiple columns of B and write the partial results in C
			for(m = 0; m < M; m++){

				// Initiate DMA transfer for one row of A
				memcpy_to_spm(A_spm, A+m*M, M);
						
				// Check amount of columns in order not to overshoot B
				n = 0;
				while(n < N){
					if(N < n+col){
						lim = N - n;
					}
					else{
						lim = col;
					}
					
					// DMA transfers for columns in B and entries in C
					C_spm = B_spm + lim*K;
					memcpy_to_spm(C_spm, C+m*N+n, lim);
					for(k = 0; k < K; k++){
						memcpy_to_spm(B_spm, B+k*N+n, lim);
					}
					dma_flush();

					// Do the computation
					#pragma omp parallel for collapse(2) num_threads(8) private(c, k)
					for(c = 0; c < lim; c++){
						for(k = 0; k < K; k++){
							C_spm[c] += A_spm[k]*B_spm[k*lim+c];
						}
					}

					// Transfer back the entries of C
					memcpy_from_spm(C+m*N+n, C_spm, lim);
					dma_flush();
					
					n += col;
				}
			}
			dma_flush();
			dealloc_spm(spm);
			}
			// Store the output of C in case we want to compare correctness.
			FILE *fp = fopen("18_C_new_dump", "w+");
			for(i=0;i<M*N;i++){
				fprintf(fp, "%f\n", C[i]);
			}
			fclose(fp);
		}	
		else if(0&&(M==128)&&(N==169)&&(K=256)){		// 18
			// No offloading
			for(i = 0; i < M; ++i){
				for(k = 0; k < K; ++k){
					register float A_PART = ALPHA*A[i*lda+k];
					for(j = 0; j < N; ++j){
						C[i*ldc+j] += A_PART*B[k*ldb+j];
					}
				}   
			}
			// Store the output of C in case we want to compare correctness.
			FILE *fp = fopen("18_C_gold_dump", "w+");
			for(i=0;i<M*N;i++){
				fprintf(fp, "%f\n", C[i]);
			}
			fclose(fp);

		}

		else{
      // No offloading
			for(i = 0; i < M; ++i){
				for(k = 0; k < K; ++k){
					register float A_PART = ALPHA*A[i*lda+k];
					for(j = 0; j < N; ++j){
						C[i*ldc+j] += A_PART*B[k*ldb+j];
					}
				}   
			}
		}
}

void gemm_nt(int M, int N, int K, float ALPHA, 
        float *A, int lda, 
        float *B, int ldb,
        float *C, int ldc)
{
    int i,j,k;
    //#pragma omp parallel for
    for(i = 0; i < M; ++i){
        for(j = 0; j < N; ++j){
            register float sum = 0;
            for(k = 0; k < K; ++k){
                sum += ALPHA*A[i*lda+k]*B[j*ldb + k];
            }
            C[i*ldc+j] += sum;
        }
    }
}

void gemm_tn(int M, int N, int K, float ALPHA, 
        float *A, int lda, 
        float *B, int ldb,
        float *C, int ldc)
{
    int i,j,k;
    //#pragma omp parallel for
    for(i = 0; i < M; ++i){
        for(k = 0; k < K; ++k){
            register float A_PART = ALPHA*A[k*lda+i];
            for(j = 0; j < N; ++j){
                C[i*ldc+j] += A_PART*B[k*ldb+j];
            }
        }
    }
}

void gemm_tt(int M, int N, int K, float ALPHA, 
        float *A, int lda, 
        float *B, int ldb,
        float *C, int ldc)
{
    int i,j,k;
    //#pragma omp parallel for
    for(i = 0; i < M; ++i){
        for(j = 0; j < N; ++j){
            register float sum = 0;
            for(k = 0; k < K; ++k){
                sum += ALPHA*A[i+k*lda]*B[k+j*ldb];
            }
            C[i*ldc+j] += sum;
        }
    }
}


void gemm_cpu(int TA, int TB, int M, int N, int K, float ALPHA, 
        float *A, int lda, 
        float *B, int ldb,
        float BETA,
        float *C, int ldc)
{
    //printf("cpu: TA=%d, TB=%d, M=%d, N=%d, K=%d, alpha=%f, lda=%d, ldb=%d, beta=%f, ldc=%d\n",TA, TB, M, N, K, ALPHA, lda, ldb, BETA, ldc);
		//printf("M*K+K*N+M*N=%d\n", M*K+K*N+M*N);
    int i, j;
    for(i = 0; i < M; ++i){
        for(j = 0; j < N; ++j){
            C[i*ldc + j] *= BETA;
        }
    }
    if(!TA && !TB)
        gemm_nn(M, N, K, ALPHA,A,lda, B, ldb,C,ldc);
    else if(TA && !TB)
        gemm_tn(M, N, K, ALPHA,A,lda, B, ldb,C,ldc);
    else if(!TA && TB)
        gemm_nt(M, N, K, ALPHA,A,lda, B, ldb,C,ldc);
    else
        gemm_tt(M, N, K, ALPHA,A,lda, B, ldb,C,ldc);
}

#ifdef GPU

#include <math.h>

void gemm_gpu(int TA, int TB, int M, int N, int K, float ALPHA, 
        float *A_gpu, int lda, 
        float *B_gpu, int ldb,
        float BETA,
        float *C_gpu, int ldc)
{
    cublasHandle_t handle = blas_handle();
    cudaError_t status = cublasSgemm(handle, (TB ? CUBLAS_OP_T : CUBLAS_OP_N), 
            (TA ? CUBLAS_OP_T : CUBLAS_OP_N), N, M, K, &ALPHA, B_gpu, ldb, A_gpu, lda, &BETA, C_gpu, ldc);
    check_error(status);
}

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

void time_gpu_random_matrix(int TA, int TB, int m, int k, int n)
{
    float *a;
    if(!TA) a = random_matrix(m,k);
    else a = random_matrix(k,m);
    int lda = (!TA)?k:m;
    float *b;
    if(!TB) b = random_matrix(k,n);
    else b = random_matrix(n,k);
    int ldb = (!TB)?n:k;

    float *c = random_matrix(m,n);
    int i;
    clock_t start = clock(), end;
    for(i = 0; i<32; ++i){
        gemm_gpu(TA,TB,m,n,k,1,a,lda,b,ldb,1,c,n);
    }
    end = clock();
    printf("Matrix Multiplication %dx%d * %dx%d, TA=%d, TB=%d: %lf s\n",m,k,k,n, TA, TB, (float)(end-start)/CLOCKS_PER_SEC);
    free(a);
    free(b);
    free(c);
}

void time_gpu(int TA, int TB, int m, int k, int n)
{
    int iter = 10;
    float *a = random_matrix(m,k);
    float *b = random_matrix(k,n);

    int lda = (!TA)?k:m;
    int ldb = (!TB)?n:k;

    float *c = random_matrix(m,n);

    float *a_cl = cuda_make_array(a, m*k);
    float *b_cl = cuda_make_array(b, k*n);
    float *c_cl = cuda_make_array(c, m*n);

    int i;
    clock_t start = clock(), end;
    for(i = 0; i<iter; ++i){
        gemm_gpu(TA,TB,m,n,k,1,a_cl,lda,b_cl,ldb,1,c_cl,n);
        cudaThreadSynchronize();
    }
    double flop = ((double)m)*n*(2.*k + 2.)*iter;
    double gflop = flop/pow(10., 9);
    end = clock();
    double seconds = sec(end-start);
    printf("Matrix Multiplication %dx%d * %dx%d, TA=%d, TB=%d: %lf s, %lf GFLOPS\n",m,k,k,n, TA, TB, seconds, gflop/seconds);
    cuda_free(a_cl);
    cuda_free(b_cl);
    cuda_free(c_cl);
    free(a);
    free(b);
    free(c);
}


void test_gpu_accuracy(int TA, int TB, int m, int k, int n)
{
    srand(0);
    float *a;
    if(!TA) a = random_matrix(m,k);
    else a = random_matrix(k,m);
    int lda = (!TA)?k:m;
    float *b;
    if(!TB) b = random_matrix(k,n);
    else b = random_matrix(n,k);
    int ldb = (!TB)?n:k;

    float *c = random_matrix(m,n);
    float *c_gpu = random_matrix(m,n);
    memset(c, 0, m*n*sizeof(float));
    memset(c_gpu, 0, m*n*sizeof(float));
    int i;
    //pm(m,k,b);
    gemm_gpu(TA,TB,m,n,k,1,a,lda,b,ldb,1,c_gpu,n);
    //printf("GPU\n");
    //pm(m, n, c_gpu);

    gemm_cpu(TA,TB,m,n,k,1,a,lda,b,ldb,1,c,n);
    //printf("\n\nCPU\n");
    //pm(m, n, c);
    double sse = 0;
    for(i = 0; i < m*n; ++i) {
        //printf("%f %f\n", c[i], c_gpu[i]);
        sse += pow(c[i]-c_gpu[i], 2);
    }
    printf("Matrix Multiplication %dx%d * %dx%d, TA=%d, TB=%d: %g SSE\n",m,k,k,n, TA, TB, sse/(m*n));
    free(a);
    free(b);
    free(c);
    free(c_gpu);
}

int test_gpu_blas()
{
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
    time_gpu(0,0,64,75,12544); 
    time_gpu(0,0,64,75,12544); 
    time_gpu(0,0,64,75,12544); 
    time_gpu(0,0,64,576,12544); 
    time_gpu(0,0,256,2304,784); 
    time_gpu(1,1,2304,256,784); 
    time_gpu(0,0,512,4608,196); 
    time_gpu(1,1,4608,512,196); 

    return 0;
}
#endif

