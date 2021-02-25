
layer = ["0", "2", "4", "6", "8", "10", "12", "13", "14", "15", "18", "21", "22"]
M = ["16", "32", "64", "128", "256", "512", "1024", "256", "512", "255", "128", "256", "255"]
N = ["173056", "43264", "10816","2704","676", "169", "169", "169", "169", "169", "169", "676", "676"]
K = ["27", "144", "288", "576", "1152", "2304", "4608", "1024", "2304", "512", "256", "3456", "256"]

print('#include <hero-target.h>\n')
print("extern int LAYER_COUNTER;\n")

for i in range(len(layer)):

	print("void gemm_" + layer[i] + "(float ALPHA, float *A, float *B, float *C){\n\
  const int M = " + M[i] + ";\n\
  const int N = " + N[i] + ";\n\
  const int K = " + K[i] + ";\n\
  __host float (*matA)[K] = (__host float(*)[K]) A;\n\
  __host float (*matB)[N] = (__host float(*)[N]) B;\n\
  __host float (*matC)[N] = (__host float(*)[N]) C;\n\
  #pragma omp target data device(BIGPULP_MEMCPY) map(to: matB[0:" + K[i] + "][0:" + N[i] + "])\n\
  {\n\
    #pragma omp target data device(BIGPULP_MEMCPY) map(to: matA[0:" + M[i] + "][0:" + K[i] + "])\n\
    {\n\
      #pragma omp target device(BIGPULP_MEMCPY) map(tofrom: matC[0:" + M[i] + "][0:" + N[i] + "])\n\
      {\n\
        #pragma omp parallel for num_threads(8) schedule(static, 1)\n\
        for(int m = 0; m < M; ++m){\n\
          for(int k = 0; k < K; ++k){\n\
            float temp = ALPHA*matA[m][k];\n\
            for(int n = 0; n < N; ++n){\n\
              matC[m][n] +=temp*matB[k][n];\n\
            }\n\
          }\n\
        }\n\
      }\n\
    }\n\
  }\n\
  LAYER_COUNTER=" + layer[(i+1)%len(layer)] + ";\n\
}\n\n")
