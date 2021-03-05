#!/usr/bin/env python3
#
# Copyright (c) 2020 ETH Zurich and University of Bologna
# Licensed under the Apache License, Version 2.0; see LICENSE.Apache-2.0 for details.
# SPDX-License-Identifier: Apache-2.0

layer = ["0", "2", "4", "6", "8", "10", "12", "13", "14", "15", "18", "21", "22"]
M = ["16", "32", "64", "128", "256", "512", "1024", "256", "512", "255", "128", "256", "255"]
N = ["173056", "43264", "10816","2704","676", "169", "169", "169", "169", "169", "169", "676", "676"]
K = ["27", "144", "288", "576", "1152", "2304", "4608", "1024", "2304", "512", "256", "3456", "256"]

with open('./gemm_layers.c', 'w') as f:
  f.write("""\
// Copyright (c) 2020 ETH Zurich and University of Bologna
// Licensed under the Apache License, Version 2.0; see LICENSE.Apache-2.0 for details.
// SPDX-License-Identifier: Apache-2.0

#include <hero-target.h>

extern int LAYER_COUNTER;

""")

  for i in range(len(layer)):

    f.write("""\
void gemm_{layer}(float ALPHA, float *A, float *B, float *C){{
  const int M = {M};
  const int N = {N};
  const int K = {K};
  __host float (*matA)[K] = (__host float(*)[K]) A;
  __host float (*matB)[N] = (__host float(*)[N]) B;
  __host float (*matC)[N] = (__host float(*)[N]) C;
  #pragma omp target data device(BIGPULP_MEMCPY) map(to: matB[0:{K}][0:{N}])
  {{
    #pragma omp target data device(BIGPULP_MEMCPY) map(to: matA[0:{M}][0:{K}])
    {{
      #pragma omp target device(BIGPULP_MEMCPY) map(tofrom: matC[0:{M}][0:{N}])
      {{
        #pragma omp parallel for num_threads(8) schedule(static, 1)
        for(int m = 0; m < M; ++m){{
          for(int k = 0; k < K; ++k){{
            float temp = ALPHA*matA[m][k];
            for(int n = 0; n < N; ++n){{
              matC[m][n] +=temp*matB[k][n];
            }}
          }}
        }}
      }}
    }}
  }}
  LAYER_COUNTER={next_layer};
}}


""".format(layer=layer[i], M=M[i], N=N[i], K=K[i], next_layer=layer[(i+1)%len(layer)]))
