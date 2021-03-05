// Copyright (c) 2020 ETH Zurich and University of Bologna
// Licensed under the Apache License, Version 2.0; see LICENSE.Apache-2.0 for details.
// SPDX-License-Identifier: Apache-2.0

// The following arrays are indexed by the layer number.  The value for non-existing layers is `-1`.
static const int LAYER_M[] = {16, -1, 32, -1, 64, -1, 128, -1, 256, -1, 512, -1, 1024, 256, 512, 255, -1, -1, 128, -1, -1, 256, 255};
static const int LAYER_N[] = {173056, -1, 43264, -1, 10816, -1, 2704, -1, 676, -1, 169, -1, 169, 169, 169, 169, -1, -1, 169, -1, -1, 676, 676};
static const int LAYER_K[] = {27, -1, 144, -1, 288, -1, 576, -1, 1152, -1, 2304, -1, 4608, 1024, 2304, 512, -1, -1, 256, -1, -1, 3456, 256};
static const int LAYER_NEXT[] = {2, -1, 4, -1, 6, -1, 8, -1, 10, -1, 12, -1, 13, 14, 15, 18, -1, -1, 21, -1, -1, 22, -1};

void gemm_0(float ALPHA, float *A, float *B, float *C);
void gemm_2(float ALPHA, float *A, float *B, float *C);
void gemm_4(float ALPHA, float *A, float *B, float *C);
void gemm_6(float ALPHA, float *A, float *B, float *C);
void gemm_8(float ALPHA, float *A, float *B, float *C);
void gemm_10(float ALPHA, float *A, float *B, float *C);
void gemm_12(float ALPHA, float *A, float *B, float *C);
void gemm_13(float ALPHA, float *A, float *B, float *C);
void gemm_14(float ALPHA, float *A, float *B, float *C);
void gemm_15(float ALPHA, float *A, float *B, float *C);
void gemm_18(float ALPHA, float *A, float *B, float *C);
void gemm_21(float ALPHA, float *A, float *B, float *C);
void gemm_22(float ALPHA, float *A, float *B, float *C);
