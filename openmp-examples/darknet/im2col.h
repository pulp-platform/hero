// Copyright (c) 2017 Joseph Redmon
// Licensed under the MIT License, see LICENSE.MIT for details.
// SPDX-License-Identifier: MIT

#ifndef IM2COL_H
#define IM2COL_H

void im2col_cpu(float* data_im, int channels, int height, int width, int ksize, int stride, int pad,
                float* data_col);

#ifdef GPU

void im2col_gpu(float* im, int channels, int height, int width, int ksize, int stride, int pad,
                float* data_col);

#endif
#endif
