// Copyright (c) 2017 Joseph Redmon
// Licensed under the MIT License, see LICENSE.MIT for details.
// SPDX-License-Identifier: MIT

#ifndef COL2IM_H
#define COL2IM_H

void col2im_cpu(float* data_col, int channels, int height, int width, int ksize, int stride,
                int pad, float* data_im);

#ifdef GPU
void col2im_gpu(float* data_col, int channels, int height, int width, int ksize, int stride,
                int pad, float* data_im);
#endif
#endif
