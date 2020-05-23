/*
 * Copyright 2018 Pedro Melgueira
 * Contribution 2018 (C) ETH Zurich and University of Bologna
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef SOBEL_H
#define SOBEL_H

#include "macros.h"

int  rgbToGray   (__host byte *rgb, __host byte *gray, int buffer_size);
void makeOpMem   (__host byte *buffer, int buffer_size, int width, int cindex, byte *op_mem);
int  convolution (byte *X, int *Y, int c_size);
void itConv      (__host byte *buffer, int buffer_size, int width, int *op, __host byte *res);
void contour     (__host byte *sobel_h, __host byte *sobel_v, int gray_size, __host byte *contour_img);
int  sobelFilter (__host byte *rgb, __host byte *gray, __host byte *sobel_h_res, __host byte *sobel_v_res, __host byte *contour_img, int width, int height);

#endif

