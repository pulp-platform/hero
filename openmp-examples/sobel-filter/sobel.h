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

int  rgbToGray   (byte *rgb, byte *gray, int buffer_size);
void makeOpMem   (byte *buffer, int buffer_size, int width, int cindex, byte *op_mem);
int  convolution (byte *X, int *Y, int c_size);
void itConv      (byte *buffer, int buffer_size, int width, int *op, byte *res);
void contour     (byte *sobel_h, byte *sobel_v, int gray_size, byte *contour_img);
int  sobelFilter (byte *rgb, byte *gray, byte *sobel_h_res, byte *sobel_v_res, byte *contour_img, int width, int height);

#endif

