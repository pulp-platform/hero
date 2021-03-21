// Copyright (c) 2017 Joseph Redmon
// Licensed under the MIT License, see LICENSE.MIT for details.
// SPDX-License-Identifier: MIT

#ifndef CROP_LAYER_H
#define CROP_LAYER_H

#include "image.h"
#include "layer.h"
#include "network.h"

typedef layer crop_layer;

image get_crop_image(crop_layer l);
crop_layer make_crop_layer(int batch, int h, int w, int c, int crop_height, int crop_width,
                           int flip, float angle, float saturation, float exposure);
void forward_crop_layer(const crop_layer l, network net);
void resize_crop_layer(layer *l, int w, int h);

#ifdef GPU
void forward_crop_layer_gpu(crop_layer l, network net);
#endif

#endif
