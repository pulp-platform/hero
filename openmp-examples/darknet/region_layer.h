// Copyright (c) 2017 Joseph Redmon
// Licensed under the MIT License, see LICENSE.MIT for details.
// SPDX-License-Identifier: MIT

#ifndef REGION_LAYER_H
#define REGION_LAYER_H

#include "darknet.h"
#include "layer.h"
#include "network.h"

layer make_region_layer(int batch, int w, int h, int n, int classes, int coords);
void forward_region_layer(const layer l, network net);
void backward_region_layer(const layer l, network net);
void resize_region_layer(layer *l, int w, int h);

#ifdef GPU
void forward_region_layer_gpu(const layer l, network net);
void backward_region_layer_gpu(layer l, network net);
#endif

#endif
