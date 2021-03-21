// Copyright (c) 2017 Joseph Redmon
// Licensed under the MIT License, see LICENSE.MIT for details.
// SPDX-License-Identifier: MIT

#ifndef TREE_H
#define TREE_H
#include "darknet.h"

int hierarchy_top_prediction(float *predictions, tree *hier, float thresh, int stride);
float get_hierarchy_probability(float *x, tree *hier, int c, int stride);

#endif
