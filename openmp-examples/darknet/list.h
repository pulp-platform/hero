// Copyright (c) 2017 Joseph Redmon
// Licensed under the MIT License, see LICENSE.MIT for details.
// SPDX-License-Identifier: MIT

#ifndef LIST_H
#define LIST_H
#include "darknet.h"

list *make_list();
int list_find(list *l, void *val);

void list_insert(list *, void *);

void free_list_contents(list *l);

#endif
