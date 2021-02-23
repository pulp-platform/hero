/*
 * Copyright (C) 2018 ETH Zurich and University of Bologna
 * 
 * Authors: 
 *    Alessandro Capotondi, UNIBO, (alessandro.capotondi@unibo.it)
 */

/* Copyright (C) 2005-2014 Free Software Foundation, Inc.
 * 
 * This file is part of the GNU OpenMP Library (libgomp).
 * 
 * Libgomp is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3, or (at your option)
 * any later version.
 * 
 * Libgomp is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 * more details.
 * 
 * Under Section 7 of GPL version 3, you are granted additional
 * permissions described in the GCC Runtime Library Exception, version
 * 3.1, as published by the Free Software Foundation.
 * 
 * You should have received a copy of the GNU General Public License and
 * a copy of the GCC Runtime Library Exception along with this program;
 * see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see
 * <http://www.gnu.org/licenses/>.
 */

/* This file lists all the files to be included for compilation.  */

#include "libgomp.h"

/* SOURCES */
#if PULP_CHIP == CHIP_HERO_Z_7045
#include "hero/offload-manager.c"
#endif

#include "barrier.c"
#include "iter.c"                
#include "work.c"
#include "team.c"
#include "target.c"
#include "loop.c"
#include "sections.c"
#include "single.c"
#include "parallel.c"
#include "critical.c"                
#include "env.c"

#include "libgomp.c"

