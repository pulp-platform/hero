/*
 * Copyright (C) 2018 ETH Zurich and University of Bologna
 * 
 * Authors: 
 *    Alessandro Capotondi, UNIBO, (alessandro.capotondi@unibo.it)
 *    Germain Haugou,       ETH,   (germain.haugou@iis.ee.ethz.ch)
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


#ifndef __PULP_OMP_CONFIG_H__
#define __PULP_OMP_CONFIG_H__

#include <pulp.h>
extern char _libgomp_start;

#define LIBGOMP_BASE_ADDR             ((int)&_libgomp_start)

#define NUM_HW_BARRIER          ( 0x04U )

//------------------------------------------------------------
// Builtin command line parameter defaults
//------------------------------------------------------------
#define SIZEOF_UNSIGNED         ( 0x04U )
#define SIZEOF_PTR              ( 0x04U )
#define SIZEOF_INT              ( 0x04U )
#define SIZEOF_WORD             ( 0x04U )
#define LIBGOMP_LBASE           ( LIBGOMP_BASE_ADDR )
#define LIBGOMP_BASE            ( LIBGOMP_BASE_ADDR )
#define CLUSTER_OFFSET          ( ARCHI_CLUSTER_SIZE )

/* Maximum number of clusters supported */
#ifndef DEFAULT_MAXCL
#if PULP_CHIP == CHIP_BIGPULP
#define DEFAULT_MAXCL           ( 0x04U )
#else
#define DEFAULT_MAXCL           ( 0x01U )
#endif
#endif

/* Maximum number of PEs per-cluster supported */
#ifndef DEFAULT_MAX_PE
#define DEFAULT_MAX_PE          ( 0x08U )
#endif

/* Maximum number of processors supported */
#ifndef DEFAULT_MAXPROC
#define DEFAULT_MAXPROC         ( DEFAULT_MAX_PE )
#endif

#ifdef __riscv__
#define PCER_ALL_EVENTS_MASK CSR_PCER_ALL_EVENTS_MASK
#define PCMR_ACTIVE CSR_PCMR_ACTIVE
#define PCMR_SATURATE CSR_PCMR_SATURATE
#else
#define PCER_ALL_EVENTS_MASK SPR_PCER_ALL_EVENTS_MASK
#define PCMR_ACTIVE SPR_PCMR_ACTIVE
#define PCMR_SATURATE SPR_PCMR_SATURATE
#endif

//------------------------------------------------------------------------------
// Hardwired Event Unit Offsets 
//------------------------------------------------------------------------------

#define OFFSET_EV_BUFF_CLEAR   ( 0x0400U + 0x0004U )
#define OFFSET_CORE_CLKGATE    ( 0x0400U + 0x000CU )

#define OFFSET_TRIGG_BARRIER   ( 0x0800U + 0x035CU )
#define OFFSET_EVENT0          ( 0x0800U + 0X0360U )
#define OFFSET_WAIT_BARRIER    ( 0x0800U + 0x036CU )

#endif
