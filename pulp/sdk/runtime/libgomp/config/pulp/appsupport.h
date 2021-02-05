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

#ifndef __APPSUPPORT_H__
#define __APPSUPPORT_H__

#include <stdint.h>
#include <hal/pulp.h>

static inline uint32_t
get_proc_id( )
{
#ifdef NATIVE
  return 0x0U;
#else
#if PULP_CHIP_FAMILY != CHIP_FULMINE
  return rt_core_id();
#else
  unsigned int value;
  __asm__ ("l.mfspr\t\t%0,r0,%1" : "=r" (value) : "I" (SPR_CORE_ID));
  return value;
#endif  
#endif
}

static inline uint32_t
get_cl_id( )
{
#ifdef NATIVE
  return 0x0U;
#else
#if PULP_CHIP_FAMILY != CHIP_FULMINE
  return rt_cluster_id();
#else    
  unsigned int value;
  __asm__ ("l.mfspr\t\t%0,r0,%1" : "=r" (value) : "I" (SPR_CLUSTER_ID));
  return value;
#endif
#endif
}

static inline uint32_t
get_num_procs()
{
#if PULP_CHIP_FAMILY != CHIP_FULMINE
  return rt_nb_pe();
#else  
  return *(volatile unsigned short*)(APB_SOC_CTRL_ADDR + 0x12);
#endif
}

static inline uint32_t
get_num_clusters()
{
#if PULP_CHIP_FAMILY != CHIP_FULMINE
  return rt_nb_cluster();
#else  
  return *(volatile unsigned short*)(APB_SOC_CTRL_ADDR + 0x10);
#endif
}

/*************************************************************
 * Print functions *
 *************************************************************/

#define _printdecp(a, b) printf("%s %d - Processor %d\n", a, b, get_proc_id())
#define _printdect(a, b) printf("%s %d - Time %d\n", a, b, get_time())
#define _printdecn(a, b) printf("%s %d\n", a, b)

#define _printhexp(a, b) printf("%s %x - Processor %d\n", a, b, get_proc_id())
#define _printhext(a, b) printf("%s %x - Time %d\n", a, b, get_time())
#define _printhexn(a, b) printf("%s %x\n", a, b)

#define _printstrp(a) printf("%s - Processor %d\n", a, get_proc_id())
#define _printstrt(a) printf("%s - Time %d\n", a, get_time())
#define _printstrn(a) printf("%s\n", a)

void abort( );

int  pulp_mchan_transfer(unsigned int len, char type, char incr, char twd, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int count, unsigned short int stride);
void pulp_mchan_barrier(int id);

void *pulp_l1malloc(int);
void *pulp_l2malloc(int);
void pulp_l1free(void *);
void pulp_l2free(void *);

static inline uint32_t
get_global_num_procs ( )
{
  return get_num_clusters( ) * get_num_procs( );
}

static inline uint32_t
get_cluster_base( uint32_t cid )
{
	uint32_t ret;
	switch( cid )
	{
		case 0x0U:
			ret = ARCHI_CLUSTER_GLOBAL_ADDR(0) + ARCHI_CLUSTER_SIZE * 0x0;
      break;
		case 0x1U:
			ret = ARCHI_CLUSTER_GLOBAL_ADDR(0) + ARCHI_CLUSTER_SIZE * 0x1;		
      break;
		case 0x2U:
			ret = ARCHI_CLUSTER_GLOBAL_ADDR(0) + ARCHI_CLUSTER_SIZE * 0x2;
      break;
		case 0x3U:
			ret = ARCHI_CLUSTER_GLOBAL_ADDR(0) + ARCHI_CLUSTER_SIZE * 0x3;
      break;
		default:
			ret = ARCHI_CLUSTER_GLOBAL_ADDR(0) + ARCHI_CLUSTER_SIZE * 0x0;
      break;
	}
	return ret;
}

static inline uint32_t
get_cluster_offset( uint32_t cid )
{
  uint32_t ret;
  switch( cid )
  {
    case 0x0U:
      ret = ARCHI_CLUSTER_SIZE * 0x0;
      break;
    case 0x1U:
      ret = ARCHI_CLUSTER_SIZE * 0x1;    
      break;
    case 0x2U:
      ret = ARCHI_CLUSTER_SIZE * 0x2;
      break;
    case 0x3U:
      ret = ARCHI_CLUSTER_SIZE * 0x3;
      break;
    default:
      ret = ARCHI_CLUSTER_SIZE * 0x0;
      break;
  }
  return ret;
}

static inline uint32_t
get_hal_addr( uint32_t cid,
              uint16_t offset)
{
	return get_cluster_base( cid ) + offset;
}
#endif // __APPSUPPORT_H__
