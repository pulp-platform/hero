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

#define __nop { \
  asm("l.nop"); \
}

#define _10_nop_block  { \
  asm("l.nop"); \
  asm("l.nop"); \
  asm("l.nop"); \
  asm("l.nop"); \
  asm("l.nop"); \
  asm("l.nop"); \
  asm("l.nop"); \
  asm("l.nop"); \
  asm("l.nop"); \
  asm("l.nop"); \
  }

#define _50_nop_block  { \
  _10_nop_block \
  _10_nop_block \
  _10_nop_block \
  _10_nop_block \
  _10_nop_block \
  }

#define _100_nop_block  { \
  _50_nop_block \
  _50_nop_block \
  }

#define _200_nop_block  { \
  _100_nop_block \
  _100_nop_block \
  }

#define _500_nop_block  { \
  _200_nop_block \
  _200_nop_block \
  _100_nop_block \
  }

#define _1000_nop_block  { \
  _500_nop_block \
  _500_nop_block \
  }

#define _2000_nop_block  { \
  _1000_nop_block \
  _1000_nop_block \
  }

#define _5000_nop_block  { \
  _2000_nop_block \
  _2000_nop_block \
  _1000_nop_block \
  }

#define _10000_nop_block  { \
  _5000_nop_block \
  _5000_nop_block \
  }

#define _20000_nop_block  { \
  _10000_nop_block \
  _10000_nop_block \
  }

#define _50000_nop_block  { \
  _10000_nop_block \
  _20000_nop_block \
  _20000_nop_block \
  }

#define _100000_nop_block  { \
  _50000_nop_block \
  _50000_nop_block \
  }
