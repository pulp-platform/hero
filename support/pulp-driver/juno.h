/*
 * This file is part of the PULP device driver.
 *
 * Copyright (C) 2018 ETH Zurich, University of Bologna
 *
 * Author: Pirmin Vogel <vogelpi@iis.ee.ethz.ch>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
#ifndef JUNO_H___
#define JUNO_H___

#include "arm64.h"

// DRAM
#define DRAM_SIZE_MB 8192

// io{read,write}64 macros - not defined in the kernel sources
#ifndef ioread64
  #define ioread64(p)                                        \
    ({                                                       \
      u64 __v = le64_to_cpu((__force __le64)__raw_readq(p)); \
      __iormb();                                             \
      __v;                                                   \
    })
#endif
#ifndef iowrite64
  #define iowrite64(v, p)                           \
    ({                                              \
      __iowmb();                                    \
      __raw_writeq((__force u64)cpu_to_le64(v), p); \
    })
#endif

#endif // JUNO_H___
