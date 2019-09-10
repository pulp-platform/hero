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
#ifndef ZYNQMP_H___
#define ZYNQMP_H___

#include "arm64.h"

// DRAM
#define DRAM_SIZE_MB 2048

// Cache-coherent interconnect CCI-400
#define CCI_BASE_ADDR 0xFD6E0000
#define CCI_SIZE_B 0xE000

#define CCI_SHOR_S0_OFFSET_B 0x1004

// System Memory Management Unit
#define SMMU_BASE_ADDR 0xFD800000
#define SMMU_SIZE_B 0x20000
#define SMMU_CB_OFFSET_B 0x10000
#define SMMU_CB_SIZE_B 0x1000

#define SMMU_N_SMRS 48

#define SMMU_STREAM_ID_HPC0 0x200
#define SMMU_STREAM_ID_HP0 0xE80

// UART1 Controller - PULP -> Host UART
#define HOST_UART_BASE_ADDR 0xFF010000
#define HOST_UART_SIZE_B 0x1000
#define MODEM_CTRL_REG0_OFFSET_B 0x24

#endif // ZYNQMP_H___
