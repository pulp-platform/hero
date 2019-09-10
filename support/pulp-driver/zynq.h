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
#ifndef ZYNQ_H___
#define ZYNQ_H___

/*
 * Board selection
 */
#define ZEDBOARD 1
#define ZC706 2
#define MINI_ITX 3

#ifndef PLATFORM
  #error "Define PLATFORM!"
#endif

// DRAM
#if PLATFORM == ZEDBOARD
  #define DRAM_SIZE_MB 512
#elif PLATFORM == ZC706 || PLATFORM == MINI_ITX
  #define DRAM_SIZE_MB 1024
#endif

// System-Level Control Register
#define SLCR_BASE_ADDR 0xF8000000
#define SLCR_SIZE_B 0x1000
#define SLCR_FPGA_RST_CTRL_OFFSET_B 0x240
#define SLCR_FPGA_OUT_RST 1
#define SLCR_FPGA0_THR_CNT_OFFSET_B 0x178
#define SLCR_FPGA0_THR_STA_OFFSET_B 0x17C

// UART0 Controller - PULP -> Host UART
#define HOST_UART_BASE_ADDR 0xE0000000
#define HOST_UART_SIZE_B 0x1000
#define MODEM_CTRL_REG0_OFFSET_B 0x24

#endif // ZYNQ_H___
