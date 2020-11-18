/*
 * Copyright (C) 2015 ETH Zurich and University of Bologna
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the BSD license.  See the LICENSE file for details.
 *
 */

#ifndef __HAL_UDMA_PERIPH_V1_H__
#define __HAL_UDMA_PERIPH_V1_H__

#include <hal/pulp.h>
#include <stdint.h>
#include "archi/udma/udma_v1.h"
#include "archi/udma/udma_periph_v1.h"


/*
 * I2S
 */

#if 0 //def ARCHI_UDMA_HAS_I2S

static inline void plp_i2s_channelModes(unsigned int channel0, unsigned int channel1, unsigned int channel2, unsigned int channel3)
{
  unsigned int value = (channel0 << 0) |  (channel1 << 2) |  (channel2 << 4) |  (channel3 << 6);
  pulp_write32(ARCHI_UDMA_ADDR + UDMA_I2S_OFFSET(0) + UDMA_CHANNEL_CUSTOM_OFFSET + I2S_CHMODE_OFFSET, value);
}

static inline void plp_i2s_useDdr(int use)
{
  pulp_write32(ARCHI_UDMA_ADDR + UDMA_I2S_OFFSET(0) + UDMA_CHANNEL_CUSTOM_OFFSET + I2S_USEDDR_OFFSET, use);
}

#endif



/*
 * UART
 */

#if 0 //def ARCHI_UDMA_HAS_UART

/**
 * Setup UART. The UART defaults to 8 bit character mode with 1 stop bit.
 *
 * parity       Enable/disable parity mode
 * clk_counter  Clock counter value that is used to derive the UART clock.
 *              There is a prescaler in place that already divides the SoC
 *              clock by 16.  Since this is a counter, a value of 0 means that
 *              the SoC clock divided by 16 is used. A value of 31 would mean
 *              that we use the SoC clock divided by 16*32 = 512.
 */

static inline void plp_uart_setup(int parity, uint16_t clk_counter)
{

  // [31:16]: clock divider (from SoC clock)
  // [9]: RX enable
  // [8]: TX enable
  // [3]: stop bits  0 = 1 stop bit
  //                 1 = 2 stop bits
  // [2:1]: bits     00 = 5 bits
  //                 01 = 6 bits
  //                 10 = 7 bits
  //                 11 = 8 bits
  // [0]: parity

  unsigned int val = 0x0306 | parity; // both tx and rx enabled; 8N1 configuration; 1 stop bits

  val |= ((clk_counter*16) << 16);

  pulp_write32(ARCHI_UDMA_ADDR + UDMA_UART_OFFSET(0) + UDMA_CHANNEL_CUSTOM_OFFSET + UART_SETUP_OFFSET, val);
}

#endif

/*
 * SPIM
 */

#ifdef ARCHI_UDMA_HAS_SPIM

static inline void plp_spi_disable(unsigned channelBase)
{
  pulp_write32(channelBase + UDMA_CHANNEL_CFG_OFFSET, 0);
}

static inline void hal_udma_spim_enqueue(unsigned int periphBase, unsigned channelBase, unsigned int spi_status, unsigned int l2Addr, unsigned int size, unsigned int cfg, unsigned int spi_len)
{
  pulp_write32(periphBase + UDMA_CHANNEL_CUSTOM_OFFSET + SPIM_SPILEN_OFFSET, spi_len << 16);
  pulp_write32(channelBase + UDMA_CHANNEL_SADDR_OFFSET, l2Addr);
  pulp_write32(channelBase + UDMA_CHANNEL_SIZE_OFFSET, size);
  pulp_write32(channelBase + UDMA_CHANNEL_CFG_OFFSET, cfg);
  pulp_write32(periphBase + UDMA_CHANNEL_CUSTOM_OFFSET + SPIM_STATUS_OFFSET, spi_status);
}

static inline uint32_t hal_udma_spim_status_compute(
  unsigned int cskeep, unsigned int cs, unsigned int reset, unsigned int command
)
{
  return (cskeep << ARCHI_SPIM_WSTATUS_CSKEEP_BIT) |
    (cs << ARCHI_SPIM_WSTATUS_CS_BIT) |
    (reset << ARCHI_SPIM_WSTATUS_RESET_BIT) |
    (command << ARCHI_SPIM_WSTATUS_CMD_BIT);
}

static inline uint32_t hal_udma_spim_status_get(uint32_t periph_base)
{
  return pulp_read32(periph_base + UDMA_CHANNEL_CUSTOM_OFFSET + SPIM_STATUS_OFFSET);
}

static inline void hal_udma_spim_status_set(uint32_t periph_base, uint32_t value)
{
  pulp_write32(periph_base + UDMA_CHANNEL_CUSTOM_OFFSET + SPIM_STATUS_OFFSET, value);
}

static inline uint32_t hal_udma_spim_clkdiv_compute(
  int datasize_tx, int datasize_rx, int cpha, int cpol, int clkdiv
)
{
  return (datasize_tx << ARCHI_SPIM_CLKDIV_DATASIZE_TX_BIT) |
    (datasize_rx << ARCHI_SPIM_CLKDIV_DATASIZE_RX_BIT) |
    (cpha << ARCHI_SPIM_CLKDIV_CPHA_BIT) |
    (cpol << ARCHI_SPIM_CLKDIV_CPOL_BIT) |
    (clkdiv << ARCHI_SPIM_CLKDIV_CLKDIV_BIT);
}

static inline uint32_t hal_udma_spim_clkdiv_get(uint32_t periph_base)
{
  return pulp_read32(periph_base + UDMA_CHANNEL_CUSTOM_OFFSET + SPIM_CLKDIV_OFFSET);
}

static inline void hal_udma_spim_clkdiv_set(uint32_t periph_base, uint32_t value)
{
  pulp_write32(periph_base + UDMA_CHANNEL_CUSTOM_OFFSET + SPIM_CLKDIV_OFFSET, value);
}


#endif

/*
 * I2C
 */

#ifdef ARCHI_UDMA_HAS_I2C

static inline uint32_t hal_udma_i2c_setup_compute(int en, int div)
{
  return (en << I2C_CMD_SETUP_ENABLE_BIT) | ( div << I2C_CMD_SETUP_DIV_BIT);
}

static inline void hal_udma_i2c_setup_set(uint32_t periph_base, uint32_t value)
{
  pulp_write32(periph_base + UDMA_CHANNEL_CUSTOM_OFFSET + ARCHI_I2C_SETUP_OFFSET, value);
}

static inline uint32_t hal_udma_i2c_setup_get(uint32_t periph_base)
{
  return pulp_read32(periph_base + UDMA_CHANNEL_CUSTOM_OFFSET + ARCHI_I2C_SETUP_OFFSET);
}

#endif

#endif