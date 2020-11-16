/*
 * Copyright (C) 2015 ETH Zurich and University of Bologna
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the BSD license.  See the LICENSE file for details.
 *
 */

#ifndef __ARCHI_UDMA_PERIPH_V1_H__
#define __ARCHI_UDMA_PERIPH_V1_H__


/*
 * I2S
 */

#ifdef PLP_UDMA_HAS_I2S

#define I2S_CHMODE_OFFSET                (0x00)
#define I2S_USEDDR_OFFSET                (0x04)
#define I2S_EXT_SETUP_OFFSET             (0x08)
#define I2S_CFG0_SETUP_OFFSET            (0x0C)
#define I2S_CFG1_SETUP_OFFSET            (0x10)

#endif


/*
 * UART
 */

#ifdef PLP_UDMA_HAS_UART

#define UART_SETUP_OFFSET                (0x00)
#define UART_STATUS_OFFSET               (0x0A)
 
#endif




/*
 * I2C
 */

#ifdef ARCHI_UDMA_HAS_I2C

#define ARCHI_I2C_SETUP_OFFSET          0x0

#define I2C_CMD_START   0x02
#define I2C_CMD_STOP    0x04
#define I2C_CMD_RD_ACK  0x08
#define I2C_CMD_RD_NACK 0x10
#define I2C_CMD_WR      0x20
#define I2C_CMD_WAIT    0x40
#define I2C_CMD_RPT     0x80

#define I2C_CMD_SETUP_ENABLE_BIT           8
#define I2C_CMD_SETUP_DIV_BIT              16

#endif




/*
 * SPIM
 */

#ifdef ARCHI_UDMA_HAS_SPIM

#define SPIM_RX_SADDR_OFFSET             0x000
#define SPIM_RX_SIZE_OFFSET              0x004
#define SPIM_RX_CFG_OFFSET               0x008
#define SPIM_RX_INTCFG_OFFSET            0x00C

#define SPIM_TX_SADDR_OFFSET             0x010
#define SPIM_TX_SIZE_OFFSET              0x014
#define SPIM_TX_CFG_OFFSET               0x018
#define SPIM_TX_INTCFG_OFFSET            0x01C

#define SPIM_STATUS_OFFSET               0x000
#define SPIM_CLKDIV_OFFSET               0x004
#define SPIM_SPICMD_OFFSET               0x008
#define SPIM_SPIADR_OFFSET               0x00C
#define SPIM_SPILEN_OFFSET               0x010
#define SPIM_SPIDUM_OFFSET               0x014
#define SPIM_TXFIFO_OFFSET               0x018
#define SPIM_RXFIFO_OFFSET               0x01C


#define ARCHI_SPIM_WSTATUS_QWRITE         8
#define ARCHI_SPIM_WSTATUS_QREAD          4
#define ARCHI_SPIM_WSTATUS_WRITE          2
#define ARCHI_SPIM_WSTATUS_READ           1

#define ARCHI_SPIM_WSTATUS_CSKEEP_BIT     16
#define ARCHI_SPIM_WSTATUS_CS_BIT         8
#define ARCHI_SPIM_WSTATUS_RESET_BIT      4
#define ARCHI_SPIM_WSTATUS_CMD_BIT        0

#define ARCHI_SPIM_RSTATUS_DATA_RX_BIT    6
#define ARCHI_SPIM_RSTATUS_DATA_TX_BIT    5
#define ARCHI_SPIM_RSTATUS_DUMMY_BIT      4
#define ARCHI_SPIM_RSTATUS_MODE_BIT       3
#define ARCHI_SPIM_RSTATUS_ADDR_BIT       2
#define ARCHI_SPIM_RSTATUS_CMD_BIT        1
#define ARCHI_SPIM_RSTATUS_IDLE_BIT       0

#define ARCHI_SPIM_CLKDIV_DATASIZE_TX_BIT 18 
#define ARCHI_SPIM_CLKDIV_DATASIZE_RX_BIT 16  
#define ARCHI_SPIM_CLKDIV_CPHA_BIT        9
#define ARCHI_SPIM_CLKDIV_CPOL_BIT        8
#define ARCHI_SPIM_CLKDIV_CLKDIV_BIT      0

#define SPIM_CMD_RD                      0
#define SPIM_CMD_WR                      1
#define SPIM_CMD_QRD                     2
#define SPIM_CMD_QWR                     3

#endif


#endif