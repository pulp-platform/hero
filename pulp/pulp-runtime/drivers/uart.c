/*
 * Copyright (C) 2019 ETH Zurich, University of Bologna
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "pulp.h"



#define UART_BAUDRATE 115200



static void uart_wait_tx_done(int periph)
{
  while (plp_udma_busy(UDMA_UART_TX_ADDR(periph - ARCHI_UDMA_UART_ID(0))))
  {
  }

  while(plp_uart_tx_busy(periph - ARCHI_UDMA_UART_ID(0)));
}


static void uart_wait_rx_done(int periph)
{
  while (plp_udma_busy(UDMA_UART_RX_ADDR(periph - ARCHI_UDMA_UART_ID(0))))
  {
  }
}



static void uart_setup(int channel, int baudrate)
{
  int div =  (PERIPH_FREQUENCY + baudrate/2) / baudrate;

  plp_uart_setup(channel - ARCHI_UDMA_UART_ID(0), 0, div-1);
}




int uart_open(int uart_id, int baudrate)
{
  int periph_id = ARCHI_UDMA_UART_ID(uart_id);
  int channel = UDMA_EVENT_ID(periph_id);

  plp_udma_cg_set(plp_udma_cg_get() | (1<<periph_id));

  soc_eu_fcEventMask_setEvent(channel);
  soc_eu_fcEventMask_setEvent(channel+1);

  uart_setup(periph_id, baudrate);

  return 0;
}




void uart_close(int uart_id)
{
  int periph_id = ARCHI_UDMA_UART_ID(uart_id);
  int channel = UDMA_EVENT_ID(periph_id);

  uart_wait_tx_done(periph_id);

  plp_uart_disable(periph_id);      

  plp_udma_cg_set(plp_udma_cg_get() & ~(1<<periph_id));
}





int uart_write(int uart_id, void *buffer, uint32_t size)
{
  int periph_id = ARCHI_UDMA_UART_ID(uart_id);
  int channel = UDMA_EVENT_ID(periph_id) + 1;

  unsigned int base = hal_udma_channel_base(channel);

  plp_udma_enqueue(base, (int)buffer, size, UDMA_CHANNEL_CFG_EN | UDMA_CHANNEL_CFG_SIZE_8);

  uart_wait_tx_done(periph_id);

  return 0;
}



int uart_read(int uart_id, void *buffer, uint32_t size)
{
  int periph_id = ARCHI_UDMA_UART_ID(uart_id);
  int channel = UDMA_EVENT_ID(periph_id);

  unsigned int base = hal_udma_channel_base(channel);

  plp_udma_enqueue(base, (int)buffer, size, UDMA_CHANNEL_CFG_EN | UDMA_CHANNEL_CFG_SIZE_8);

  uart_wait_rx_done(periph_id);

  return 0;
}
