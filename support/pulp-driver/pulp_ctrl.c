/*
 * This file is part of the PULP device driver.
 *
 * Copyright (C) 2018 ETH Zurich, University of Bologna
 *
 * Author: Pirmin Vogel <vogelpi@iis.ee.ethz.ch>
 *         Koen Wolters <kwolters@student.ethz.ch>
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

#include "pulp_ctrl.h"

#include <linux/delay.h>
#include <asm/io.h>

int pulp_reset(void *gpio_config, void *slcr_config, unsigned *gpio_value, bool full)
{
#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX
  unsigned slcr_value;

  // FPGA reset control register
  slcr_value = ioread32((void *)((unsigned long)slcr_config + SLCR_FPGA_RST_CTRL_OFFSET_B));

  // extract the FPGA_OUT_RST bits
  slcr_value = slcr_value & 0xF;

  if (full) { // if full reset required
    // enable reset
    iowrite32(0xF, (void *)((unsigned long)slcr_config + SLCR_FPGA_RST_CTRL_OFFSET_B));

    // wait
    msleep(100);

    // disable reset
    iowrite32(slcr_value, (void *)((unsigned long)slcr_config + SLCR_FPGA_RST_CTRL_OFFSET_B));
  } else {
    // enable reset
    iowrite32(slcr_value | (0x1 << SLCR_FPGA_OUT_RST), (void *)((unsigned long)slcr_config + SLCR_FPGA_RST_CTRL_OFFSET_B));

    // wait
    msleep(100);

    // disable reset
    iowrite32(slcr_value, (void *)((unsigned long)slcr_config + SLCR_FPGA_RST_CTRL_OFFSET_B));
#endif

    // trigger reset using GPIO register
#if GPIO_RST_N >= 0
    BIT_CLEAR(*gpio_value, BF_MASK_GEN(GPIO_RST_N, 1));
    iowrite32(*gpio_value, (void *)((unsigned long)gpio_config + GPIO_HOST2PULP_OFFSET));
    msleep(100);
    BIT_SET(*gpio_value, BF_MASK_GEN(GPIO_RST_N, 1));
    iowrite32(*gpio_value, (void *)((unsigned long)gpio_config + GPIO_HOST2PULP_OFFSET));
    msleep(100);
#endif

#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX
  }
#endif

  return 0;
}

/*
 * clk_in   = CLKING_INPUT_FREQ_MHZ (100 or 50 MHz) multiplied to 1000 MHz
 * clk_out1 = CLKOUT0: divide 1000 MHz by CLKING_CONFIG_REG_2 -> ClkSoc_C
 * clk_out2 = CLKOUT1: divide 1000 MHz by CLKING_CONFIG_REG_5 -> ClkCluster_C
 */
int pulp_clking_set_freq(void *clking_config, unsigned des_freq_mhz)
{
  unsigned status, value;
  unsigned freq_mhz;
  int divclk_divide, clkout0_divide, clkout0_divide_frac;
  int clkfbout_mult;

  freq_mhz = des_freq_mhz - (des_freq_mhz % 5);
  if (freq_mhz <= 0)
    freq_mhz = 5;
  else if (freq_mhz >= 200)
    freq_mhz = 200;

    // Bring the input clock to 1000 MHz
#if CLKING_INPUT_FREQ_MHZ == 50
  divclk_divide = 1;
  clkfbout_mult = 20;
#elif CLKING_INPUT_FREQ_MHZ == 100
  divclk_divide = 1;
  clkfbout_mult = 10;
#else
  #error CLKING_INPUT_FREQ_MHZ value is not supported
#endif

  // default output clock = 50 MHz
  clkout0_divide = 1000 / freq_mhz;
  clkout0_divide_frac = ((1000 % freq_mhz) << 10) / freq_mhz;

  // config DIVCLK_DIVIDE, CLKFBOUT_MULT, CLKFBOUT_FRAC, CLKFBOUT_PHASE
  value = 0x04000000 + 0x100 * clkfbout_mult + 0x1 * divclk_divide;
  iowrite32(value, (void *)(((unsigned long)clking_config) + CLKING_CONFIG_REG_0_OFFSET_B));
  if (DEBUG_LEVEL_CTRL > 3)
    printk(KERN_INFO "CLKING_CONFIG_REG_0: %#x\n", value);

  // config CLKOUT0/1: DIVIDE, FRAC, FRAC_EN
  value = 0x00040000 + 0x100 * clkout0_divide_frac + 0x1 * clkout0_divide;
  iowrite32(value, (void *)(((unsigned long)clking_config) + CLKING_CONFIG_REG_2_OFFSET_B));
  iowrite32(value, (void *)(((unsigned long)clking_config) + CLKING_CONFIG_REG_5_OFFSET_B));
  if (DEBUG_LEVEL_CTRL > 3)
    printk(KERN_INFO "CLKING_CONFIG_REG_2/5: %#x\n", value);

  // wait for lock
  status = 1;
  while (status) {
    msleep(1);
    status = !(ioread32((void *)(((unsigned long)clking_config) + CLKING_STATUS_REG_OFFSET_B)) & 0x1);
  }

  // start reconfiguration
  iowrite32(0x7, (void *)(((unsigned long)clking_config) + CLKING_CONFIG_REG_23_OFFSET_B));
  msleep(100);
  iowrite32(0x2, (void *)(((unsigned long)clking_config) + CLKING_CONFIG_REG_23_OFFSET_B));

  // wait for lock
  status = 1;
  while (status) {
    msleep(1);
    status = !(ioread32((void *)(((unsigned long)clking_config) + CLKING_STATUS_REG_OFFSET_B)) & 0x1);
  }

  return freq_mhz;
}
