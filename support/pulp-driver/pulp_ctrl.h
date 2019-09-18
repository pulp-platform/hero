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

#ifndef _PULP_CTRL_H_
#define _PULP_CTRL_H_

#include "pulp_module.h"

/** Resets the accelerator

    NOTE: This function sleeps while performing the reset

    \param    gpio_config virtual addres of the GPIO configuration
    \param    gpio_config virtual addres of the SLCR configuration (NULL if not used)
    \param    gpio_value pointer to the current gpio value
    \param    full if full reset has to be performed (only used with slcr)

    \return   zero if succesful, negative value with errno on errors
*/
int pulp_reset(void *gpio_config, void *slcr_config, unsigned *gpio_value, bool full);

/** Configures the clock speed of the accelerator

    NOTE: This function sleeps while performing the configuration

    \param    clking_config virtual address of the clocking configuration
    \param    des_freq_mhz requested destination clock speed in mhz

    \return   final configured clock speed if succesful, negative value with errno on errors
*/
int pulp_clking_set_freq(void *clking_config, unsigned des_freq_mhz);

#endif
