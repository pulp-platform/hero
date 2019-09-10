/*
 * This file is part of the PULP device driver.
 *
 * Copyright (C) 2018 ETH Zurich, University of Bologna
 *
 * Author: Koen Wolters <kwolters@student.ethz.ch>
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

#include <linux/types.h>
#include <linux/kernel.h>

#define U64_COUNTER_DIFF(s, e) ((e >= s) ? e - s : (U64_MAX - s) + e)

/** Get internal host clock counter
 *
 *  \return number of clock cycles since last reset
 */
uint64_t host_get_clock_counter(void);
/** Reset internal host clock counter
 */
void host_reset_clock_counter(void);

/** Get time in nanoseconds precision

    \return time in nanoseconds
 */
uint64_t host_get_time(void);

/** Get accelerator clock counter

    \param clusters virtual address of the cluster config
    \param index index of the cluster to get the time for

    \return pulp time value
*/
uint64_t accel_get_clk(void *clusters, int index);

/** Reset accelerator clock counter

    \param clusters virtual address of the cluster config
    \param index index of the cluster to reset the time
*/
void accel_reset_clk(void *clusters, int index);
