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
#ifndef _PULP_MBOX_H_
#define _PULP_MBOX_H_

#include <linux/spinlock.h> /* locking in interrupt context*/
#include <asm/uaccess.h> /* copy_to_user, copy_from_user, access_ok */
#include <asm/io.h> /* ioremap, iounmap, iowrite32 */
#include <linux/fs.h> /* file_operations struct, struct file */
#include <linux/sched.h> /* wake_up_interruptible(), TASK_INTERRUPTIBLE */

#include "pulp_module.h"

#define MBOX_GET_REQ_TYPE(type, request) \
  (type = BF_GET(request, 32 - MBOX_N_BITS_REQ_TYPE, MBOX_N_BITS_REQ_TYPE) << (32 - MBOX_N_BITS_REQ_TYPE))
#define MBOX_GET_N_WORDS(n_words, request) (n_words = BF_GET(request, 0, 32 - MBOX_N_BITS_REQ_TYPE))

/** @name mailbox functions
 * @{
 */

/** Initialize the mailbox.

  \param    mbox kernel virtual address of the mailbox PULP-2-Host interface (Interface 1)
 */
void pulp_mbox_init(void *mbox);

/** Set the mailbox operation mode

    \param mode new mode to operate

    \return 0 on success; negative with errno on errors
*/
int pulp_mbox_set_mode(MailboxMode mode);

/** Get the mailbox operation mode

    \return operation mode
*/
MailboxMode pulp_mbox_get_mode(void);

/** Empty mbox_fifo buffer
 */
void pulp_mbox_clear(void);

/** Read from PULP-2-Host mailbox interface to software FIFO

 *  NOTE: This is the bottom-half, it should actually go into a tasklet.

  \param    mbox kernel virtual address of the mailbox PULP-2-Host interface (Interface 1)
 */
void pulp_mbox_intr(void *mbox);

/** Provide read data from mbox_fifo to user-space application.

 *  Standard Linux kernel read interface
 */
ssize_t pulp_mbox_read(struct file *filp, char __user *buf, size_t count, loff_t *offp);

//!@}

#endif // _PULP_MBOX_H_
