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
#include "pulp_module.h"
#include "pulp_mbox.h"
#include "pulp_rab.h" /* for pulp_rab_update() */

#undef ARM
#include "archi/pulp.h"

static void *pulp_mbox;
static MailboxMode mbox_mode = MBOX_OFF;

static unsigned mbox_fifo[MBOX_FIFO_DEPTH * 2];
static unsigned mbox_fifo_full;
static unsigned *mbox_fifo_rd = mbox_fifo;
static unsigned *mbox_fifo_wr = mbox_fifo;
static unsigned n_words_written, n_words_to_write;

DEFINE_SPINLOCK(mbox_fifo_mtx);
DECLARE_WAIT_QUEUE_HEAD(mbox_wq);

void pulp_mbox_init(void *mbox)
{
  // initialize the pointer for pulp_mbox_read
  pulp_mbox = mbox;

  mbox_mode = MBOX_OFF;
  mbox_fifo_full = 0;

  pulp_mbox_clear();

  return;
}

int pulp_mbox_set_mode(MailboxMode mode)
{
  mbox_mode = mode;

  if (mode == MBOX_OFF) {
    // Disable all mailbox IRQs.
    iowrite32(MBOX_IRQ_MASK_NONE, pulp_mbox + MBOX_IE_OFFSET_B);
    pr_info("PULP - MBOX: All IRQs disabled.\n");
  } else {
    // Enable read threshold and error IRQ.
    iowrite32(MBOX_IRQ_MASK_READ | MBOX_IRQ_MASK_ERROR, pulp_mbox + MBOX_IE_OFFSET_B);
    pr_info("PULP - MBOX: Read threshold and error IRQ enabled.\n");
  }

  return 0;
}
MailboxMode pulp_mbox_get_mode(void)
{
  return mbox_mode;
}

void mbox_fifo_lock(void) {
  spin_lock(&mbox_fifo_mtx);
  pr_debug("PULP - MBOX: Acquired FIFO lock.\n");
}

void mbox_fifo_lock_irqsave(unsigned long* const flags) {
  unsigned long _flags;
  spin_lock_irqsave(&mbox_fifo_mtx, _flags);
  *flags = _flags;
  pr_debug("PULP - MBOX: Acquired FIFO lock after disabling IRQs.\n");
}

void mbox_fifo_unlock(void) {
  spin_unlock(&mbox_fifo_mtx);
  pr_debug("PULP - MBOX: Released FIFO lock.\n");
}

void mbox_fifo_unlock_irqrestore(const unsigned long flags) {
  spin_unlock_irqrestore(&mbox_fifo_mtx, flags);
  pr_debug("PULP - MBOX: Released FIFO lock and re-enabled IRQs.\n");
}

void pulp_mbox_clear(void)
{
  int i;
  unsigned long flags;

  mbox_fifo_lock_irqsave(&flags);

  // empty mbox_fifo
  if ((mbox_fifo_wr != mbox_fifo_rd) || mbox_fifo_full) {
    for (i = 0; i < 2 * MBOX_FIFO_DEPTH; i++) {
      pr_info("mbox_fifo[%d]: %d %d %#x \n", i, (&mbox_fifo[i] == mbox_fifo_wr) ? 1 : 0,
             (&mbox_fifo[i] == mbox_fifo_rd) ? 1 : 0, mbox_fifo[i]);
    }
  }
  mbox_fifo_wr = mbox_fifo;
  mbox_fifo_rd = mbox_fifo;
  mbox_fifo_full = 0;
  n_words_written = 0;
  n_words_to_write = 0;

  // Flush hardware mailbox and acknowledge any Host-side IRQs.
  pr_info("PULP - MBOX: Flushing read and write FIFOs.\n");
  iowrite32(MBOX_CTRL_MASK_FLUSH_WRITES | MBOX_CTRL_MASK_FLUSH_READS,
      pulp_mbox + MBOX_CTRL_OFFSET_B);
  pr_info("PULP - MBOX: Acknowledging any Host-side IRQs.\n");
  iowrite32(MBOX_IRQ_MASK_ALL, pulp_mbox + MBOX_IS_OFFSET_B);

  mbox_fifo_unlock_irqrestore(flags);

  return;
}

void pulp_mbox_intr(void *mbox)
{
  int i;
  unsigned n_words_written_tmp;
  unsigned req_type;
  unsigned mbox_is, mbox_data;
  struct timeval time;

  if (mbox_mode == MBOX_OFF) {
    pr_warn("PULP - MBOX: Got IRQ outside driver mode, propagating IRQ Off to hardware.\n");
    pulp_mbox_set_mode(MBOX_OFF);
    return;
  } else if (DEBUG_LEVEL_MBOX > 0) {
    pr_info("PULP - MBOX: Handling IRQ.\n");
  }

  // check interrupt status
  mbox_is = ioread32((void *)((unsigned long)mbox + MBOX_IS_OFFSET_B)) & MBOX_IRQ_MASK_ALL;

  if (mbox_is & MBOX_IRQ_MASK_READ) { // mailbox receive threshold interrupt
    // clear the interrupt
    iowrite32(0x2, (void *)((unsigned long)mbox + MBOX_IS_OFFSET_B));

    n_words_written_tmp = 0;

    mbox_fifo_lock();
    // while mailbox not empty and FIFO buffer not full
    while (!(0x1 & ioread32((void *)((unsigned long)mbox + MBOX_STATUS_OFFSET_B))) && !mbox_fifo_full) {
      // read mailbox
      mbox_data = ioread32((void *)((unsigned long)mbox + MBOX_RDDATA_OFFSET_B));

      if (n_words_written == n_words_to_write) { // new transfer

        MBOX_GET_REQ_TYPE(req_type, mbox_data);

        if (TO_RUNTIME == req_type) {
          // extract number of words
          MBOX_GET_N_WORDS(n_words_to_write, mbox_data);
          n_words_written = 0;

          continue;
        } else {
          mbox_fifo_unlock();

          if (RAB_UPDATE == req_type) {
            pulp_rab_update(mbox_data);
          } else if (RAB_SWITCH == req_type) {
            pulp_rab_switch();
          } else {
            pr_info("PULP - MBOX: Unknown request type %d\n", req_type);
          }

          mbox_fifo_lock();
        }
      } else { // write to mailbox FIFO buffer

        // write to mbox_fifo
        *mbox_fifo_wr = mbox_data;

        // update write pointer
        mbox_fifo_wr++;

        // wrap around?
        if (mbox_fifo_wr >= (mbox_fifo + 2 * MBOX_FIFO_DEPTH))
          mbox_fifo_wr = mbox_fifo;
        // full?
        if (mbox_fifo_wr == mbox_fifo_rd)
          mbox_fifo_full = 1;
        if (DEBUG_LEVEL_MBOX > 0) {
          pr_info("PULP - MBOX: Written %#x to mbox_fifo.\n", mbox_data);
          pr_info("PULP - MBOX: mbox_fifo_wr: %d\n", (unsigned)(mbox_fifo_wr - mbox_fifo));
          pr_info("PULP - MBOX: mbox_fifo_rd: %d\n", (unsigned)(mbox_fifo_rd - mbox_fifo));
          pr_info("PULP - MBOX: mbox_fifo_full %d\n", mbox_fifo_full);
          if (DEBUG_LEVEL_MBOX > 1) {
            for (i = 0; i < 2 * MBOX_FIFO_DEPTH; i++) {
              pr_info("mbox_fifo[%d]: %d %d %#x\n", i, (&mbox_fifo[i] == mbox_fifo_wr) ? 1 : 0,
                     (&mbox_fifo[i] == mbox_fifo_rd) ? 1 : 0, mbox_fifo[i]);
            }
          }
        }
        n_words_written++;
        n_words_written_tmp++;

      } // write to mailbox FIFO buffer
    } // while mailbox not empty and FIFO buffer not full
    mbox_fifo_unlock();

    // wake up user space process
    if (n_words_written_tmp) {
      wake_up_interruptible(&mbox_wq);
      if (DEBUG_LEVEL_MBOX > 0)
        pr_info("PULP - MBOX: Wrote %d words to mbox_fifo.\n", n_words_written_tmp);
    }
    // adjust receive interrupt threshold of mailbox interface
    else if (mbox_fifo_full) {
      pr_info("PULP - MBOX: mbox_fifo_full %d\n", mbox_fifo_full);
    }
  } else if (mbox_is & MBOX_IRQ_MASK_ERROR) // mailbox error
    iowrite32(MBOX_IRQ_MASK_ERROR, (void *)((unsigned long)mbox + MBOX_IS_OFFSET_B));
  else // mailbox send interrupt threshold - not used
    iowrite32(MBOX_IRQ_MASK_WRITE, (void *)((unsigned long)mbox + MBOX_IS_OFFSET_B));

  if (DEBUG_LEVEL_MBOX > 0) {
    do_gettimeofday(&time);
    pr_info("PULP - MBOX: IRQ status: %#x. IRQ handled at: %02li:%02li:%02li.\n", mbox_is,
           (time.tv_sec / 3600) % 24, (time.tv_sec / 60) % 60, time.tv_sec % 60);
  }

  return;
}

ssize_t pulp_mbox_read(struct file *filp, char __user *buf, size_t count, loff_t *offp)
{
  int i;
  unsigned mbox_data;
  unsigned req_type;
  unsigned long not_copied, flags;

  mbox_fifo_lock_irqsave(&flags);
  while ((mbox_fifo_wr == mbox_fifo_rd) && !mbox_fifo_full) { // nothing to read
    mbox_fifo_unlock_irqrestore(flags);

    if (filp->f_flags & O_NONBLOCK)
      return -EAGAIN;
    if (wait_event_interruptible(mbox_wq, (mbox_fifo_wr != mbox_fifo_rd) || mbox_fifo_full))
      return -ERESTARTSYS; // signal: tell the fs layer to handle it

    mbox_fifo_lock_irqsave(&flags);
  }

  // mbox_fifo contains data to be read by user
  if (mbox_fifo_wr > mbox_fifo_rd)
    count = min(count, (size_t)(mbox_fifo_wr - mbox_fifo_rd) * sizeof(mbox_fifo[0]));
  else // wrap, return data up to end of FIFO
    count = min(count, (size_t)(mbox_fifo + 2 * MBOX_FIFO_DEPTH - mbox_fifo_rd) * sizeof(mbox_fifo[0]));

  // release the spinlock, copy_to_user can sleep
  mbox_fifo_unlock_irqrestore(flags);

  not_copied = copy_to_user(buf, mbox_fifo_rd, count);

  mbox_fifo_lock_irqsave(&flags);

  // update read pointer
  mbox_fifo_rd = mbox_fifo_rd + (count - not_copied) / sizeof(mbox_fifo[0]);

  // wrap around
  if (mbox_fifo_rd >= (mbox_fifo + 2 * MBOX_FIFO_DEPTH))
    mbox_fifo_rd = mbox_fifo;

  // not full anymore?
  if (mbox_fifo_full && ((count - not_copied) / sizeof(mbox_fifo[0]) > 0)) {
    mbox_fifo_full = 0;

    // if there is data available in the mailbox, read it to mbox_fifo
    // as the interrupt won't be triggered anymore
    while (!(0x1 & ioread32((void *)((unsigned long)pulp_mbox + MBOX_STATUS_OFFSET_B))) && !mbox_fifo_full) {
      // read mailbox
      mbox_data = ioread32((void *)((unsigned long)pulp_mbox + MBOX_RDDATA_OFFSET_B));

      if (n_words_written == n_words_to_write) { // new transfer

        MBOX_GET_REQ_TYPE(req_type, mbox_data);

        if (TO_RUNTIME == req_type) {
          // extract number of words
          MBOX_GET_N_WORDS(n_words_to_write, mbox_data);
          n_words_written = 0;

          continue;
        } else {
          mbox_fifo_unlock_irqrestore(flags);

          if (RAB_UPDATE == req_type) {
            pr_info("PULP: RAB update in MBOX read detected.\n");
            pulp_rab_update(mbox_data);
          } else if (RAB_SWITCH == req_type) {
            pr_info("PULP: RAB switch in MBOX read detected.\n");
            pulp_rab_switch();
          } else {
            pr_info("PULP - MBOX: Unknown request type %d\n", req_type);
          }

          mbox_fifo_lock_irqsave(&flags);
        }
      } else { // write to mailbox FIFO buffer
        // write to mbox_fifo
        *mbox_fifo_wr = mbox_data;

        // update write pointer
        mbox_fifo_wr++;

        // wrap around?
        if (mbox_fifo_wr >= (mbox_fifo + 2 * MBOX_FIFO_DEPTH))
          mbox_fifo_wr = mbox_fifo;
        // full?
        if (mbox_fifo_wr == mbox_fifo_rd)
          mbox_fifo_full = 1;
        if (DEBUG_LEVEL_MBOX > 0) {
          pr_info("PULP - MBOX: Written %#x to mbox_fifo.\n", mbox_data);
          pr_info("PULP - MBOX: mbox_fifo_wr: %d\n", (unsigned)(mbox_fifo_wr - mbox_fifo));
          pr_info("PULP - MBOX: mbox_fifo_rd: %d\n", (unsigned)(mbox_fifo_rd - mbox_fifo));
          pr_info("PULP - MBOX: mbox_fifo_full %d\n", mbox_fifo_full);
          if (DEBUG_LEVEL_MBOX > 1) {
            for (i = 0; i < 2 * MBOX_FIFO_DEPTH; i++) {
              pr_info("mbox_fifo[%d]: %d %d %#x\n", i, (&mbox_fifo[i] == mbox_fifo_wr) ? 1 : 0,
                     (&mbox_fifo[i] == mbox_fifo_rd) ? 1 : 0, mbox_fifo[i]);
            }
          }
        }
        n_words_written++;

      } // write to mailbox FIFO buffer
    } // while mailbox not empty and FIFO buffer not full
  }
  if (DEBUG_LEVEL_MBOX > 0) {
    pr_info("PULP - MBOX: Read from mbox_fifo.\n");
    pr_info("PULP - MBOX: mbox_fifo_wr: %d\n", (unsigned)(mbox_fifo_wr - mbox_fifo));
    pr_info("PULP - MBOX: mbox_fifo_rd: %d\n", (unsigned)(mbox_fifo_rd - mbox_fifo));
    pr_info("PULP - MBOX: mbox_fifo_full %d\n", mbox_fifo_full);
  }
  mbox_fifo_unlock_irqrestore(flags);

  if (DEBUG_LEVEL_MBOX > 0) {
    pr_info("PULP - MBOX: Read %li words from mbox_fifo.\n", (count - not_copied) / sizeof(mbox_fifo[0]));
  }

  if (not_copied)
    return -EFAULT; // bad address
  else
    return count;
}
