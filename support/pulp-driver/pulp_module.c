/*
 * PULP device driver
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
/* --=========================================================================--
 *
 * ██████╗ ██╗   ██╗██╗     ██████╗     ██████╗ ██████╗ ██╗██╗   ██╗███████╗██████╗
 * ██╔══██╗██║   ██║██║     ██╔══██╗    ██╔══██╗██╔══██╗██║██║   ██║██╔════╝██╔══██╗
 * ██████╔╝██║   ██║██║     ██████╔╝    ██║  ██║██████╔╝██║██║   ██║█████╗  ██████╔╝
 * ██╔═══╝ ██║   ██║██║     ██╔═══╝     ██║  ██║██╔══██╗██║╚██╗ ██╔╝██╔══╝  ██╔══██╗
 * ██║     ╚██████╔╝███████╗██║         ██████╔╝██║  ██║██║ ╚████╔╝ ███████╗██║  ██║
 * ╚═╝      ╚═════╝ ╚══════╝╚═╝         ╚═════╝ ╚═╝  ╚═╝╚═╝  ╚═══╝  ╚══════╝╚═╝  ╚═╝
 *
 *
 * Author: Pirmin Vogel - vogelpi@iis.ee.ethz.ch
 *
 * Purpose : Linux kernel-level driver for PULP
 *           RAB management for shared virtual memory between host and PULP
 *
 * --=========================================================================--
 */

/***************************************************************************************/

#include <linux/module.h> /* Needed by all modules */
#include <linux/kernel.h> /* KERN_ALERT, container_of */
#include <linux/kdev_t.h> /* major, minor */
#include <linux/interrupt.h> /* interrupt handling */
#include <linux/workqueue.h> /* schedule non-atomic work */
#include <linux/wait.h> /* wait_queue */
#include <asm/io.h> /* ioremap, iounmap, iowrite32 */
#include <linux/cdev.h> /* cdev struct */
#include <linux/fs.h> /* file_operations struct */
#include <linux/mm.h> /* vm_area_struct struct, page struct, PAGE_SHIFT, page_to_phys */
#include <linux/pagemap.h> /* page_put() */
#include <asm/cacheflush.h> /* __cpuc_flush_dcache_area, outer_cache.flush_range */
#include <asm/uaccess.h> /* copy_to_user, copy_from_user, access_ok */
#include <linux/time.h> /* do_gettimeofday */
#include <linux/ioctl.h> /* ioctl */
#include <linux/slab.h> /* kmalloc */
#include <linux/errno.h> /* errno */
#include <linux/err.h> /* IS_ERR */
#include <linux/sched.h> /* wake_up_interruptible(), TASK_INTERRUPTIBLE */
#include <linux/delay.h> /* udelay */
#include <linux/device.h> // class_create, device_create

/***************************************************************************************/
//#include <linux/wait.h>
#include <linux/ktime.h> /* For ktime_get(), ktime_us_delta() */
/***************************************************************************************/

#include <linux/platform_device.h> /* for device tree stuff*/
#include <linux/device.h>
#include <linux/of_device.h>

#include "pulp_module.h"

#if PLATFORM == JUNO || PLATFORM == TE0808
  #include <asm/compat.h> /* for compat_ioctl */
#endif

#include "pulp_ctrl.h"
#include "pulp_mem.h"
#include "pulp_rab.h"
#include "pulp_dma.h"
#include "pulp_mbox.h"
#include "pulp_profile.h"

#if PLATFORM == TE0808
  #include "pulp_smmu.h"
#endif

#undef ARM
#include <archi/pulp.h>

/***************************************************************************************/

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Pirmin Vogel");
MODULE_DESCRIPTION("PULP driver");

/***************************************************************************************/

// static variables {{{
static PulpDev my_dev;
static struct class *my_class;

static unsigned pulp_rab_ax_log_en = 0;
static MissHandlingMode mh_mode = MH_NONE;

// gpio
static unsigned gpio_value = 0x00000000;

// control
DEFINE_SPINLOCK(ctrl_lock);
static uint32_t active_cluster_mask = 0;
static DECLARE_COMPLETION(ctrl_finished);

// profiling
static ProfileInfo profile_info;

// for DMA
static struct dma_chan *pulp_dma_chan[2];
static DmaCleanup pulp_dma_cleanup[2];
// }}}

// Device Tree {{{
/***********************************************************************************
 *
 * ██████╗ ███████╗██╗   ██╗██╗ ██████╗███████╗    ████████╗██████╗ ███████╗███████╗
 * ██╔══██╗██╔════╝██║   ██║██║██╔════╝██╔════╝    ╚══██╔══╝██╔══██╗██╔════╝██╔════╝
 * ██║  ██║█████╗  ██║   ██║██║██║     █████╗         ██║   ██████╔╝█████╗  █████╗
 * ██║  ██║██╔══╝  ╚██╗ ██╔╝██║██║     ██╔══╝         ██║   ██╔══██╗██╔══╝  ██╔══╝
 * ██████╔╝███████╗ ╚████╔╝ ██║╚██████╗███████╗       ██║   ██║  ██║███████╗███████╗
 * ╚═════╝ ╚══════╝  ╚═══╝  ╚═╝ ╚═════╝╚══════╝       ╚═╝   ╚═╝  ╚═╝╚══════╝╚══════╝
 *
 * The IRQ is allocated through the device tree at boot time. In order to
 * register the interrupt service routine, request_irq() needs the interrupt index
 * reserved at boot time instead of the physical IRQ. This can be obtained through
 * the device tree. The addresses we still "pass" through the header files.
 *
 ***********************************************************************************/
// connect to the device tree
static struct of_device_id pulp_of_match[] = { {
                                                 .compatible = "pulp,bigpulp",
                                               },
                                               { /* sentinel */ } };

MODULE_DEVICE_TABLE(of, pulp_of_match);

#if PLATFORM == TE0808

/**
   * Compare device name with string.
   *
   * This function compares the name of a device with a string provided in data.
   * To protect the system from faulty device trees, the comparison is aborted
   * if a NULL pointer would have to be derefenced.
   *
   * @param   dev  Pointer to device struct of interest
   * @param   data Pointer to name of interest.
   *
   * @return  non-zero on success, 0 if the name does not match the string.
   */
static int compare_dev_name(struct device *dev, void *data)
{
  const char *name = data;

  // make sure to not dereference NULL pointers - in case we start with device zero
  if (dev->of_node == NULL) {
    if (DEBUG_LEVEL_OF > 0)
      printk(KERN_INFO "PULP: No of_node for:\n - dev %p\n", dev);
    return 0;
  } else if (dev->of_node->name == NULL) {
    if (DEBUG_LEVEL_OF > 0)
      printk(KERN_INFO "PULP: No of_node->name for:\n - dev %p\n - of_node %p", dev, dev->of_node);
    return 0;
  } else
    return sysfs_streq(name, dev->of_node->name);
}

/**
   * Find a device by name in the device tree.
   *
   * @param   name Name of the device to search for
   * @param   dev  Pointer to struct device pointer to fill
   *
   * @return  0 on success, -ENXIO if the device cannot be found.
   */
static int find_dev(const char *name, struct device **dev)
{
  // search the device on the platform bus using the custom compare function
  *dev = bus_find_device(&platform_bus_type, NULL, (void *)name, compare_dev_name);
  if (dev == NULL)
    return -ENODEV;

  return 0;
}
#endif

// method definition
static int pulp_probe(struct platform_device *pdev)
{
  int i;
  int *irq_vars[] = {
    &my_dev.irq_mbox,
    &my_dev.irq_rab_host_miss,
    &my_dev.irq_rab_host_multi,
    &my_dev.irq_rab_host_prot,
    &my_dev.irq_rab_pulp_miss,
    &my_dev.irq_rab_pulp_multi,
    &my_dev.irq_rab_pulp_prot,
    &my_dev.irq_eoc,
    &my_dev.irq_rab_mhr_full
  };
#if !INTR_REG_BASE_ADDR
  char *irq_names[] = {
    "mailbox",
    "RAB Host miss",
    "RAB Host multi hit",
    "RAB Host prot violation",
    "RAB PULP miss",
    "RAB PULP multi hit",
    "RAB PULP prot violation",
    "end of computation",
    "RAB MHR full"
  };
#endif

#if PLATFORM == TE0808
  int err;
#endif

  printk(KERN_ALERT "PULP: Probing device.\n");

#if PLATFORM == TE0808
  // Get struct device pointer
  err = find_dev("pulp", &my_dev.dt_dev_ptr);
  if (err) {
    printk(KERN_WARNING "PULP: Could not get device struct pointer.\n");
    return -ENODEV;
  }

  if (DEBUG_LEVEL_OF > 0) {
    printk(KERN_INFO "PULP: &(pdev->dev)      = %p\n", &(pdev->dev));
    printk(KERN_INFO "PULP: my_dev.dt_dev_ptr = %p\n", my_dev.dt_dev_ptr);
  }
#endif

  // store device struct pointer
  my_dev.dt_dev_ptr = &(pdev->dev);

  // IRQs
#if INTR_REG_BASE_ADDR
  // events are shared via separate register, single IRQ
  my_dev.intr_reg_irq = platform_get_irq(pdev, 0);
  if (my_dev.intr_reg_irq <= 0) {
    printk(KERN_WARNING "PULP: Could not allocate general IRQ resource.\n");
    return -ENODEV;
  }
  if (DEBUG_LEVEL_OF > 0) {
    printk(KERN_INFO "PULP: Allocated general IRQ %d", my_dev.intr_reg_irq);
  }
  for (i = 0; i < sizeof(irq_vars) / sizeof(int *); ++i) {
    *irq_vars[i] = -1;
  }
#else
  // separate IRQs are used per event
  for (i = 0; i < sizeof(irq_vars) / sizeof(int *); ++i) {
    int irq = platform_get_irq(pdev, i);
    if (irq <= 0) {
      printk(KERN_WARNING "PULP: Could not allocate IRQ resource for %s.\n", irq_names[i]);
      *irq_vars[i] = -1;
      return -ENODEV;
    }
    *irq_vars[i] = irq;
    if (DEBUG_LEVEL_OF > 0) {
      printk(KERN_INFO "PULP: Allocated IRQ %d for %s", irq, irq_names[i]);
    }
  }
  my_dev.intr_reg_irq = -1;
#endif

#if PLATFORM == TE0808
  // DMA Channels

  // TX: Host -> PULP
  pulp_dma_chan[0] = dma_request_slave_channel(my_dev.dt_dev_ptr, "tx_channel");
  if (pulp_dma_chan[0] == NULL) {
    printk(KERN_WARNING "PULP: Could not allocate TX DMA channel.\n");
    return -ENODEV;
  }

  // RX: Host -> PULP
  pulp_dma_chan[1] = dma_request_slave_channel(my_dev.dt_dev_ptr, "rx_channel");
  if (pulp_dma_chan[1] == NULL) {
    printk(KERN_WARNING "PULP: Could not allocate RX DMA channel.\n");
    dma_release_channel(pulp_dma_chan[0]);
    return -ENODEV;
  }
#endif

  return 0;
}

static int pulp_remove(struct platform_device *pdev)
{
  printk(KERN_ALERT "PULP: Removing device.\n");

#if PLATFORM == TE0808
  // DMA Channels
  dma_release_channel(pulp_dma_chan[0]);
  dma_release_channel(pulp_dma_chan[1]);
#endif

  return 0;
}

// (un-)register to/from the device tree
static struct platform_driver pulp_platform_driver = {
  .probe  = pulp_probe,
  .remove = pulp_remove,
  .driver = {
    .name = "pulp",
    .owner = THIS_MODULE,
    .of_match_table = pulp_of_match,
    },
};

/***************************************************************************************/

// }}}

/***********************************************************************************
 * SYSFS
 ***********************************************************************************/

static ssize_t num_clusters_show(struct device *dev, struct device_attribute *attr, char *buf)
{
  int len;

  len = sprintf(buf, "%d\n", N_CLUSTERS);
  return len;
}

static ssize_t host_clk_start_show(struct device *dev, struct device_attribute *attr, char *buf)
{
  int i;
  int len = 0;

  for (i = 0; i < N_CLUSTERS; ++i) {
    len = sprintf(buf + len, "%llu\n", profile_info.clusters[i].host_clk_start);
  }
  return len;
}

static ssize_t host_clk_finish_show(struct device *dev, struct device_attribute *attr, char *buf)
{
  int i;
  int len = 0;

  for (i = 0; i < N_CLUSTERS; ++i) {
    len += sprintf(buf + len, "%llu\n", profile_info.clusters[i].host_clk_finish);
  }
  return len;
}

static ssize_t host_time_diff_show(struct device *dev, struct device_attribute *attr, char *buf)
{
  int i;
  uint64_t diff = 0;
  int len = 0;

  for (i = 0; i < N_CLUSTERS; ++i) {
    if (profile_info.clusters[i].host_time_finish) {
      diff = U64_COUNTER_DIFF(profile_info.clusters[i].host_time_start, profile_info.clusters[i].host_time_finish);
    } else {
      diff = 0;
    }

    len += sprintf(buf + len, "%llu\n", diff);
  }
  return len;
}
static ssize_t accel_clk_diff_show(struct device *dev, struct device_attribute *attr, char *buf)
{
  int i;
  uint64_t diff = 0;
  int len = 0;

  for (i = 0; i < N_CLUSTERS; ++i) {
    if (profile_info.clusters[i].accel_clk_finish) {
      diff = U64_COUNTER_DIFF(profile_info.clusters[i].accel_clk_start, profile_info.clusters[i].accel_clk_finish);
    } else {
      diff = 0;
    }
    len += sprintf(buf + len, "%llu\n", diff);
  }
  return len;
}

// sysfs attributes
static DEVICE_ATTR_RO(num_clusters);
static DEVICE_ATTR_RO(host_clk_start);
static DEVICE_ATTR_RO(host_clk_finish);
static DEVICE_ATTR_RO(host_time_diff);
static DEVICE_ATTR_RO(accel_clk_diff);

static struct attribute *pulp_attrs[] = {
  &dev_attr_num_clusters.attr,   &dev_attr_host_clk_start.attr, &dev_attr_host_clk_finish.attr,
  &dev_attr_host_time_diff.attr, &dev_attr_accel_clk_diff.attr, NULL,
};

// attribute groups
ATTRIBUTE_GROUPS(pulp);

// helper functions
/***********************************************************************************/

static int vm_set_mh_mode(MissHandlingMode mh_md, void *ptr)
{
  int retval = 0;
  unsigned request[2];
  unsigned int bytes_left;

  // disable old mode
  switch (mh_mode) {
  case MH_HOST_RAB:
    pulp_rab_mh_dis();
    break;
  case MH_HOST_SMMU:
#if PLATFORM == TE0808
    pulp_smmu_dis(&my_dev);
#endif
    break;
  case MH_ACCEL:
    pulp_rab_soc_mh_dis(my_dev.rab_config);
    break;
  default:
    break;
  }

  // enable new mode
  switch (mh_md) {
  case MH_NONE:
    break;
  case MH_HOST_RAB:
    bytes_left = copy_from_user((void *)request, (void __user *)ptr, 2 * sizeof(unsigned));
    if (bytes_left) {
      retval = -EFAULT;
    } else {
      retval = pulp_rab_mh_ena(my_dev.rab_config, request[0], request[1]);
    }
    break;
  case MH_HOST_SMMU:
#if PLATFORM == TE0808
    bytes_left = copy_from_user((void *)request, (void __user *)ptr, sizeof(unsigned));
    if (bytes_left) {
      retval = -EFAULT;
    } else {
      retval = pulp_smmu_ena(&my_dev, BIT_GET(request[0], (SMMU_FLAGS_CC | SMMU_FLAGS_SHPT_EMU)));
    }
#else
    retval = -EINVAL;
#endif
    break;
  case MH_ACCEL:
    bytes_left = copy_from_user((void *)request, (void __user *)ptr, sizeof(unsigned));
    if (bytes_left) {
      retval = -EFAULT;
    } else {
      retval = pulp_rab_soc_mh_ena(my_dev.rab_config, request[0]);
    }
    break;
  default:
    retval = -EINVAL;
  }

  if (retval) {
    mh_mode = MH_NONE;
  } else {
    mh_mode = mh_md;
  }

  return retval;
}

static MissHandlingMode vm_get_mh_mode(void)
{
  return mh_mode;
}

/**********************************************************************************/

// VM_RESERVERD for mmap
#ifndef VM_RESERVED
  #define VM_RESERVED (VM_DONTEXPAND | VM_DONTDUMP)
#endif

// method declarations {{{
static int pulp_open(struct inode *inode, struct file *filp);
static int pulp_release(struct inode *p_inode, struct file *filp);
static int pulp_mmap(struct file *filp, struct vm_area_struct *vma);
static long pulp_ioctl(struct file *filp, unsigned int cmd, unsigned long arg);
#ifdef CONFIG_COMPAT
static long pulp_compat_ioctl(struct file *filp, unsigned int cmd, unsigned long arg);
#endif

static irqreturn_t pulp_isr(int irq, void *ptr);

// }}}

// important structs {{{
struct file_operations pulp_fops = {
  .owner = THIS_MODULE,
  .open = pulp_open,
  .release = pulp_release,
  .read = pulp_mbox_read,
  .mmap = pulp_mmap,
  .unlocked_ioctl = pulp_ioctl,
#ifdef CONFIG_COMPAT
  .compat_ioctl = pulp_compat_ioctl,
#endif
};
// }}}

// methods definitions

// init {{{
/***********************************************************************************
 *
 * ██╗███╗   ██╗██╗████████╗
 * ██║████╗  ██║██║╚══██╔══╝
 * ██║██╔██╗ ██║██║   ██║
 * ██║██║╚██╗██║██║   ██║
 * ██║██║ ╚████║██║   ██║
 * ╚═╝╚═╝  ╚═══╝╚═╝   ╚═╝
 *
 ***********************************************************************************/
static int __init pulp_init(void)
{
  int i, err;
  struct device *my_device;
#if !INTR_REG_BASE_ADDR
  int *irq_vars[] = {
    &my_dev.irq_mbox,
    &my_dev.irq_rab_host_miss,
    &my_dev.irq_rab_host_prot,
    &my_dev.irq_rab_host_multi,
    &my_dev.irq_rab_pulp_miss,
    &my_dev.irq_rab_pulp_prot,
    &my_dev.irq_rab_pulp_multi,
    &my_dev.irq_eoc,
    &my_dev.irq_rab_mhr_full
  };
#endif

  // initialize profiling structure
  for (i = 0; i < MAX_CLUSTERS; ++i) {
    profile_info.clusters[i].host_clk_start = 0;
    profile_info.clusters[i].host_clk_finish = 0;
    profile_info.clusters[i].host_time_start = 0;
    profile_info.clusters[i].host_time_finish = 0;
  }

  printk(KERN_ALERT "PULP: Loading device driver.\n");

  my_dev.minor = 0;

  /*
   *  init module char device
   */
  // get dynamic device numbers
  err = alloc_chrdev_region(&my_dev.dev, my_dev.minor, PULP_N_DEV_NUMBERS, "PULP");
  if (err) {
    printk(KERN_WARNING "PULP: Can't get major device number.\n");
    goto fail_alloc_chrdev_region;
  }
  // create class struct
  my_class = class_create(THIS_MODULE, "PULP");
  if (IS_ERR(my_class)) {
    printk(KERN_WARNING "PULP: Error creating class.\n");
    err = -1;
    goto fail_create_class;
  }
  // create device and register it with sysfs
  my_device = device_create_with_groups(my_class, NULL, my_dev.dev, NULL, pulp_groups, "PULP");
  if (IS_ERR(my_device)) {
    printk(KERN_WARNING "PULP: Error creating device.\n");
    err = -1;
    goto fail_create_device;
  }
  printk(KERN_INFO "PULP: Device created.\n");

  my_dev.major = MAJOR(my_dev.dev);
  my_dev.fops = &pulp_fops;

  /*
   *  struct cdev
   */
  cdev_init(&my_dev.cdev, my_dev.fops);
  my_dev.cdev.owner = THIS_MODULE;

  /**********
   *
   * ioremap
   *
   **********/
  // map the GPIO first so we can use it to enable PULP
  my_dev.gpio = ioremap_nocache(H_GPIO_BASE_ADDR, H_GPIO_SIZE_B);
  if (DEBUG_LEVEL_PULP > 0)
    printk(KERN_INFO "PULP: Host GPIO mapped to virtual kernel space @ %#lx.\n", (long unsigned int)my_dev.gpio);

  // remove GPIO reset and enable the clock
  gpio_value = 0;
#if GPIO_RST_N >= 0
  BIT_SET(gpio_value, BF_MASK_GEN(GPIO_RST_N, 1));
#endif
#if GPIO_CLK_EN >= 0
  BIT_SET(gpio_value, BF_MASK_GEN(GPIO_CLK_EN, 1));
#endif
  iowrite32(gpio_value, (void *)((unsigned long)my_dev.gpio + GPIO_HOST2PULP_OFFSET));

#ifdef GPIO_EXT_RESET_ADDR
  my_dev.gpio_reset = ioremap_nocache(GPIO_EXT_RESET_ADDR, GPIO_EXT_RESET_SIZE_B);
  if (DEBUG_LEVEL_PULP > 0)
    printk(KERN_INFO "PULP: Reset GPIO mapped to virtual kernel space @ %#lx.\n", (long unsigned int)my_dev.gpio_reset);
#endif

#if CLKING_BASE_ADDR
  my_dev.clking = ioremap_nocache(CLKING_BASE_ADDR, CLKING_SIZE_B);
  if (DEBUG_LEVEL_PULP > 0)
    printk(KERN_INFO "PULP: clking mapped to virtual kernel space @ %#lx.\n", (long unsigned int)my_dev.clking);
#endif

#if PLATFORM == TE0808
  my_dev.cci = ioremap_nocache(CCI_BASE_ADDR, CCI_SIZE_B);
  if (DEBUG_LEVEL_PULP > 0)
    printk(KERN_INFO "PULP: CCI mapped to virtual kernel space @ %#lx.\n", (long unsigned int)my_dev.cci);

  /*
     * Make sure to enable AxDOMAIN shareability overriding on Slave 0 (HPC0/1 PL ports).
     *
     * Note: The CCI does not accept any shareable transactions from the SMMU. Thus, we
     * must force the SMMU to inject non-shareable transactions into CCI only. To enable
     * coherency, we then must configure the CCI to force the transactions coming from
     * the HPC0/1 ports to be shareable.
     *
     * This requires non-secure access to CCI registers being enabled.
     */
  iowrite32(0x3, (void *)((unsigned long)my_dev.cci + CCI_SHOR_S0_OFFSET_B));

  my_dev.smmu = ioremap_nocache(SMMU_BASE_ADDR, SMMU_SIZE_B);
  if (DEBUG_LEVEL_PULP > 0)
    printk(KERN_INFO "PULP: SMMU mapped to virtual kernel space @ %#lx.\n", (long unsigned int)my_dev.smmu);
  err = pulp_smmu_init(&my_dev);
  if (err) {
    printk(KERN_WARNING "PULP: Could not initialize SMMU.\n");
    goto fail_smmu_init;
  }
#endif // PLATFORM

#if INTR_REG_BASE_ADDR
  my_dev.intr_reg = ioremap_nocache(INTR_REG_BASE_ADDR, INTR_REG_SIZE_B);
  if (DEBUG_LEVEL_PULP > 0)
    printk(KERN_INFO "PULP: Interrupt register mapped to virtual kernel space @ %#lx.\n",
           (long unsigned int)my_dev.intr_reg);
#endif

#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX
  my_dev.slcr = ioremap_nocache(SLCR_BASE_ADDR, SLCR_SIZE_B);
  if (DEBUG_LEVEL_PULP > 0)
    printk(KERN_INFO "PULP: Zynq SLCR mapped to virtual kernel space @ %#lx.\n", (long unsigned int)my_dev.slcr);

  // make sure to enable the PL clock
  if (!BF_GET(ioread32((void *)((unsigned long)my_dev.slcr + SLCR_FPGA0_THR_STA_OFFSET_B)), 16, 1)) {
    iowrite32(0x0, (void *)((unsigned long)my_dev.slcr + SLCR_FPGA0_THR_CNT_OFFSET_B));

    if (!BF_GET(ioread32((void *)((unsigned long)my_dev.slcr + SLCR_FPGA0_THR_STA_OFFSET_B)), 16, 1)) {
      printk(KERN_WARNING "PULP: Could not enable reference clock for PULP.\n");
      goto fail_ioremap;
    }
  }
#endif // PLATFORM

#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX || PLATFORM == TE0808
  my_dev.uart = ioremap_nocache(HOST_UART_BASE_ADDR, HOST_UART_SIZE_B);
  if (DEBUG_LEVEL_PULP > 0)
    printk(KERN_INFO "PULP: Zynq UART control register mapped to virtual kernel space @ %#lx.\n",
           (long unsigned int)my_dev.uart);

  // make sure to enable automatic flow control on PULP -> Host UART
  iowrite32(0x20, (void *)((unsigned long)my_dev.uart + MODEM_CTRL_REG0_OFFSET_B));
#endif // PLATFORM

#if RAB_AX_LOG_EN == 1
  my_dev.rab_ar_log = ioremap_nocache(RAB_AR_LOG_BASE_ADDR, RAB_AX_LOG_SIZE_B);
  if (DEBUG_LEVEL_PULP > 0)
    printk(KERN_INFO "PULP: RAB AR log mapped to virtual kernel space @ %#lx.\n", (long unsigned int)my_dev.rab_ar_log);

  my_dev.rab_aw_log = ioremap_nocache(RAB_AW_LOG_BASE_ADDR, RAB_AX_LOG_SIZE_B);
  if (DEBUG_LEVEL_PULP > 0)
    printk(KERN_INFO "PULP: RAB AW log mapped to virtual kernel space @ %#lx.\n", (long unsigned int)my_dev.rab_aw_log);

  #if PLATFORM == JUNO //|| PLATFORM == TE0808
  my_dev.rab_cfg_log = ioremap_nocache(RAB_CFG_LOG_BASE_ADDR, RAB_CFG_LOG_SIZE_B);
  if (DEBUG_LEVEL_PULP > 0)
    printk(KERN_INFO "PULP: RAB CFG log mapped to virtual kernel space @ %#lx.\n", (long unsigned int)my_dev.rab_cfg_log);
  #endif
#endif // RAB_AX_LOG_EN == 1

  // RAB config
  my_dev.rab_config = ioremap_nocache(RAB_CONFIG_BASE_ADDR, RAB_CONFIG_SIZE_B);
  if (DEBUG_LEVEL_PULP > 0)
    printk(KERN_INFO "PULP: RAB config mapped to virtual kernel space @ %#lx.\n", (long unsigned int)my_dev.rab_config);
  err = pulp_rab_init(&my_dev);
  if (err) {
    printk(KERN_WARNING "PULP: RAB initialization failed.\n");
    goto fail_ioremap;
  }

  // PULP timer used for RAB profiling
  my_dev.clusters = ioremap_nocache(PULP_H_BASE_ADDR, CLUSTERS_SIZE_B);
  if (DEBUG_LEVEL_PULP > 0)
    printk(KERN_INFO "PULP: Clusters mapped to virtual kernel space @ %#lx.\n", (long unsigned int)my_dev.clusters);

  // actually not needed - handled in user space
  my_dev.soc_periph = ioremap_nocache(SOC_PERIPHERALS_H_BASE_ADDR, SOC_PERIPHERALS_SIZE_B);
  if (DEBUG_LEVEL_PULP > 0)
    printk(KERN_INFO "PULP: SoC peripherals mapped to virtual kernel space @ %#lx.\n", (long unsigned int)my_dev.soc_periph);

  // actually not needed - handled in user space
  my_dev.l2_mem = ioremap_nocache(L2_MEM_H_BASE_ADDR, L2_MEM_SIZE_B);
  if (DEBUG_LEVEL_PULP > 0)
    printk(KERN_INFO "PULP: L2 memory mapped to virtual kernel space @ %#lx.\n", (long unsigned int)my_dev.l2_mem);

  // for profiling
  my_dev.l3_mem = ioremap_nocache(L3_MEM_H_BASE_ADDR, L3_MEM_SIZE_B);
  if (my_dev.l3_mem == NULL) {
    printk(KERN_WARNING "PULP: ioremap_nocache not allowed for non-reserved RAM.\n");
    err = -EPERM;
    goto fail_ioremap;
  }
  if (DEBUG_LEVEL_PULP > 0)
    printk(KERN_INFO "PULP: Shared L3 memory (DRAM) mapped to virtual kernel space @ %#lx.\n",
           (long unsigned int)my_dev.l3_mem);

  // initialialize mailbox
  my_dev.mbox = ioremap_nocache(MBOX_H_BASE_ADDR, MBOX_SIZE_B * 2);
  if (DEBUG_LEVEL_PULP > 0)
    printk(KERN_INFO "PULP: Mailbox mapped to virtual kernel space @ %#lx.\n", (long unsigned int)my_dev.mbox);
  pulp_mbox_init(my_dev.mbox);

  /*********************
   *
   * interrupts
   *
   *********************/
  // register the device to get the interrupt index
  err = platform_driver_register(&pulp_platform_driver);
  if (err) {
    printk(KERN_WARNING "PULP: Error registering platform driver: %d\n", err);
    goto fail_register_platform_driver;
  }

  // request interrupts and install top-half handler
#if INTR_REG_BASE_ADDR
  err = request_irq(my_dev.intr_reg_irq, pulp_isr, 0, "PULP", NULL);
  if (err) {
    printk(KERN_WARNING "PULP: Error requesting IRQ: errno %d.\n", err);
    goto fail_request_irq;
  }
#else
  for (i = 0; i < sizeof(irq_vars) / sizeof(int *); ++i) {
    if (*irq_vars[i] == -1)
      continue;
    err = request_irq(*irq_vars[i], pulp_isr, 0, "PULP", NULL);
    if (err) {
      printk(KERN_WARNING "PULP: Error requesting IRQ %d.\n", *irq_vars[i]);
      goto fail_request_irq;
    }
  }
#endif

  /************************************
   *
   *  request DMA channels
   *
   ************************************/
#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX
  err = pulp_dma_chan_req(&pulp_dma_chan[0], 0);
  if (err) {
    printk(KERN_WARNING "PULP: Error requesting DMA channel.\n");
    goto fail_request_dma;
  }
  err = pulp_dma_chan_req(&pulp_dma_chan[1], 1);
  if (err) {
    printk(KERN_WARNING "PULP: Error requesting DMA channel.\n");
    goto fail_request_dma;
  }
#endif // PLATFORM

  /************************************
   *
   *  tell the kernel about the device
   *
   ************************************/
  err = cdev_add(&my_dev.cdev, my_dev.dev, PULP_N_DEV_NUMBERS);
  if (err) {
    printk(KERN_WARNING "PULP: Error registering the device.\n");
    goto fail_cdev_add;
  }
  printk(KERN_INFO "PULP: Device registered.\n");

  return 0;

  /*
   * error handling
   */
  cdev_del(&my_dev.cdev);
fail_cdev_add:
#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX
  pulp_dma_chan_clean(pulp_dma_chan[1]);
  pulp_dma_chan_clean(pulp_dma_chan[0]);
fail_request_dma:
#endif // PLATFORM
#if INTR_REG_BASE_ADDR
  free_irq(my_dev.intr_reg_irq, NULL);
#else
  if (my_dev.irq_mbox != -1)
    free_irq(my_dev.irq_mbox, NULL);
  if (my_dev.irq_rab_host_miss != -1)
    free_irq(my_dev.irq_rab_host_miss, NULL);
  if (my_dev.irq_rab_host_multi != -1)
    free_irq(my_dev.irq_rab_host_multi, NULL);
  if (my_dev.irq_rab_host_prot != -1)
    free_irq(my_dev.irq_rab_host_prot, NULL);
  if (my_dev.irq_rab_pulp_miss != -1)
    free_irq(my_dev.irq_rab_pulp_miss, NULL);
  if (my_dev.irq_rab_pulp_multi != -1)
    free_irq(my_dev.irq_rab_pulp_multi, NULL);
  if (my_dev.irq_rab_pulp_prot != -1)
    free_irq(my_dev.irq_rab_pulp_prot, NULL);
  if (my_dev.irq_eoc != -1)
    free_irq(my_dev.irq_eoc, NULL);
  if (my_dev.irq_rab_mhr_full != -1)
    free_irq(my_dev.irq_rab_mhr_full, NULL);
#endif
fail_request_irq:
  platform_driver_unregister(&pulp_platform_driver);
fail_register_platform_driver:
  iounmap(my_dev.mbox);
  iounmap(my_dev.l3_mem);
  iounmap(my_dev.l2_mem);
  iounmap(my_dev.soc_periph);
  iounmap(my_dev.clusters);
#if defined(PROFILE_RAB_STR) || defined(PROFILE_RAB_MH)
  pulp_rab_prof_free();
#endif
  iounmap(my_dev.rab_config);
#if RAB_AX_LOG_EN == 1
  #if PLATFORM == JUNO //|| PLATFORM == TE0808
  iounmap(my_dev.rab_cfg_log);
  #endif
  pulp_rab_ax_log_free();
  iounmap(my_dev.rab_aw_log);
  iounmap(my_dev.rab_ar_log);
#endif
#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX || PLATFORM == TE0808
  iounmap(my_dev.uart);
#endif
#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX
  iounmap(my_dev.slcr);
#endif
#if INTR_REG_BASE_ADDR
  iounmap(my_dev.intr_reg);
#endif
#if PLATFORM == TE0808
fail_smmu_init:
  iounmap(my_dev.smmu);
  iounmap(my_dev.cci);
#endif // PLATFORM
#if CLKING_BASE_ADDR
  iounmap(my_dev.clking);
#endif
#ifdef GPIO_EXT_RESET_ADDR
  iounmap(my_dev.gpio_reset);
#endif
  iounmap(my_dev.gpio);
fail_ioremap:
  device_destroy(my_class, my_dev.dev);
fail_create_device:
  class_destroy(my_class);
fail_create_class:
  unregister_chrdev_region(my_dev.dev, 1);
fail_alloc_chrdev_region:
  return err;
}
module_init(pulp_init);
// }}}

// exit {{{
/***********************************************************************************
 *
 * ███████╗██╗  ██╗██╗████████╗
 * ██╔════╝╚██╗██╔╝██║╚══██╔══╝
 * █████╗   ╚███╔╝ ██║   ██║
 * ██╔══╝   ██╔██╗ ██║   ██║
 * ███████╗██╔╝ ██╗██║   ██║
 * ╚══════╝╚═╝  ╚═╝╚═╝   ╚═╝
 *
 ***********************************************************************************/
static void __exit pulp_exit(void)
{
  unsigned gpio;

  pulp_mbox_clear();

  printk(KERN_ALERT "PULP: Unloading device driver.\n");

  cdev_del(&my_dev.cdev);

#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX
  pulp_dma_chan_clean(pulp_dma_chan[1]);
  pulp_dma_chan_clean(pulp_dma_chan[0]);
#endif // PLATFORM

  // deregister
#if INTR_REG_BASE_ADDR
  free_irq(my_dev.intr_reg_irq, NULL);
#else
  if (my_dev.irq_mbox != -1)
    free_irq(my_dev.irq_mbox, NULL);
  if (my_dev.irq_rab_host_miss != -1)
    free_irq(my_dev.irq_rab_host_miss, NULL);
  if (my_dev.irq_rab_host_multi != -1)
    free_irq(my_dev.irq_rab_host_multi, NULL);
  if (my_dev.irq_rab_host_prot != -1)
    free_irq(my_dev.irq_rab_host_prot, NULL);
  if (my_dev.irq_rab_pulp_miss != -1)
    free_irq(my_dev.irq_rab_pulp_miss, NULL);
  if (my_dev.irq_rab_pulp_multi != -1)
    free_irq(my_dev.irq_rab_pulp_multi, NULL);
  if (my_dev.irq_rab_pulp_prot != -1)
    free_irq(my_dev.irq_rab_pulp_prot, NULL);
  if (my_dev.irq_eoc != -1)
    free_irq(my_dev.irq_eoc, NULL);
  if (my_dev.irq_rab_mhr_full != -1)
    free_irq(my_dev.irq_rab_mhr_full, NULL);
#endif
  platform_driver_unregister(&pulp_platform_driver);

  // disable PULP
  gpio = 0;
  iowrite32(gpio, (void *)((unsigned long)my_dev.gpio + GPIO_HOST2PULP_OFFSET));

#if defined(PROFILE_RAB_STR) || defined(PROFILE_RAB_MH)
  pulp_rab_prof_free();
#endif

  // unmap memory
  iounmap(my_dev.mbox);
  iounmap(my_dev.l3_mem);
  iounmap(my_dev.l2_mem);
  iounmap(my_dev.soc_periph);
  iounmap(my_dev.clusters);
  iounmap(my_dev.rab_config);
#if RAB_AX_LOG_EN == 1
  pulp_rab_ax_log_free();
  iounmap(my_dev.rab_ar_log);
  iounmap(my_dev.rab_aw_log);
  #if PLATFORM == JUNO //|| PLATFORM == TE0808
  iounmap(my_dev.rab_cfg_log);
  #endif
#endif
#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX || PLATFORM == TE0808
  iounmap(my_dev.uart);
#endif
#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX
  iounmap(my_dev.slcr);
#endif
#if INTR_REG_BASE_ADDR
  iounmap(my_dev.intr_reg);
#endif
#if PLATFORM == TE0808
  iounmap(my_dev.smmu);
  iounmap(my_dev.cci);
#endif
#if CLKING_BASE_ADDR
  iounmap(my_dev.clking);
#endif
#ifdef GPIO_EXT_RESET_ADDR
  iounmap(my_dev.gpio_reset);
#endif
  iounmap(my_dev.gpio);

  device_destroy(my_class, my_dev.dev);
  class_destroy(my_class);
  unregister_chrdev_region(my_dev.dev, 1);
}
module_exit(pulp_exit);
// }}}

// open {{{
/***********************************************************************************
 *
 *  ██████╗ ██████╗ ███████╗███╗   ██╗
 * ██╔═══██╗██╔══██╗██╔════╝████╗  ██║
 * ██║   ██║██████╔╝█████╗  ██╔██╗ ██║
 * ██║   ██║██╔═══╝ ██╔══╝  ██║╚██╗██║
 * ╚██████╔╝██║     ███████╗██║ ╚████║
 *  ╚═════╝ ╚═╝     ╚══════╝╚═╝  ╚═══╝
 *
 ***********************************************************************************/

int pulp_open(struct inode *inode, struct file *filp)
{
  // get a pointer to the PulpDev structure
  PulpDev *dev;
  dev = container_of(inode->i_cdev, PulpDev, cdev);
  filp->private_data = dev;

  // init local structures
  vm_set_mh_mode(MH_NONE, NULL);
  pulp_mbox_set_mode(MBOX_DRIVER);

  // // trim to 0 the length of the device if open is write_only
  // if ((filp->f_flags & O_ACCMODE) == O_WRONLY) {
  //
  // }

  printk(KERN_INFO "PULP: Device opened.\n");

  return 0;
}
// }}}

// release {{{
/***********************************************************************************
 *
 * ██████╗ ███████╗██╗     ███████╗ █████╗ ███████╗███████╗
 * ██╔══██╗██╔════╝██║     ██╔════╝██╔══██╗██╔════╝██╔════╝
 * ██████╔╝█████╗  ██║     █████╗  ███████║███████╗█████╗
 * ██╔══██╗██╔══╝  ██║     ██╔══╝  ██╔══██║╚════██║██╔══╝
 * ██║  ██║███████╗███████╗███████╗██║  ██║███████║███████╗
 * ╚═╝  ╚═╝╚══════╝╚══════╝╚══════╝╚═╝  ╚═╝╚══════╝╚══════╝
 *
 ***********************************************************************************/

int pulp_release(struct inode *p_inode, struct file *filp)
{
  // release local structures
  vm_set_mh_mode(MH_NONE, NULL);
  pulp_mbox_clear();
  pulp_mbox_set_mode(MBOX_OFF);
  pulp_rab_release(false);

  // reset GPIO
  gpio_value = 0;
#if GPIO_RST_N >= 0
  BIT_SET(gpio_value, BF_MASK_GEN(GPIO_RST_N, 1));
#endif
#if GPIO_CLK_EN >= 0
  BIT_SET(gpio_value, BF_MASK_GEN(GPIO_CLK_EN, 1));
#endif
  iowrite32(gpio_value, (void *)((unsigned long)my_dev.gpio + GPIO_HOST2PULP_OFFSET));

  printk(KERN_INFO "PULP: Device released.\n");

  return 0;
}
// }}}

// mmap {{{
/***********************************************************************************
 *
 * ███╗   ███╗███╗   ███╗ █████╗ ██████╗
 * ████╗ ████║████╗ ████║██╔══██╗██╔══██╗
 * ██╔████╔██║██╔████╔██║███████║██████╔╝
 * ██║╚██╔╝██║██║╚██╔╝██║██╔══██║██╔═══╝
 * ██║ ╚═╝ ██║██║ ╚═╝ ██║██║  ██║██║
 * ╚═╝     ╚═╝╚═╝     ╚═╝╚═╝  ╚═╝╚═╝
 *
 ***********************************************************************************/
int pulp_mmap(struct file *filp, struct vm_area_struct *vma)
{
  unsigned long base_addr; // base address to use for the remapping
  unsigned long size_b; // size for the remapping
  unsigned long off; // address offset in VMA
  unsigned long physical; // PFN of physical page
  unsigned long vsize;
  unsigned long psize;
  char type[12];
  int io_remap;

  off = (vma->vm_pgoff) << PAGE_SHIFT;

  /*
   * based on the offset, set the proper base_addr and size_b, and adjust off
   */
  // PULP internals
  if (off < CLUSTERS_SIZE_B) {
    // Clusters
    base_addr = PULP_H_BASE_ADDR;
    size_b = CLUSTERS_SIZE_B;
    strcpy(type, "Clusters");
  } else if (off < (CLUSTERS_SIZE_B + SOC_PERIPHERALS_SIZE_B)) {
    // SoC peripherals
    base_addr = SOC_PERIPHERALS_H_BASE_ADDR;
    off = off - CLUSTERS_SIZE_B;
    size_b = SOC_PERIPHERALS_SIZE_B;
    strcpy(type, "Peripherals");
  } else if (off < (CLUSTERS_SIZE_B + SOC_PERIPHERALS_SIZE_B + MBOX_SIZE_B)) {
    // Mailbox
    base_addr = MBOX_H_BASE_ADDR;
    off = off - CLUSTERS_SIZE_B - SOC_PERIPHERALS_SIZE_B;
    size_b = MBOX_SIZE_B;
    strcpy(type, "Mailbox");
  } else if (off < (CLUSTERS_SIZE_B + SOC_PERIPHERALS_SIZE_B + MBOX_SIZE_B + L2_MEM_SIZE_B)) {
    // L2
    base_addr = L2_MEM_H_BASE_ADDR;
    off = off - CLUSTERS_SIZE_B - SOC_PERIPHERALS_SIZE_B - MBOX_SIZE_B;
    size_b = L2_MEM_SIZE_B;
    strcpy(type, "L2");
  }
  // Platform
  else if (off < (CLUSTERS_SIZE_B + SOC_PERIPHERALS_SIZE_B + MBOX_SIZE_B + L2_MEM_SIZE_B + L3_MEM_SIZE_B)) {
    // Shared L3
    base_addr = L3_MEM_H_BASE_ADDR;
    off = off - CLUSTERS_SIZE_B - SOC_PERIPHERALS_SIZE_B - MBOX_SIZE_B - L2_MEM_SIZE_B;
    size_b = L3_MEM_SIZE_B;
    strcpy(type, "Shared L3");
  }
  // PULP external, PULPEmu
  else if (off < (CLUSTERS_SIZE_B + SOC_PERIPHERALS_SIZE_B + MBOX_SIZE_B + L2_MEM_SIZE_B + L3_MEM_SIZE_B + H_GPIO_SIZE_B)) {
    // H_GPIO
    base_addr = H_GPIO_BASE_ADDR;
    off = off - CLUSTERS_SIZE_B - SOC_PERIPHERALS_SIZE_B - MBOX_SIZE_B - L2_MEM_SIZE_B - L3_MEM_SIZE_B;
    size_b = H_GPIO_SIZE_B;
    strcpy(type, "Host GPIO");
  } else if (off < (CLUSTERS_SIZE_B + SOC_PERIPHERALS_SIZE_B + MBOX_SIZE_B + L2_MEM_SIZE_B + L3_MEM_SIZE_B + H_GPIO_SIZE_B +
                    CLKING_SIZE_B)) {
    // CLKING
#if !CLKING_BASE_ADDR
    // No clocking device
    return -ENODEV;
#else
    base_addr = CLKING_BASE_ADDR;
    off = off - CLUSTERS_SIZE_B - SOC_PERIPHERALS_SIZE_B - MBOX_SIZE_B - L2_MEM_SIZE_B - L3_MEM_SIZE_B - H_GPIO_SIZE_B;
    size_b = CLKING_SIZE_B;
    strcpy(type, "Clking");
#endif
  } else if (off < (CLUSTERS_SIZE_B + SOC_PERIPHERALS_SIZE_B + MBOX_SIZE_B + L2_MEM_SIZE_B + L3_MEM_SIZE_B + H_GPIO_SIZE_B +
                    CLKING_SIZE_B + RAB_CONFIG_SIZE_B)) {
    // RAB config
    base_addr = RAB_CONFIG_BASE_ADDR;
    off = off - CLUSTERS_SIZE_B - SOC_PERIPHERALS_SIZE_B - MBOX_SIZE_B - L2_MEM_SIZE_B - L3_MEM_SIZE_B - H_GPIO_SIZE_B -
          CLKING_SIZE_B;
    size_b = RAB_CONFIG_SIZE_B;
    strcpy(type, "RAB config");
  }
#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX
  // Zynq System
  else if (off < (CLUSTERS_SIZE_B + SOC_PERIPHERALS_SIZE_B + MBOX_SIZE_B + L2_MEM_SIZE_B + L3_MEM_SIZE_B + H_GPIO_SIZE_B +
                  CLKING_SIZE_B + RAB_CONFIG_SIZE_B + SLCR_SIZE_B)) {
    // Zynq SLCR
    base_addr = SLCR_BASE_ADDR;
    off = off - CLUSTERS_SIZE_B - SOC_PERIPHERALS_SIZE_B - MBOX_SIZE_B - L2_MEM_SIZE_B - L3_MEM_SIZE_B - H_GPIO_SIZE_B -
          CLKING_SIZE_B - RAB_CONFIG_SIZE_B;
    size_b = SLCR_SIZE_B;
    strcpy(type, "Zynq SLCR");
  }
#endif // PLATFORM
  else {
    printk(KERN_INFO "PULP: Invalid VMA offset for mmap.\n");
    return -EINVAL;
  }

  // set physical PFN and virtual size
  physical = (base_addr + off) >> PAGE_SHIFT;
  vsize = vma->vm_end - vma->vm_start;
  psize = size_b - off;

  // set protection flags to avoid caching and paging
  vma->vm_flags |= VM_IO | VM_DONTEXPAND | VM_DONTDUMP;
  vma->vm_page_prot = pgprot_noncached(vma->vm_page_prot);

  if (DEBUG_LEVEL_PULP > 0) {
    printk(KERN_INFO "PULP: %s memory mapped. \nPhysical address = %#lx, user-space virtual address = %#lx, vsize = %#lx.\n",
           type, physical << PAGE_SHIFT, vma->vm_start, vsize);
  }

  if (vsize > psize)
    return -EINVAL; /*  spans too high */

  // map physical kernel space addresses to virtual user space addresses
  io_remap = io_remap_pfn_range(vma, vma->vm_start, physical, vsize, vma->vm_page_prot);
  if (io_remap != 0) {
    printk(KERN_ERR "PULP: io_remap_pfn_range(.., %lx, %lx, %lu, ..) failed: %d!\n", vma->vm_start,
        physical, vsize, io_remap);
    return -EAGAIN;
  }

  return 0;
}

// // avoid the extension of the mapping using mremap
// //   to avoid remapping past the end of the physical device area
// struct page *simple_nopage(struct vm_area_struct *vma, unsigned long address, int *type);
// {
//   return NOPAGE_SIGBUS;
// }

// }}}

// isr {{{
/***********************************************************************************
 *
 * ██╗███████╗██████╗
 * ██║██╔════╝██╔══██╗
 * ██║███████╗██████╔╝
 * ██║╚════██║██╔══██╗
 * ██║███████║██║  ██║
 * ╚═╝╚══════╝╚═╝  ╚═╝
 *
 ***********************************************************************************/
irqreturn_t pulp_isr(int irq, void *ptr)
{
  unsigned long intr_reg_value = 0;
  struct timeval time;
  uint64_t cur_clk, cur_time;
  int i;
  unsigned rab_mh;

  pr_debug("PULP: Handling IRQ %0d.\n", irq);

  // read and clear the interrupt register
#if INTR_REG_BASE_ADDR
  intr_reg_value = ioread32((void *)(unsigned long)my_dev.intr_reg);
#else
  if (irq == my_dev.irq_mbox) {
    BIT_SET(intr_reg_value, BF_MASK_GEN(INTR_MBOX, 1));
  } else if (irq == my_dev.irq_rab_host_miss) {
    BIT_SET(intr_reg_value, BF_MASK_GEN(INTR_RAB_HOST_MISS, 1));
  } else if (irq == my_dev.irq_rab_host_multi) {
    BIT_SET(intr_reg_value, BF_MASK_GEN(INTR_RAB_HOST_MULTI, 1));
  } else if (irq == my_dev.irq_rab_host_prot) {
    BIT_SET(intr_reg_value, BF_MASK_GEN(INTR_RAB_HOST_PROT, 1));
  } else if (irq == my_dev.irq_rab_pulp_miss) {
    BIT_SET(intr_reg_value, BF_MASK_GEN(INTR_RAB_PULP_MISS, 1));
  } else if (irq == my_dev.irq_rab_pulp_multi) {
    BIT_SET(intr_reg_value, BF_MASK_GEN(INTR_RAB_PULP_MULTI, 1));
  } else if (irq == my_dev.irq_rab_pulp_prot) {
    BIT_SET(intr_reg_value, BF_MASK_GEN(INTR_RAB_PULP_PROT, 1));
  } else if (irq == my_dev.irq_rab_mhr_full) {
    BIT_SET(intr_reg_value, BF_MASK_GEN(INTR_RAB_MHR_FULL, 1));
  } else if (irq == my_dev.irq_eoc) {
    // find which cluster actually finished
    for (i = 0; i < N_CLUSTERS; ++i) {
      if (ioread32(my_dev.clusters + ARCHI_CLUSTER_SIZE * i + ARCHI_CLUSTER_PERIPHERALS_OFFSET +
                   ARCHI_CLUSTER_CTRL_OFFSET)) {
        BIT_SET(intr_reg_value, BF_MASK_GEN(INTR_EOC_0 + i, INTR_EOC_0 + i + 1));
      }
    }
  } else {
    printk(KERN_WARNING "PULP: Cannot handle interrupt %d, cannot be mapped to to identifier\n", irq);
    return IRQ_NONE;
  }
#endif

  /*********************
  *
  * top-half handler
  *
  *********************/
  do_gettimeofday(&time);

  if (BF_GET(intr_reg_value, INTR_MBOX, 1)) { // mailbox
    pulp_mbox_intr(my_dev.mbox);
  }
  if (BF_GET(intr_reg_value, INTR_RAB_HOST_MISS, 1)) { // RAB Host miss
    rab_mh = pulp_rab_mh_sched();

    if ((DEBUG_LEVEL_RAB_MH > 1) && (rab_mh == 1)) {
      if (printk_ratelimit()) {
        printk(KERN_INFO "PULP: RAB Host miss interrupt handled at %02li:%02li:%02li.\n", (time.tv_sec / 3600) % 24,
               (time.tv_sec / 60) % 60, time.tv_sec % 60);

        // for debugging
        pulp_rab_mapping_print(my_dev.rab_config, 0xAAAA);
      }
    }
  }
  if (BF_GET(intr_reg_value, INTR_RAB_HOST_MULTI, 1)) { // RAB Host multi
    if (printk_ratelimit()) {
      printk(KERN_ALERT "PULP: RAB Host multi interrupt received at %02li:%02li:%02li.\n", (time.tv_sec / 3600) % 24,
             (time.tv_sec / 60) % 60, time.tv_sec % 60);
    }
  }
  if (BF_GET(intr_reg_value, INTR_RAB_HOST_PROT, 1)) { // RAB Host prot
    if (printk_ratelimit()) {
      printk(KERN_ALERT "PULP: RAB Host prot interrupt received at %02li:%02li:%02li.\n", (time.tv_sec / 3600) % 24,
             (time.tv_sec / 60) % 60, time.tv_sec % 60);
    }
  }
  if (BF_GET(intr_reg_value, INTR_RAB_PULP_MISS, 1)) { // RAB PULP miss
    rab_mh = pulp_rab_mh_sched();

    if ((DEBUG_LEVEL_RAB_MH > 1) && (rab_mh == 1)) {
      if (printk_ratelimit()) {
        printk(KERN_INFO "PULP: RAB PULP miss interrupt handled at %02li:%02li:%02li.\n", (time.tv_sec / 3600) % 24,
               (time.tv_sec / 60) % 60, time.tv_sec % 60);

        // for debugging
        pulp_rab_mapping_print(my_dev.rab_config, 0xAAAA);
      }
    }
  }
  if (BF_GET(intr_reg_value, INTR_RAB_PULP_MULTI, 1)) { // RAB PULP multi
    if (printk_ratelimit()) {
      printk(KERN_ALERT "PULP: RAB PULP multi interrupt received at %02li:%02li:%02li.\n", (time.tv_sec / 3600) % 24,
             (time.tv_sec / 60) % 60, time.tv_sec % 60);
    }
  }
  if (BF_GET(intr_reg_value, INTR_RAB_PULP_PROT, 1)) { // RAB PULP prot
    if (printk_ratelimit()) {
      printk(KERN_ALERT "PULP: RAB PULP prot interrupt received at %02li:%02li:%02li.\n", (time.tv_sec / 3600) % 24,
             (time.tv_sec / 60) % 60, time.tv_sec % 60);
    }
  }
  if (BF_GET(intr_reg_value, INTR_RAB_MHR_FULL, 1)) { // RAB mhr full
    if (printk_ratelimit()) {
      printk(KERN_ALERT "PULP: RAB mhr full interrupt received at %02li:%02li:%02li.\n", (time.tv_sec / 3600) % 24,
             (time.tv_sec / 60) % 60, time.tv_sec % 60);
    }
  }
  if (BF_GET(intr_reg_value, INTR_EOC_0, INTR_EOC_N - INTR_EOC_0 + 1)) { // EOC
    cur_clk = host_get_clock_counter();
    cur_time = host_get_time();

    for (i = 0; i < N_CLUSTERS; i++) {
      if (BF_GET(intr_reg_value, INTR_EOC_0 + i, 1)) {
        profile_info.clusters[i].host_clk_finish = cur_clk;
        profile_info.clusters[i].host_time_finish = cur_time;

        profile_info.clusters[i].accel_clk_finish = accel_get_clk(my_dev.clusters, i);

        BIT_CLEAR(active_cluster_mask, BF_MASK_GEN(i, 1));
        if (!active_cluster_mask) {
          complete(&ctrl_finished);
        }

        printk(KERN_INFO "PULP: End of Computation Cluster %i at %02li:%02li:%02li.\n", i, (time.tv_sec / 3600) % 24,
               (time.tv_sec / 60) % 60, time.tv_sec % 60);
      }
    }
#if RAB_AX_LOG_EN == 1
    if (pulp_rab_ax_log_en)
      pulp_rab_ax_log_read(gpio_value, 1);
#endif
  }
#if RAB_AX_LOG_EN == 1
  if (BF_GET(intr_reg_value, INTR_RAB_AR_LOG_FULL, 1) || BF_GET(intr_reg_value, INTR_RAB_AW_LOG_FULL, 1) ||
      BF_GET(intr_reg_value, INTR_RAB_CFG_LOG_FULL, 1)) {
    printk(KERN_INFO "PULP: RAB AX log full interrupt received at %02li:%02li:%02li.\n", (time.tv_sec / 3600) % 24,
           (time.tv_sec / 60) % 60, time.tv_sec % 60);

    pulp_rab_ax_log_read(gpio_value, 1);
  }
#endif

  return IRQ_HANDLED;
}
// }}}

// ioctl {{{
/***********************************************************************************
 *
 * ██╗ ██████╗  ██████╗████████╗██╗
 * ██║██╔═══██╗██╔════╝╚══██╔══╝██║
 * ██║██║   ██║██║        ██║   ██║
 * ██║██║   ██║██║        ██║   ██║
 * ██║╚██████╔╝╚██████╗   ██║   ███████╗
 * ╚═╝ ╚═════╝  ╚═════╝   ╚═╝   ╚══════╝
 *
 ***********************************************************************************/
#ifdef CONFIG_COMPAT
long pulp_compat_ioctl(struct file *filp, unsigned int cmd, unsigned long arg)
{
  return pulp_ioctl(filp, cmd, (unsigned long)compat_ptr(arg));
}
#endif

long pulp_ioctl(struct file *filp, unsigned int cmd, unsigned long arg)
{
  int err = 0, i;
  long retval = 0;
  unsigned long flags;

  // to read and write from user space
  unsigned request[3];
  unsigned long n_bytes_left;

  MailboxMode mb_md;
  MissHandlingMode mh_md;
  RabSliceReq rab_slice_request;

  // needed for DMA
  unsigned size_b;
  unsigned addr_l3, addr_pulp;
  unsigned char dma_cmd;

  // needed for profiling
  uint64_t cur_clk;
  uint64_t cur_time;
  uint64_t accel_clk;

#ifdef PROFILE_DMA
  unsigned long ret;
  ktime_t time_dma_start, time_dma_end;
  unsigned time_dma_acc;
  time_dma_acc = 0;
#endif

  /*
   * extract the type and number bitfields, and don't decode wrong
   * cmds: return ENOTTY before access_ok()
   */
  if (_IOC_TYPE(cmd) != PULP_IOCTL_MAGIC)
    return -ENOTTY;
  if ((_IOC_NR(cmd) < PULP_IOC_NR_MIN) | (_IOC_NR(cmd) > PULP_IOC_NR_MAX))
    return -ENOTTY;

  /*
   * the direction is a bitmask, and VERIFY_WRITE catches R/W
   * transfers. 'Type' is user-oriented, while access_ok is
   * kernel-oriented, so the concept of "read" and "write" is reversed
   */
  if (_IOC_DIR(cmd) & _IOC_READ)
    err = !access_ok(VERIFY_WRITE, (void __user *)arg, _IOC_SIZE(cmd));
  else if (_IOC_DIR(cmd) & _IOC_WRITE)
    err = !access_ok(VERIFY_READ, (void __user *)arg, _IOC_SIZE(cmd));
  if (err)
    return -EFAULT;

  // the actual ioctls {{{
  switch (cmd) {
  case PULP_IOCTL_CTRL_START: // start execution

    // set the fetch enable mask
    if (arg & (~CLUSTER_MASK)) {
      return -EINVAL;
    }
    BIT_SET(gpio_value, arg << GPIO_CLUSTER_OFFSET);

    // initialalize start condition
    cur_clk = host_get_clock_counter();
    cur_time = host_get_time();

    if (DEBUG_LEVEL_CTRL > 0) {
      printk(KERN_INFO "PULP: Started execution for cluster mask 0x%lx at time %llu\n", arg, cur_time);
    }

    spin_lock_irqsave(&ctrl_lock, flags);

    for (i = 0; i < MAX_CLUSTERS; ++i) {
      if (arg & (1 << i)) {
        profile_info.clusters[i].host_clk_start = cur_clk;
        profile_info.clusters[i].host_clk_finish = 0;
        profile_info.clusters[i].host_time_start = cur_time;
        profile_info.clusters[i].host_time_finish = 0;

        spin_unlock_irqrestore(&ctrl_lock, flags);
        accel_reset_clk(my_dev.clusters, i);
        accel_clk = accel_get_clk(my_dev.clusters, i);
        spin_lock_irqsave(&ctrl_lock, flags);
        profile_info.clusters[i].accel_clk_start = accel_clk;
        profile_info.clusters[i].accel_clk_finish = 0;
      }
    }
    active_cluster_mask = arg;
    reinit_completion(&ctrl_finished);

    spin_unlock_irqrestore(&ctrl_lock, flags);

    // write the update GPIO value
    iowrite32(gpio_value, (void *)((unsigned long)my_dev.gpio + GPIO_HOST2PULP_OFFSET));

    break;

  case PULP_IOCTL_CTRL_STOP: // stop execution

    // set the disable mask
    if (arg & (~CLUSTER_MASK)) {
      return -EINVAL;
    }

    // clear the fetch enable mask
    BIT_CLEAR(gpio_value, arg << GPIO_CLUSTER_OFFSET);

    // write the update GPIO value
    iowrite32(gpio_value, (void *)((unsigned long)my_dev.gpio + GPIO_HOST2PULP_OFFSET));

    // set finish time for remaining clusters
    cur_clk = host_get_clock_counter();
    cur_time = host_get_time();

    if (DEBUG_LEVEL_CTRL > 0) {
      printk(KERN_INFO "PULP: Stopped execution for cluster mask 0x%lx at time %llu\n", arg, cur_time);
    }

    spin_lock_irqsave(&ctrl_lock, flags);

    for (i = 0; i < MAX_CLUSTERS; ++i) {
      if (arg & (1 << i) && !profile_info.clusters[i].host_clk_finish) {
        profile_info.clusters[i].host_clk_finish = cur_clk;
        profile_info.clusters[i].host_time_finish = cur_time;

        spin_unlock_irqrestore(&ctrl_lock, flags);
        accel_clk = accel_get_clk(my_dev.clusters, i);
        spin_lock_irqsave(&ctrl_lock, flags);
        profile_info.clusters[i].accel_clk_finish = accel_clk;
      }
    }
    active_cluster_mask = 0;

    spin_unlock_irqrestore(&ctrl_lock, flags);

    break;

  case PULP_IOCTL_CTRL_RESET: // reset execution

    // disable miss handling and mailbox
    err = vm_set_mh_mode(MH_NONE, NULL);
    if (err) {
      retval = err;
      break;
    }
    err = pulp_mbox_set_mode(MBOX_OFF);
    if (err) {
      retval = err;
      break;
    }

    // reset all slices including driver
    pulp_rab_release(true);

#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX
    retval = pulp_reset(my_dev.gpio, NULL, my_dev.slcr, &gpio_value, arg);
#elif defined(GPIO_EXT_RESET_ADDR)
    retval = pulp_reset(my_dev.gpio, my_dev.gpio_reset, NULL, &gpio_value, arg);
#else
    retval = pulp_reset(my_dev.gpio, NULL, NULL, &gpio_value, arg);
#endif

    if (retval) {
      break;
    }

    // reinitialize rab
    err = pulp_rab_init(&my_dev);
    if (err) {
      retval = err;
      break;
    }

    // reinitialize mailbox
    pulp_mbox_init(my_dev.mbox);

    break;

  case PULP_IOCTL_CTRL_SET_FREQ: // set frequency

#if CLKING_BASE_ADDR
    retval = pulp_clking_set_freq(my_dev.clking, arg);
#else
    retval = -ENOSYS;
#endif

    // reinitialize rab to ensure mappings are placed
    if (retval >= 0) {
      err = pulp_rab_init(&my_dev);
      if (err) {
        retval = err;
        break;
      }
    }

    break;

  case PULP_IOCTL_CTRL_WAIT:

    wait_for_completion_interruptible_timeout(&ctrl_finished, max(1ul, arg * HZ / 1000));

    break;

  case PULP_IOCTL_VM_SET_MH_MODE:

    n_bytes_left = copy_from_user((void *)request, (void __user *)arg, sizeof(unsigned));
    if (n_bytes_left) {
      retval = -EFAULT;
      break;
    }
    mh_md = request[0];

    vm_set_mh_mode(mh_md, ((void *)arg) + sizeof(unsigned));

    break;

  case PULP_IOCTL_VM_GET_MH_MODE:

    mh_md = vm_get_mh_mode();

    err = copy_to_user((void *)arg, &mh_md, sizeof(MailboxMode));

    if (err != 0)
      retval = -EFAULT;

    break;

  case PULP_IOCTL_RAB_REQ: // request new RAB slices

    // get slice data from user space - arg already checked above
    n_bytes_left = copy_from_user((void *)request, (void __user *)arg, 3 * sizeof(unsigned));
    if (n_bytes_left) {
      retval = -EFAULT;
      break;
    }

    // parse request
    RAB_GET_FLAGS_HW(rab_slice_request.flags_hw, request[0]);
    RAB_GET_PORT(rab_slice_request.rab_port, request[0]);
    RAB_GET_LVL(rab_slice_request.rab_lvl, request[0]);
    RAB_GET_DATE_EXP(rab_slice_request.date_exp, request[0]);
    RAB_GET_DATE_CUR(rab_slice_request.date_cur, request[0]);
    rab_slice_request.rab_mapping = 0;

    rab_slice_request.addr_start = request[1];
    size_b = request[2];

    rab_slice_request.addr_end = rab_slice_request.addr_start + size_b;

    retval = pulp_rab_req(my_dev.rab_config, &rab_slice_request);

    break;

  case PULP_IOCTL_RAB_FREE: // free RAB slices based on time code

    pulp_rab_free(my_dev.rab_config, BF_GET(arg, 0, RAB_CONFIG_N_BITS_DATE), false);

#if RAB_AX_LOG_EN == 1
    if (pulp_rab_ax_log_en) {
      pulp_rab_ax_log_read(gpio_value, 1);
      pulp_rab_ax_log_print();
    }
#endif

#if defined(PROFILE_RAB_STR) || defined(PROFILE_RAB_MH)
    pulp_rab_prof_print();
#endif

    break;

  case PULP_IOCTL_RAB_REQ_STRIPED: // request striped RAB slices

    retval = pulp_rab_req_striped(my_dev.rab_config, arg);

    break;

  case PULP_IOCTL_RAB_FREE_STRIPED: // free striped RAB slices

    pulp_rab_free_striped(my_dev.rab_config, arg);

#if RAB_AX_LOG_EN == 1
    if (pulp_rab_ax_log_en) {
      pulp_rab_ax_log_read(gpio_value, 1);
      pulp_rab_ax_log_print();
    }
#endif

#if defined(PROFILE_RAB_STR) || defined(PROFILE_RAB_MH)
    pulp_rab_prof_print();
#endif

    break;

  case PULP_IOCTL_MBOX_SET_MODE:

    mb_md = (MailboxMode)arg;

    pulp_mbox_set_mode(mb_md);

    break;

  case PULP_IOCTL_MBOX_GET_MODE:

    mb_md = pulp_mbox_get_mode();

    err = copy_to_user((void *)arg, &mh_md, sizeof(MailboxMode));

    if (err != 0)
      retval = -EFAULT;

    break;

  // DMA_XFER {{{
  case PULP_IOCTL_DMA_XFER_ASYNC: // setup a transfer using the host DMA engine

    // get transfer data from user space - arg already checked above
    n_bytes_left = copy_from_user((void *)request, (void __user *)arg, 3 * sizeof(unsigned));
    if (n_bytes_left) {
      retval = -EFAULT;
      break;
    }

    addr_l3 = request[0];
    addr_pulp = request[1];

    size_b = request[2] & 0x7FFFFFFF;
    dma_cmd = (request[2] >> 31);

    pulp_dma_xfer_async(pulp_dma_chan, pulp_dma_cleanup, addr_l3, addr_pulp, size_b, dma_cmd);

    break;

  case PULP_IOCTL_DMA_XFER_WAIT:
    printk(KERN_WARNING "PULP - DMA: IOCTL call not implemented.\n");
    break;
    // }}}

  case PULP_IOCTL_RAB_AX_LOG_ENA: // enable the AX logging

#if GPIO_RAB_AX_LOG_EN >= 0
    pulp_rab_ax_log_en = 1;
    BIT_SET(gpio_value, BF_MASK_GEN(GPIO_RAB_AX_LOG_EN, 1));
    iowrite32(gpio_value, (void *)((unsigned long)my_dev.gpio + GPIO_HOST2PULP_OFFSET));
#else
    retval = -ENOSYS;
#endif

    break;

  case PULP_IOCTL_RAB_AX_LOG_DIS: // disable the AX logging

#if GPIO_RAB_AX_LOG_EN >= 0
    pulp_rab_ax_log_en = 0;
    BIT_CLEAR(gpio_value, BF_MASK_GEN(GPIO_RAB_AX_LOG_EN, 1));
    iowrite32(gpio_value, (void *)((unsigned long)my_dev.gpio + GPIO_HOST2PULP_OFFSET));
#else
    retval = -ENOSYS;
#endif

    break;

  case PULP_IOCTL_RAB_AX_LOG_READ: // userspace wants to read the AX log buffers
#if RAB_AX_LOG_EN == 1
    pulp_rab_ax_log_to_user(arg);
#endif
    break;

  case PULP_IOCTL_INFO_PROFILE: // pass profiling information

    err = copy_to_user((void __user *)arg, &profile_info, sizeof(ProfileInfo));

    if (err != 0)
      retval = -EFAULT;

    break;

  default:
    return -ENOTTY;
  }
  // }}}

  return retval;
}
// }}}
