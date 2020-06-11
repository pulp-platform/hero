/*
 * Zynq Performance Monitoring Module
 *
 * This program uses both the performance monitoring units (PMUs)
 * inside the ARM Cortex-A9 cores and the performance counters inside
 * the L2 cache controller L2C-310 of the Xilinx Zynq-7000
 * All-Programmable SoC to monitor cache miss rates.
 *
 * Copyright (C) 2014 Pirmin Vogel <vogelpi@iis.ee.ethz.ch>
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 1, or (at
 * your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston MA
 * 02110-1301 USA.
 * 
 */

#include <linux/module.h>	/* Needed by all modules */
#include <linux/kernel.h>	/* KERN_ALERT, container_of */
#include <linux/kdev_t.h>	/* MAJOR, MINOR */
#include <asm/io.h>		/* ioremap, iounmap, iowrite32 */
#include <linux/cdev.h>		/* cdev struct */
#include <linux/fs.h>		/* file_operations struct */
#include <linux/kthread.h>      /* for the monitoring thread */
#include <asm/uaccess.h>	/* copy_to_user, copy_from_user,access_ok */
#include <linux/delay.h>        /* msleep */
#include <linux/device.h>       /* class_create, device_create */
#include <linux/proc_fs.h>      /* for /proc */

#include "v7_pmu.h"

#define ZYNQ_PMM_N_DEV_NUMBERS 1
#define N_ARM_CORES            2

#define ZYNQ_PMM_PROC_N_CHARS_MAX 1000

// Performance Monitor Unit
// ARM Architecture Reference Manual ARMv7, Appendix D3.1
#define ARM_PMU_PMXEVCNTR1_EV 0x3 // event: L1 data refill/miss
#define ARM_PMU_PMXEVCNTR0_EV 0x4 // event: L1 data access
//#define ARM_PMU_PMXEVCNTR1_EV 0x5 // event: data micro TLB refill/miss
// ARM Architecture Reference Manual ARMv7, Appendix D3.1 -- not implemented in Cortex-A9
//#define ARM_PMU_PMXEVCNTR1_EV 0x42 // event: L1 data read refill
//#define ARM_PMU_PMXEVCNTR0_EV 0x40 // event: L1 data read access
//#define ARM_PMU_PMXEVCNTR1_EV 0x43 // event: L1 data write refill
//#define ARM_PMU_PMXEVCNTR0_EV 0x41 // event: L1 data write access

// Level 2 Cache Controller L2C-310
#define L2C_310_BASE_ADDR 0xF8F02000
#define L2C_310_SIZE_B    0x1000

#define L2C_310_REG2_EV_COUNTER_CTRL_OFFSET_B 0x200 // event counter control register
#define L2C_310_REG2_EV_COUNTERS_DISABLE      0x0
#define L2C_310_REG2_EV_COUNTERS_ENABLE       0x1
#define L2C_310_REG2_EV_COUNTERS_RESET        0x7

#define L2C_310_REG2_EV_COUNTER1_CFG_OFFSET_B 0x204 // event counter 1 configuration register
#define L2C_310_REG2_EV_COUNTER0_CFG_OFFSET_B 0x208 // event counter 0 configuration register
// CoreLink L2C-310 Technical Reference Manual, Sections 2.5.8 & 3.3.7
#define L2C_310_REG2_EV_COUNTER1_EV_RH        0x2   // event: L2 data read hit
#define L2C_310_REG2_EV_COUNTER0_EV_RR        0x3   // event: L2 data read request
#define L2C_310_REG2_EV_COUNTER1_EV_WH        0x4   // event: L2 data write hit
#define L2C_310_REG2_EV_COUNTER0_EV_WR        0x5   // event: L2 data write request

#define L2C_310_REG2_EV_COUNTER1_OFFSET_B     0x20C // event counter 1 value register offset
#define L2C_310_REG2_EV_COUNTER0_OFFSET_B     0x210 // event counter 0 value register offset

//#define L2C_310_REG1_TAG_RAM_CONTROL_OFFSET_B  0x0108 // tag RAM latency control register
//#define L2C_310_REG1_DATA_RAM_CONTROL_OFFSET_B 0x010c // data RAM latency control register
//#define L2C_310_TAG_RAM_LAT                    0x1    // tag RAM latency
//#define L2C_310_DATA_RAM_WRITE_LAT             0x1    // data RAM write latency
//#define L2C_310_DATA_RAM_READ_LAT              0x2    // data RAM read latency

// Level 2 Cache Controller L2C-310
//#define L2C_310_TAG_RAM_LAT_VALUE  ((L2C_310_TAG_RAM_LAT << 8) | (L2C_310_TAG_RAM_LAT << 4) | L2C_310_TAG_RAM_LAT)
//#define L2C_310_DATA_RAM_LAT_VALUE ((L2C_310_DATA_RAM_WRITE_LAT << 8) | (L2C_310_DATA_RAM_READ_LAT << 4) | L2C_310_DATA_RAM_WRITE_LAT)

// methods declarations
int zynq_pmm_open(struct inode *inode, struct file *filp);
int zynq_pmm_release(struct inode *p_inode, struct file *filp);
int zynq_pmm_proc_read(struct file *filp, char *buf, size_t count, loff_t *offp);

static void zynq_pmm_proc_update(void *data);
static int zynq_pmm_thread(void* data);

// for ARM performance monitor unit
static void arm_pmu_setup(void *data);
static void arm_pmu_read(void *data);
static void arm_pmu_user_enable(void *data);
static void arm_pmu_user_disable(void *data);

// important structs
struct file_operations zynq_pmm_fops = {
  .owner = THIS_MODULE,
  .open = zynq_pmm_open,
  .read = zynq_pmm_proc_read,
  .release = zynq_pmm_release,
};

// type definitions
typedef struct {
  dev_t dev; // device number
  struct file_operations *fops;
  struct cdev cdev;
  int minor;
  int major;
  void *l2c_310;
} ZynqPMMDev;

// global variables
ZynqPMMDev my_dev;

// static variables
static struct class *my_class;
static struct task_struct *zynq_pmm_task; 

static unsigned current_length = ZYNQ_PMM_PROC_N_CHARS_MAX;
static unsigned transferred_length = ZYNQ_PMM_PROC_N_CHARS_MAX+1;
static char proc_text[ZYNQ_PMM_PROC_N_CHARS_MAX];
static int status = 0;

static unsigned arm_pmu_pmxevcntr0[N_ARM_CORES];
static unsigned arm_pmu_pmxevcntr1[N_ARM_CORES];
static unsigned arm_pmu_pmovsr[N_ARM_CORES];
static unsigned l1_miss_rate[N_ARM_CORES];
static unsigned l2c_310_reg2_ev_counter1;
static unsigned l2c_310_reg2_ev_counter0;
static unsigned l2_miss_rate;
static unsigned miss_rate[N_ARM_CORES];
static unsigned miss_rate_total;
static unsigned shift[N_ARM_CORES+1];
static unsigned shift_total;
static unsigned n_misses;
static unsigned n_accesses;
static unsigned delay = 500;
static unsigned debug = 0;
static unsigned l2_mode = 0; // 0: read, else: write

static int i;

/*
 * methods definitions
 */
// init
static int __init zynq_pmm_init(void) {
  
  int err;
  printk(KERN_ALERT "ZYNQ_PMM: Loading device driver.\n");

  my_dev.minor = 0;
  
  /*
   *  init module char device
   */
  // get dynamic device numbers
  err = alloc_chrdev_region(&my_dev.dev, my_dev.minor, ZYNQ_PMM_N_DEV_NUMBERS, "ZYNQ_PMM");
  if (err) {
    printk(KERN_WARNING "ZYNQ_PMM: Can't get major device number.\n");
    goto fail_alloc_chrdev_region;
  }
  // create class struct
  if ((my_class = class_create(THIS_MODULE, "chardrv")) == NULL) {
    printk(KERN_WARNING "ZYNQ_PMM: Error creating class.\n");
    err = -1;
    goto fail_create_class;
  }
  // create device and register it with sysfs
  if (device_create(my_class, NULL, my_dev.dev, NULL, "ZYNQ_PMM") == NULL) {
    printk(KERN_WARNING "ZYNQ_PMM: Error creating device.\n");
    err = -1;
    goto fail_create_device;
  }
  printk(KERN_INFO "ZYNQ_PMM: Device created.\n");

  my_dev.major = MAJOR(my_dev.dev);
  my_dev.fops = &zynq_pmm_fops;

  /*
   *  struct cdev
   */
  cdev_init(&my_dev.cdev, my_dev.fops);
  my_dev.cdev.owner = THIS_MODULE;

  /*
   *  ioremap 
   */
  my_dev.l2c_310 = ioremap_nocache(L2C_310_BASE_ADDR, L2C_310_SIZE_B);
  if (my_dev.l2c_310 == NULL) {
    printk(KERN_INFO "ZYNQ_PMM: ioremap_nochache not allowed for non-reserved RAM.\n");
  }
  printk(KERN_INFO "ZYNQ_PMM: L2 Cache Controller L2C-310 mapped to virtual kernel space @ %#lx.\n",
	 (long unsigned int) my_dev.l2c_310);
 
  /*
   *  tell the kernel about the device
   */
  err = cdev_add(&my_dev.cdev, my_dev.dev, ZYNQ_PMM_N_DEV_NUMBERS);
  if (err) {
    printk(KERN_WARNING "ZYNQ_PMM: Error registering the device.\n");
    goto fail_register_device;
  }
  printk(KERN_INFO "ZYNQ_PMM: Device registered.\n");

  /*
   *  create the /proc entry
   */
  if (proc_create("zynq_pmm",0,NULL,&zynq_pmm_fops) == NULL) {
    printk(KERN_WARNING "ZYNQ_PMM: /proc entry could not be created");
    goto fail_create_proc;
  }

  /*
   * setup the ARM performance monitoring unit
   */
  on_each_cpu(arm_pmu_setup, NULL, 1);

  /*
   * setup the L2 Cache Controller L2C-310
   */
  // configure the events to monitor
  if (l2_mode == 0) {
    iowrite32( L2C_310_REG2_EV_COUNTER1_EV_RH << 2 ,
	       my_dev.l2c_310 + L2C_310_REG2_EV_COUNTER1_CFG_OFFSET_B);
    iowrite32( L2C_310_REG2_EV_COUNTER0_EV_RR << 2 ,
	       my_dev.l2c_310 + L2C_310_REG2_EV_COUNTER0_CFG_OFFSET_B);
  }
  else {
    iowrite32( L2C_310_REG2_EV_COUNTER1_EV_WH << 2 ,
	       my_dev.l2c_310 + L2C_310_REG2_EV_COUNTER1_CFG_OFFSET_B);
    iowrite32( L2C_310_REG2_EV_COUNTER0_EV_WR << 2 ,
	       my_dev.l2c_310 + L2C_310_REG2_EV_COUNTER0_CFG_OFFSET_B);
  }
  // reset the counters
  iowrite32( L2C_310_REG2_EV_COUNTERS_RESET,
	     my_dev.l2c_310 + L2C_310_REG2_EV_COUNTER_CTRL_OFFSET_B);
  // enable the counters
  iowrite32( L2C_310_REG2_EV_COUNTERS_ENABLE,
	     my_dev.l2c_310 + L2C_310_REG2_EV_COUNTER_CTRL_OFFSET_B);

  /*
   * enable user mode access to counters in ARM Cortex-A9
   */
  on_each_cpu(arm_pmu_user_enable, NULL, 1);

  /*
   * start the monitoring thread
   */
  if (debug)
    zynq_pmm_task = kthread_run(zynq_pmm_thread,(void *)0,"zynq_pmm_thread");

  return 0;

  /*
   * error handling
   */
 fail_create_proc:
  cdev_del(&my_dev.cdev);
 fail_register_device:
  iounmap(my_dev.l2c_310);
  fail_create_device: 
  class_destroy(my_class);
 fail_create_class: 
  unregister_chrdev_region(my_dev.dev, 1);
 fail_alloc_chrdev_region:
  return err;
}
module_init(zynq_pmm_init);

// exit
static void __exit zynq_pmm_exit(void) {

  printk(KERN_ALERT "ZYNQ_PMM: Unloading device driver.\n");

  /*
   * stop the monitoring thread
   */
  if (debug)
    kthread_stop(zynq_pmm_task);

  /*
   * disable user mode access to counters in ARM Cortex-A9
   */
  on_each_cpu(arm_pmu_user_disable, NULL, 1);

  /*
   * disable the counters
   */
  disable_pmn(0);
  disable_pmn(1);
  iowrite32( L2C_310_REG2_EV_COUNTERS_DISABLE,
	     my_dev.l2c_310 + L2C_310_REG2_EV_COUNTER_CTRL_OFFSET_B);

  /*
   * remove the /proc entry
   */
  remove_proc_entry("zynq_pmm", NULL);

  // undo __init zynq_pmm_init
  iounmap(my_dev.l2c_310);
  cdev_del(&my_dev.cdev);
  device_destroy(my_class, my_dev.dev);
  class_destroy(my_class);
  unregister_chrdev_region(my_dev.dev, 1);
}
module_exit(zynq_pmm_exit);

// open
int zynq_pmm_open(struct inode *inode, struct file *filp) {
  // get a pointer to the ZynqPMMDev structure 
  ZynqPMMDev *dev;
  dev = container_of(inode->i_cdev, ZynqPMMDev, cdev);
  filp->private_data = dev;

  printk(KERN_INFO "ZYNQ_PMM: Device opened.\n");
  
  return 0;
}

// close
int zynq_pmm_release(struct inode *p_inode, struct file *filp) {

  printk(KERN_INFO "ZYNQ_PMM: Device released.\n");
  return 0;
}

// read proc entry
int zynq_pmm_proc_read(struct file *filp, char *buf, size_t count, loff_t *offp) {

  // an error occured
  if ( status ) {
    transferred_length = current_length + 1;
    status = 0;

    return -EFAULT;
  }
  
  // the last entry has been read completely
  // -> signal eof to caller
  if ( transferred_length == current_length ) {
    transferred_length++;

    return 0;
  }
  
  // update the entry if
  // - the last entry has been read completely, and
  // - eof has been signaled
  if ( transferred_length > current_length )
    zynq_pmm_proc_update(NULL);

  // return at most the remainder of the current entry
  if ( count > (current_length - transferred_length ))
    count = current_length - transferred_length;

  // copy the entry
  status = copy_to_user(buf,&proc_text[transferred_length],count);
  transferred_length = current_length - status;
  
  return (count - status);
}

// update proc entry
static void zynq_pmm_proc_update(void *data) {

  //printk("ZYNQ_PMM: Updating proc entry.\n");

  // setup
  transferred_length = 0;
  shift_total = 0;
  n_misses = 0;
  n_accesses = 0;

  /*
   * ARM PMUs
   */
  on_each_cpu(arm_pmu_read, NULL, 1);

  /*
   *  L2C-310
   */
  // disable the counters
  iowrite32( L2C_310_REG2_EV_COUNTERS_DISABLE,
	     my_dev.l2c_310 + L2C_310_REG2_EV_COUNTER_CTRL_OFFSET_B);

  // read the counters
  l2c_310_reg2_ev_counter1 = ioread32(my_dev.l2c_310
				      + L2C_310_REG2_EV_COUNTER1_OFFSET_B);
  l2c_310_reg2_ev_counter0 = ioread32(my_dev.l2c_310
				      + L2C_310_REG2_EV_COUNTER0_OFFSET_B);

  // reset the counters
  iowrite32( L2C_310_REG2_EV_COUNTERS_RESET,
	     my_dev.l2c_310 + L2C_310_REG2_EV_COUNTER_CTRL_OFFSET_B);
  
  // reenable the counters
  iowrite32( L2C_310_REG2_EV_COUNTERS_ENABLE,
	     my_dev.l2c_310 + L2C_310_REG2_EV_COUNTER_CTRL_OFFSET_B);

  /*
   *  generate the proc entry
   */
  // Info
  current_length = sprintf(proc_text,"Zynq Performance Monitoring Module \n");
   if (l2_mode == 0) 
    current_length += sprintf(proc_text+current_length,
			      "Monitoring cache miss rates - L2: Read accesses only! \n");
  else 
    current_length += sprintf(proc_text+current_length,
			      "Monitoring cache miss rates - L2: Write accesses only! \n");
  
  current_length += sprintf(proc_text+current_length,
			    "------------------------------------------------------------------\n");
  current_length += sprintf(proc_text+current_length,
			    "| Cache\t\t | # Misses\t | # Accesses\t | Miss Rate\t |\n");
  current_length += sprintf(proc_text+current_length,
			    "------------------------------------------------------------------\n");
  // L1
  for (i=0; i<N_ARM_CORES; i++) {
    // shift down to avoid corrupted results due to integer division
    if ( (arm_pmu_pmxevcntr1[i] >> 25) || (arm_pmu_pmxevcntr0[i] >> 25) )
      shift[i] = 7;
    else
      shift[i] = 0;
 
    if (arm_pmu_pmxevcntr0[i]) {
      //l1_miss_rate[i] = 100*arm_pmu_pmxevcntr1[i]/arm_pmu_pmxevcntr0[i];
      l1_miss_rate[i] = 100*(arm_pmu_pmxevcntr1[i] >> shift[i])/(arm_pmu_pmxevcntr0[i] >> shift[i]);
     }
    else
      l1_miss_rate[i] = 0;
    current_length += sprintf(proc_text+current_length,
			      "| L1 Core %i\t | %u \t | %u \t |  %u %% \t |\n",
			      i, arm_pmu_pmxevcntr1[i], arm_pmu_pmxevcntr0[i], l1_miss_rate[i]);
  }
  // L2
  // shift down to avoid corrupted results due to integer division
  if ( (l2c_310_reg2_ev_counter1 >> 25) || (l2c_310_reg2_ev_counter0 >> 25) )
    shift[N_ARM_CORES] = 7;
  else
    shift[N_ARM_CORES] = 0;
 
  if (l2c_310_reg2_ev_counter0) {
    //l2_miss_rate = 100*(l2c_310_reg2_ev_counter0 - l2c_310_reg2_ev_counter1)/l2c_310_reg2_ev_counter0;
    l2_miss_rate = 100*( (l2c_310_reg2_ev_counter0 >> shift[N_ARM_CORES]) 
			 - (l2c_310_reg2_ev_counter1 >> shift[N_ARM_CORES]) )
      /(l2c_310_reg2_ev_counter0 >> shift[N_ARM_CORES]);
  }
  else
    l2_miss_rate = 0;
  current_length += sprintf(proc_text+current_length,
			    "| L2 \t\t | %i\t | %u\t |  %u %% \t |\n",
			    l2c_310_reg2_ev_counter0-l2c_310_reg2_ev_counter1,
			    l2c_310_reg2_ev_counter0, l2_miss_rate);  
  current_length += sprintf(proc_text+current_length,
			    "------------------------------------------------------------------\n");
  
  // global miss rates
  for (i=0; i<N_ARM_CORES; i++) {
    //miss_rate[i] = l1_miss_rate[i]*l2_miss_rate/100;
    if (arm_pmu_pmxevcntr0[i])
      miss_rate[i] = ((l2_miss_rate ) * (arm_pmu_pmxevcntr1[i] >> shift[i]))
	/(arm_pmu_pmxevcntr0[i] >> shift[i]);
    else
      l1_miss_rate[i] = 0;
   
    current_length += sprintf(proc_text+current_length,
			      "Global miss rate Core %i: %u %%\n",i,miss_rate[i]);
  }
  
  // total global miss rate
  shift_total = 0;
  for (i=0; i<N_ARM_CORES; i++) {
    shift_total |= shift[i];
  }
  n_misses = 0;
  n_accesses = 0;
  for (i=0; i<N_ARM_CORES; i++) {
    n_misses += (arm_pmu_pmxevcntr1[i] >> shift_total); 
    n_accesses += (arm_pmu_pmxevcntr0[i] >> shift_total); 
  }
  if (n_accesses)
    miss_rate_total = (l2_miss_rate*n_misses)/n_accesses;
  else
    miss_rate_total = 0;
 
  current_length += sprintf(proc_text+current_length,"Total global miss rate: %u %%\n",miss_rate_total);

  // check overlow flags - L1 only!
  for (i=0; i<N_ARM_CORES; i++) {
    if (arm_pmu_pmovsr[i] && 0x3)
      current_length += sprintf(proc_text+current_length,"WARNING: Overflow in PMU of Core %i detected.\n",i);
  }
}

// thread to automatically monitor and print
static int zynq_pmm_thread(void* data) {
  printk(KERN_INFO "ZYNQ_PMM: Entering loop thread...\n");
  while(1)
    {
      if(kthread_should_stop()) break;
	       
      msleep(delay);

      // update the entry
      zynq_pmm_proc_update(NULL);

      // print the entry
      printk("%s",proc_text);
		
      msleep(10);
    }
  printk(KERN_INFO "ZYNQ_PMM: Exiting loop thread...\n");
  return 0;
}

// setup of ARM PMU
static void arm_pmu_setup(void *data) {
  // enable the PMU
  enable_pmu();
  // configure the events to montior
  pmn_config(0,ARM_PMU_PMXEVCNTR0_EV);
  pmn_config(1,ARM_PMU_PMXEVCNTR1_EV);
  // reset the counters
  reset_pmn();
  // reset the overflow flags
  write_flags( (1 << 31) | 0x3f );
  // enable the counters
  enable_pmn(0);
  enable_pmn(1);
}

/*
 * Function to read and reset the counters inside the PMU of the
 * current CPU. WARNING: preemption must be disabled before calling
 * this function. Call using on_each_cpu().
 */
static void arm_pmu_read(void *data) {
  // get the core ID
  int core_id = smp_processor_id();
  if ( (core_id > N_ARM_CORES - 1) || (core_id < 0) )
    printk(KERN_WARNING "ZYNQ_PMM: Invalid core ID %i",core_id);			  
  
  // disable the counters
  disable_pmn(0);
  disable_pmn(1);

  // read the counters
  arm_pmu_pmxevcntr0[core_id] = read_pmn(0);
  arm_pmu_pmxevcntr1[core_id] = read_pmn(1);

  // read the overflow flags
  arm_pmu_pmovsr[core_id] = read_flags();

  // reset the counters
  reset_pmn();
  write_flags( (1 << 31) | 0x3f ); // reset the overflow flags
  
  // reenable the counters
  enable_pmn(0);
  enable_pmn(1);
}

// enable user-space access to ARM PMUs, to use clock counters in user
// space programs
static void arm_pmu_user_enable(void *data) {
  // enable user-space access to counters
  asm volatile("mcr p15, 0, %0, c9, c14, 0" :: "r"(1));
  // enable clock counter divider (by 64), reset & enable clock counter, PMCR register 
  asm volatile("mcr p15, 0, %0, c9, c12, 0" :: "r"(0xD));
  // disable interrupts on clock counter overflow, PMINTENCLR register
  asm volatile("mcr p15, 0, %0, c9, c14, 2" :: "r"(0x80000000));
  // enable the clock counter, PMCNTENSET register
  asm volatile("mcr p15, 0, %0, c9, c12, 1" :: "r"(0x80000000));
}

// disable user-space access to ARM PMUs
static void arm_pmu_user_disable(void *data) {
  // disable user-space access to counters
  asm volatile("mcr p15, 0, %0, c9, c14, 0" :: "r"(0));
  // disable clock counter, PMCNTENCLR register
  asm volatile("mcr p15, 0, %0, c9, c12, 2" :: "r"(0x80000000));
  // disable all counters, PMCR register
  asm volatile("mcr p15, 0, %0, c9, c12, 1" :: "r"(0));
}

// module parameters 
module_param(delay,int,500);
module_param(debug,int,0);
module_param(l2_mode,int,0);

// info
MODULE_LICENSE("GPL");
MODULE_AUTHOR("Pirmin Vogel <vogelpi@iis.ee.ethz.ch>");
MODULE_DESCRIPTION("Zynq Performance Monitoring Module");
