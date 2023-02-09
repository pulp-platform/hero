//#define DEBUG
#include <asm/io.h>       /* ioremap, iounmap, iowrite32 */
#include <asm/uaccess.h>  /* for put_user */
#include <linux/cdev.h>   /* cdev struct */
#include <linux/delay.h>  // sleep
#include <linux/device.h> // class_create, device_create
#include <linux/kernel.h> /* Needed for KERN_INFO */
#include <linux/mm.h>     /* vm_area_struct struct, page struct, PAGE_SHIFT, page_to_phys */
#include <linux/module.h> /* Needed by all modules */
#include <linux/of.h>
#include <linux/of_address.h>
#include <linux/platform_device.h>
#include <linux/proc_fs.h> /* Necessary because we use the proc fs */
#include <linux/spinlock.h>

#include "snitch_module.h"
#include "snitch_reg.h"

// ----------------------------------------------------------------------------
//
//   Module properties
//
// ----------------------------------------------------------------------------

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Noah Huetter");
MODULE_DESCRIPTION("Snitch driver");

/* Match table for of_platform binding */
static const struct of_device_id snitch_of_match[] = {
    {
        .compatible = "eth,snitch-cluster",
    },
    {},
};
MODULE_DEVICE_TABLE(of, snitch_of_match);

#define dbg(...) printk(KERN_DEBUG "Snitch: " __VA_ARGS__)
#define info(...) printk(KERN_INFO "Snitch: " __VA_ARGS__)

#define DEVICE_NAME "snitch"
#define CLASS_NAME "snitch"

// VM_RESERVERD for mmap
#ifndef VM_RESERVED
#define VM_RESERVED (VM_DONTEXPAND | VM_DONTDUMP)
#endif

// AXI TLBs on quadrant narrow and wide ports translate 48-bit addresses, thus contain 3 uint64_t
// (first, last, base) and 1 uint32_t (flags) register
#define TLB_ENTRY_BYTES (3 * 8 + 1 * 4)

/**
 * Representation of a generic shared memory-region
 * @pbase: Physical address base
 * @vbase: Kernel virtual address base
 */
struct shared_mem {
  phys_addr_t pbase;
  void __iomem *vbase;
  resource_size_t size;
};

/**
 * struct sn_cluster - Internal representation of a snitch cluster
 * @dev: Pointer to device structure
 * @pbase: peripherals base
 * @soc_regs: kernel-mapped soc-control registers
 * @clint_regs: kernel-mapped clint registers
 * @l1: TCDM memory
 * @l3: Shared L3 memory
 * @sci: Snitch cluster info, shared with userspace on read
 * @list: Links it to the global sc_list
 * @minor: Minor device number in /dev
 * @fops: Copy of a pointer to the file operations
 * @nodename: nodename of the chardev
 * @mode: mode of the chardev
 * @this_device: the chardev
 * @quadrant_ctrl: handle to the associated quadrant controller
 */
struct sn_cluster {
  struct device *dev;
  void __iomem *pbase;
  struct shared_mem l1;
  struct shared_mem l3;
  struct sn_cluster_info sci;
  struct list_head list;
  int minor;
  const struct file_operations *fops;
  const char *nodename;
  umode_t mode;
  struct device *this_device;
  struct quadrant_ctrl *quadrant_ctrl;
};

struct sn_dev {
  struct class *class;
  struct cdev cdev;
  struct device *pDev;
  int major;
};

struct quadrant_ctrl {
  u32 quadrant_idx;
  void __iomem *regs;
  struct list_head list;
};

// ----------------------------------------------------------------------------
//
//   Static function declaration
//
// ----------------------------------------------------------------------------

static void set_isolation(struct sn_cluster *sc, int iso);
static int isolate(struct sn_cluster *sc);
static int deisolate(struct sn_cluster *sc);
static uint32_t get_isolation(uint32_t quadrant);
static void soc_reg_write(uint32_t reg_off, uint32_t val);
static uint32_t soc_reg_read(uint32_t reg_off);
static void quadrant_ctrl_reg_write(struct quadrant_ctrl *qc, uint32_t reg_off, uint32_t val);
static uint32_t quadrant_ctrl_reg_read(struct quadrant_ctrl *qc, uint32_t reg_off);
static void quadrant_ctrl_reg_write64(struct quadrant_ctrl *qc, uint32_t reg_off, uint64_t val);
static uint64_t quadrant_ctrl_reg_read64(struct quadrant_ctrl *qc, uint32_t reg_off);
static void set_clint(const struct snios_reg *sr);
static void clear_clint(const struct snios_reg *sr);
static uint32_t get_clint(uint32_t reg_off);
static struct quadrant_ctrl *get_quadrant_ctrl(u32 quadrant_idx);
static int write_tlb(struct sn_cluster *sc, struct axi_tlb_entry *tlbe);
static int read_tlb(struct sn_cluster *sc, struct axi_tlb_entry *tlbe);
static int test_read_regions(struct sn_cluster *sc, uint32_t reg_off);
// ----------------------------------------------------------------------------
//
//   Static data
//
// ----------------------------------------------------------------------------

static struct sn_dev sn_dev;

/**
 * @brief A list containing all pointers to registers snitch cluster `struct sn_cluster` structs
 */
static LIST_HEAD(sc_list);
/**
 * @brief A list containing all pointers to quadrant controllers `struct quadrant_ctrl` structs
 */
static LIST_HEAD(quadrant_ctrl_list);
/**
 * @brief Protect the sc_list
 *
 */
static DEFINE_MUTEX(sn_mtx);

// ----------------------------------------------------------------------------
//
//   "Shared" Data
//
// ----------------------------------------------------------------------------

/**
 * @clint_lock: Protects the clint and soc-reg resources
 * @soc_lock: Protects the clint and soc-reg resources
 */
spinlock_t clint_lock;
spinlock_t soc_lock;
/**
 * clint and soc-regs are ioremapped by the first module probe
 *
 * @soc_regs: kernel-mapped soc-control registers
 * @clint_regs: kernel-mapped clint registers
 */
void __iomem *soc_regs;
void __iomem *clint_regs;
void __iomem *clint_regs_p;

// ----------------------------------------------------------------------------
//
//   SYSFS
//
// ----------------------------------------------------------------------------

// ----------------------------------------------------------------------------
//
//   File OPs
//
// ----------------------------------------------------------------------------

/*
 * Called when a process tries to open the device file, like
 * "cat /dev/mycharfile"
 */
static int snitch_open(struct inode *inode, struct file *file) {
  int minor = iminor(inode);
  struct sn_cluster *sc;
  int err = -ENODEV;

  // mutex_lock(&sn_mtx);

  list_for_each_entry(sc, &sc_list, list) {
    if (sc->minor == minor) {
      /*
       * Place the miscdevice in the file's private_data so it can be used by the
       * file operations
       */
      file->private_data = sc;
      break;
    }
  }

  if (!file->private_data) {
    goto fail;
  }

  err = 0;
  info("cluster %d opened\n", sc->minor);

fail:
  // mutex_unlock(&sn_mtx);
  return err;
}

/*
 * Called when a process closes the device file.
 */
static int snitch_release(struct inode *inode, struct file *file) {
  struct sn_cluster *sc;
  sc = file->private_data;
  info("cluster %d released\n", sc->minor);
  return 0;
}

/*
 * Called when a process, which already opened the dev file, attempts to
 * read from it. If size is correct, returns a copy of the sn_cluster_info struct
 */
static ssize_t snitch_read(struct file *file, char __user *buffer, size_t length, loff_t *offset) {
  struct sn_cluster *sc;
  sc = file->private_data;

  // only support reads of size sizeof(struct sn_cluster_info)
  if (length != sizeof(struct sn_cluster_info)) {
    info(KERN_ALERT "Sorry, this operation isn't supported.\n");
    return -EINVAL;
  }

  if (copy_to_user(buffer, &sc->sci, sizeof(struct sn_cluster_info)) != 0)
    return -EFAULT;

  return sizeof(struct sn_cluster_info);
}

/*
 * Called when a process writes to dev file: echo "hi" > /dev/hello
 */
static ssize_t snitch_write(struct file *file, const char *buff, size_t len, loff_t *off) {
  info(KERN_ALERT "Sorry, this operation isn't supported.\n");
  return -EINVAL;
}

static long snitch_ioctl(struct file *file, unsigned int cmd, unsigned long arg) {
  void __user *argp = (void __user *)arg;
  int __user *p = argp;
  struct snios_reg sreg;
  struct axi_tlb_entry tlbe;
  struct sn_cluster *sc;
  sc = file->private_data;

  // check correct magic
  if (_IOC_TYPE(cmd) != SNIOC_MAGIC)
    return -ENOTTY;

  info("Received ioctl with cmd %d arg %ld\n", cmd, arg);

  // Switch according to the ioctl called
  switch (cmd) {
  case SNIOC_SET_OPTIONS: {
    info("(CMD SNIOC_SET_OPTIONS)\n");
    int options, retval = -EINVAL;
    if (get_user(options, p))
      return -EFAULT;

    if (options & SNIOS_ISOLATE)
      retval = isolate(sc);
    if (options & SNIOS_DEISOLATE) {
      retval = deisolate(sc);
    }

    return retval;
  }
  case SNIOS_SCRATCH_W: {
    info("(CMD SNIOS_SCRATCH_W)\n");
    if (copy_from_user(&sreg, p, sizeof(sreg)))
      return -EFAULT;
    // Sanitize to 4 scratch registers
    if (sreg.off > 4)
      return -EINVAL;
    info("scratch write reg %d val %#x\n", sreg.off, sreg.val);
    soc_reg_write(SCTL_SCRATCH_0_REG_OFFSET / 4 + sreg.off, sreg.val);
    return 0;
  }
  case SNIOS_SCRATCH_R: {
    info("(CMD SNIOS_SCRATCH_R)\n");
    if (copy_from_user(&sreg, p, sizeof(sreg)))
      return -EFAULT;
    // Sanitize to 4 scratch registers
    if (sreg.off > 4)
      return -EINVAL;
    sreg.val = soc_reg_read(SCTL_SCRATCH_0_REG_OFFSET / 4 + sreg.off);
    info("scratch read reg %d val %#x\n", sreg.off, sreg.val);
    if (copy_to_user(p, &sreg, sizeof(sreg)))
      return -EFAULT;
    return 0;
  }
  case SNIOS_READ_ISOLATION: {
    info("(CMD SNIOS_READ_ISOLATION)\n");
    uint32_t quadrant;
    if (get_user(quadrant, p))
      return -EFAULT;
    return get_isolation(quadrant);
  }
  case SNIOS_SET_IPI: {
    info("(CMD SNIOS_SET_IPI)\n");
    if (copy_from_user(&sreg, p, sizeof(sreg)))
      return -EFAULT;
    set_clint(&sreg);
    return 0;
  }
  case SNIOS_GET_IPI: {
    info("(CMD SNIOS_GET_IPI)\n");
    if (copy_from_user(&sreg, p, sizeof(sreg)))
      return -EFAULT;
    sreg.val = get_clint(sreg.off);
    if (copy_to_user(p, &sreg, sizeof(sreg)))
      return -EFAULT;
    return 0;
  }
  case SNIOS_CLEAR_IPI: {
    info("(CMD SNIOS_CLEAR_IPI)\n");
    if (copy_from_user(&sreg, p, sizeof(sreg)))
      return -EFAULT;
    clear_clint(&sreg);
    return 0;
  }
  case SNIOS_FLUSH: {
    info("(CMD SNIOS_FLUSH)\n");
    asm volatile("fence");
    return 0;
  }
  case SNIOS_WRITE_TLB_ENTRY: {
    info("(CMD SNIOS_WRITE_TLB_ENTRY)\n");
    if (copy_from_user(&tlbe, p, sizeof(tlbe)))
      return -EFAULT;
    return write_tlb(sc, &tlbe);
  }
  case SNIOS_READ_TLB_ENTRY: {
    int ret;
    info("(CMD SNIOS_READ_TLB_ENTRY)\n");
    if (copy_from_user(&tlbe, p, sizeof(tlbe)))
      return -EFAULT;
    ret = read_tlb(sc, &tlbe);
    if (copy_to_user(p, &tlbe, sizeof(tlbe)))
      return -EFAULT;
    return ret;
  }
  case SNIOS_TEST_READ_REGIONS: {
    info("(CMD SNIOS_TEST_READ_REGIONS)\n");
    if (copy_from_user(&sreg, p, sizeof(sreg)))
      return -EFAULT;
    return test_read_regions(sc, sreg.off);
  }
  default:
    return -ENOTTY;
  }

  return 0;
}

/**
 * @brief memory map to user-space. The module's address map is contiguous
 * refer to the SNITCH_MMAP_x_BASE() macros for address calculation
 *
 */
int snitch_mmap(struct file *file, struct vm_area_struct *vma) {
  unsigned long mapoffset, vsize, psize;
  char type[20];
  int ret;
  struct sn_cluster *sc;
  sc = file->private_data;

  switch (vma->vm_pgoff) {
  case 0:
    strncpy(type, "l3", sizeof(type));
    mapoffset = sc->l3.pbase;
    psize = sc->l3.size;
    break;
  case 1:
    strncpy(type, "l1", sizeof(type));
    mapoffset = sc->l1.pbase;
    psize = sc->l1.size;
    break;
  default:
    return -EINVAL;
  }

  info("Map region %s from kernel to user space with offset %#lx\n", type, vma->vm_pgoff);

  vsize = vma->vm_end - vma->vm_start;
  if (vsize > psize) {
    info("error: vsize %ld > psize %ld\n", vsize, psize);
    info("  vma->vm_end %lx vma->vm_start %lx\n", vma->vm_end, vma->vm_start);
    return -EINVAL;
  }

  // set protection flags to avoid caching and paging
  vma->vm_flags |= VM_IO | VM_RESERVED;
  vma->vm_page_prot = pgprot_noncached(vma->vm_page_prot);

  info("%s mmap: phys: %#lx, virt: %#lx vsize: %#lx psize: %#lx\n", type, mapoffset, vma->vm_start,
      vsize, psize);

  ret = remap_pfn_range(vma, vma->vm_start, mapoffset >> PAGE_SHIFT, vsize, vma->vm_page_prot);

  if (ret)
    info("mmap error: %d\n", ret);

  return ret;
}

int snitch_flush(struct file *file, fl_owner_t id) {
  // unsigned long mapoffset, vsize, psize;
  // char type[20];
  // int ret;
  // struct sn_cluster *sc;
  // sc = file->private_data;

  info("Device file flushed\n");
  return 0;
}

struct file_operations snitch_fops = {
    .owner = THIS_MODULE,
    .open = snitch_open,
    .read = snitch_read,
    .write = snitch_write,
    .release = snitch_release,
    .unlocked_ioctl = snitch_ioctl,
    .mmap = snitch_mmap,
    .flush = snitch_flush,
};

// ----------------------------------------------------------------------------
//
//   Statics
//
// ----------------------------------------------------------------------------
/**
 * @brief Set the isolation of the cluster in the soc-control register
 *
 * @param iso 1 to isolate, 0 to de-isolate
 */
static void set_isolation(struct sn_cluster *sc, int iso) {
  u32 mask, val;
  val = iso ? 1U : 0U;
  mask = (val << QCTL_ISOLATE_NARROW_IN_BIT) | (val << QCTL_ISOLATE_NARROW_OUT_BIT) |
         (val << QCTL_ISOLATE_WIDE_IN_BIT) | (val << QCTL_ISOLATE_WIDE_OUT_BIT);
  info("set_isolation quadrant %d value %01x\n", sc->quadrant_ctrl->quadrant_idx, mask);
  quadrant_ctrl_reg_write(sc->quadrant_ctrl, QCTL_ISOLATE_REG_OFFSET / 4, mask);
}

/**
 * @brief Set the reset of the quadrant
 *
 * @param reset 1 to assert reset, 0 de-assert reset
 */
static void set_reset(struct sn_cluster *sc, int reset) {
  info("set_reset quadrant %d %s\n", sc->quadrant_ctrl->quadrant_idx,
      reset ? "ASSERT" : "DE-ASSERT");
  // Active-low reset
  quadrant_ctrl_reg_write(sc->quadrant_ctrl, QCTL_RESET_N_REG_OFFSET / 4,
                          (reset ? 0U : 1U) << QCTL_RESET_N_RESET_N_BIT);
}

/**
 * @brief Isolate a quadrant by first setting the isolation and after succesful isolation
 * (isolated = 0xf), put quadrant in reset. If isolation does not succeed, does not reset the
 * quadrant and returns ETIMEOUT
 */
static int isolate(struct sn_cluster *sc) {
  unsigned quadrant_id = sc->sci.quadrant_idx;
  u32 timeout = 1000; // [x10 us]
  uint32_t iso;

  set_isolation(sc, 1);
  do {
    iso = get_isolation(quadrant_id);
    if (iso != 0xf)
      udelay(10);
  } while (iso != 0xf && --timeout);

  if (iso == 0xf) {
    set_reset(sc, 1);
  } else {
    return -ETIMEDOUT;
  }
  return 0;
}

/**
 * @brief Release reset and deisolate quadrant. On success (isolated = 0) return 0, on fail (isolate
 * != 0) put quadrant into reset and isolate, return -ETIMEDOUT
 */
static int deisolate(struct sn_cluster *sc) {
  unsigned quadrant_id = sc->sci.quadrant_idx;
  u32 timeout = 1000; // [x10 us]
  uint32_t iso;

  set_reset(sc, 0);
  set_isolation(sc, 0);
  do {
    iso = get_isolation(quadrant_id);
    if (iso != 0x0)
      udelay(10);
  } while (iso != 0x0 && --timeout);

  if (iso != 0x0) {
    set_isolation(sc, 1);
    set_reset(sc, 1);
    return -ETIMEDOUT;
  }

  return 0;
}

/**
 * @brief Read isolation bits of quadrant `quadrant`
 *
 * @param quadrant quadrant index to read isolation bits from
 */
static uint32_t get_isolation(uint32_t quadrant) {
  struct quadrant_ctrl *qc = get_quadrant_ctrl(quadrant);
  return quadrant_ctrl_reg_read(qc, QCTL_ISOLATED_REG_OFFSET / 4) & 0xf;
}

static void soc_reg_write(uint32_t reg_off, uint32_t val) {
  u32 rb;
  spin_lock(&soc_lock);
  iowrite32(val, (uint32_t *)soc_regs + reg_off);
  rb = ioread32((uint32_t *)soc_regs + reg_off);
  spin_unlock(&soc_lock);
  info("soc_reg_write reg %d value %08x rb: %08x (va=%px)\n", reg_off, val, rb, (uint32_t *)soc_regs + reg_off);
}
static uint32_t soc_reg_read(uint32_t reg_off) {
  u32 val;
  spin_lock(&soc_lock);
  val = ioread32((uint32_t *)soc_regs + reg_off);
  spin_unlock(&soc_lock);
  return val;
}
static void quadrant_ctrl_reg_write(struct quadrant_ctrl *qc, uint32_t reg_off, uint32_t val) {
  iowrite32(val, (uint32_t *)qc->regs + reg_off);
}
static uint32_t quadrant_ctrl_reg_read(struct quadrant_ctrl *qc, uint32_t reg_off) {
  return ioread32((uint32_t *)qc->regs + reg_off);
}
static void quadrant_ctrl_reg_write64(struct quadrant_ctrl *qc, uint32_t reg_off, uint64_t val) {
  iowrite64(val, (uint32_t *)qc->regs + reg_off);
}
static uint64_t quadrant_ctrl_reg_read64(struct quadrant_ctrl *qc, uint32_t reg_off) {
  return ioread64((uint32_t *)qc->regs + reg_off);
}
static void set_clint(const struct snios_reg *sr) {
  u32 val;
  spin_lock(&clint_lock);
  val = ioread32((uint32_t *)clint_regs + sr->off);
  iowrite32(val | sr->val, (uint32_t *)clint_regs + sr->off);
  spin_unlock(&clint_lock);
  info("clint write reg %d value %08x\n", sr->off, val | sr->val);
}
static void clear_clint(const struct snios_reg *sr) {
  u32 val;
  info("write at %px\n", (uint32_t *)clint_regs + sr->off);
  iowrite32((uint32_t) 0, (uint32_t *)clint_regs + sr->off);
  info("clint ready to clear at %px\n", (uint32_t *)clint_regs + sr->off);
  spin_lock(&clint_lock);
  info("read at %px\n", (uint32_t *)clint_regs + sr->off);
  val = ioread32((uint32_t *)clint_regs + sr->off);
  info("write at %px\n", (uint32_t *)clint_regs + sr->off);
  iowrite32(val & (~sr->val), (uint32_t *)clint_regs + sr->off);
  spin_unlock(&clint_lock);
  info("clint write reg %d value %08x\n", sr->off, val & (~sr->val));
}
static uint32_t get_clint(uint32_t reg_off) {
  u32 val;
  spin_lock(&clint_lock);
  val = ioread32((uint32_t *)clint_regs + reg_off);
  spin_unlock(&clint_lock);
  info("clint read reg %d val %08x\n", reg_off, val);
  return val;
}
static struct quadrant_ctrl *get_quadrant_ctrl(u32 quadrant_idx) {
  struct quadrant_ctrl *qc, *ret;
  ret = NULL;
  list_for_each_entry(qc, &quadrant_ctrl_list, list) if (qc->quadrant_idx == quadrant_idx) {
    ret = qc;
    break;
  }
  return ret;
}

static int write_tlb(struct sn_cluster *sc, struct axi_tlb_entry *tlbe) {
  uint32_t reg_off;
  uint64_t page_num_first = tlbe->first >> 12;
  uint64_t page_num_last  = tlbe->last  >> 12;
  uint64_t page_num_base  = tlbe->base  >> 12;

  // TODO: Sanitize index in range correctly
  if (tlbe->idx > 64)
    return -EINVAL;

  uint32_t i;
  // Add 4 to TLB_ENTRY_BYTES since there is one reserved word between each TLB_ENTRY
  if (tlbe->loc == AXI_TLB_NARROW) {
    reg_off = (QCTL_TLB_NARROW_REG_OFFSET + tlbe->idx * (TLB_ENTRY_BYTES+4)) / 4;
  } else if (tlbe->loc == AXI_TLB_WIDE) {
    reg_off = (QCTL_TLB_WIDE_REG_OFFSET   + tlbe->idx * (TLB_ENTRY_BYTES+4)) / 4;
  } else
    return -EINVAL;

  info("Writing at %px -> %px\n", (uint32_t *) sc->quadrant_ctrl->regs + reg_off + 0, (uint32_t *) sc->quadrant_ctrl->regs + reg_off + 6);
  iowrite32((uint32_t) page_num_first        , (uint32_t *) sc->quadrant_ctrl->regs + reg_off + 0 );
  iowrite32((uint32_t) (page_num_first >> 32), (uint32_t *) sc->quadrant_ctrl->regs + reg_off + 1 );
  iowrite32((uint32_t) page_num_last         , (uint32_t *) sc->quadrant_ctrl->regs + reg_off + 2 );
  iowrite32((uint32_t) (page_num_last >> 32) , (uint32_t *) sc->quadrant_ctrl->regs + reg_off + 3 );
  iowrite32((uint32_t) page_num_base         , (uint32_t *) sc->quadrant_ctrl->regs + reg_off + 4 );
  iowrite32((uint32_t) (page_num_base >> 32) , (uint32_t *) sc->quadrant_ctrl->regs + reg_off + 5 );
  iowrite32((uint32_t) tlbe->flags           , (uint32_t *) sc->quadrant_ctrl->regs + reg_off + 6 );
  return 0;
}

static int read_tlb(struct sn_cluster *sc, struct axi_tlb_entry *tlbe) {
  uint32_t reg_off;
  uint32_t page_num_first_low, page_num_first_high;
  uint32_t page_num_last_low , page_num_last_high ;
  uint32_t page_num_base_low , page_num_base_high ;

  // TODO: Sanitize index in range correctly
  if (tlbe->idx > 64)
    return -EINVAL;

  uint32_t i;
  // Add 4 to TLB_ENTRY_BYTES since there is one reserved word between each TLB_ENTRY
  if (tlbe->loc == AXI_TLB_NARROW) {
    reg_off = (QCTL_TLB_NARROW_REG_OFFSET + tlbe->idx * (TLB_ENTRY_BYTES+4)) / 4;
  } else if (tlbe->loc == AXI_TLB_WIDE) {
    reg_off = (QCTL_TLB_WIDE_REG_OFFSET   + tlbe->idx * (TLB_ENTRY_BYTES+4)) / 4;
  } else
    return -EINVAL;
  

  info("Reading at %px -> %px (off %x, %x)\n", (uint32_t *) sc->quadrant_ctrl->regs + reg_off + 0 , (uint32_t *) sc->quadrant_ctrl->regs + reg_off + 6, QCTL_TLB_NARROW_REG_OFFSET, reg_off);
  page_num_first_low  = ioread32((uint32_t *) sc->quadrant_ctrl->regs + reg_off + 0 );
  page_num_first_high = ioread32((uint32_t *) sc->quadrant_ctrl->regs + reg_off + 1 );
  page_num_last_low   = ioread32((uint32_t *) sc->quadrant_ctrl->regs + reg_off + 2 );
  page_num_last_high  = ioread32((uint32_t *) sc->quadrant_ctrl->regs + reg_off + 3 );
  page_num_base_low   = ioread32((uint32_t *) sc->quadrant_ctrl->regs + reg_off + 4 );
  page_num_base_high  = ioread32((uint32_t *) sc->quadrant_ctrl->regs + reg_off + 5 );
  tlbe->flags =         ioread32((uint32_t *) sc->quadrant_ctrl->regs + reg_off + 6 );

  tlbe->first =  ((uint64_t) page_num_first_low << 12) + ((uint64_t) page_num_first_high << 32);
  tlbe->last  =  ((uint64_t) page_num_last_low  << 12) + ((uint64_t) page_num_last_high  << 32);
  tlbe->base  =  ((uint64_t) page_num_base_low  << 12) + ((uint64_t) page_num_base_high  << 32);

  return 0;
}

static int test_read_regions(struct sn_cluster *sc, uint32_t reg_off) {
  u32 val;

  info("SOC_CTL : Attempting to read at %px + %x\n", (uint32_t *)soc_regs, reg_off);
  spin_lock(&soc_lock);
  val = ioread32((uint32_t *)soc_regs + reg_off);
  spin_unlock(&soc_lock);

  info("TCDM : Attempting to read at %px + %x\n", (void *)sc->l1.vbase, reg_off);
  val = ioread32((uint32_t *)sc->l1.vbase + reg_off);

  info("PERIPHERALS : Attempting to read at %px + %x\n", (void *)sc->pbase, reg_off);
  val = ioread32((uint32_t *)sc->pbase + reg_off);

  info("CLUSTER L3 : Attempting to read at %px + %x\n", (void *)sc->l3.vbase, reg_off);
  val = ioread32((void *)sc->l3.vbase + reg_off);

  //info("QUAD CTL : Attempting to read at %px + %x\n", qc->regs, reg_off);
  //val = ioread32((uint32_t *)qc->regs + reg_off);

  info("CLINT : Attempting to read at %px + %x\n", (uint32_t *) clint_regs, reg_off);
  val = ioread32((uint32_t *)clint_regs + reg_off);


  return 0;
}

// ----------------------------------------------------------------------------
//
//   Platform Driver
//
// ----------------------------------------------------------------------------

/**
 * @brief read property `propname` from node `np` and return value if exists, else `default
 *
 * @param np device nope pointer
 * @param propname property name
 * @param default value if not found
 * @return u32 property value or default
 */
static u32 of_get_prop_u32_default(const struct device_node *np, const char *propname, u32 dflt) {
  int ret;
  u32 value;
  ret = of_property_read_u32(np, propname, &value);
  return !ret ? value : dflt;
}

/**
 * snitch_probe - Snitch cluster probe function.
 * @pdev:	Pointer to platform device structure.
 *
 * Return: 0, on success
 *	    Non-zero error value on failure.
 *
 */
static int snitch_probe(struct platform_device *pdev) {
  struct resource *res, memres;
  struct sn_cluster *sc;
  struct quadrant_ctrl *qc;
  struct device_node *np;
  struct resource socres;
  struct resource clintres;
  struct resource quadctrlres;
  int ret;
  int err = 0;

  info("<-------SNITCH PROBE STARTS------->\n");
  dev_info(&pdev->dev, "probe\n");

  // Allocate memory for the snitch cluster structure
  sc = devm_kmalloc(&pdev->dev, sizeof(*sc), GFP_KERNEL);
  sc->nodename = NULL;
  if (!sc)
    return -ENOMEM;

  // Populate cluster info struct
  sc->sci.compute_num = of_get_prop_u32_default(pdev->dev.of_node, "eth,compute-cores", 8);
  sc->sci.dm_num = of_get_prop_u32_default(pdev->dev.of_node, "eth,dm-cores", 1);
  sc->sci.cluster_idx = of_get_prop_u32_default(pdev->dev.of_node, "eth,cluster-idx", 0);
  sc->sci.quadrant_idx = of_get_prop_u32_default(pdev->dev.of_node, "eth,quadrant-idx", 0);

  dev_info(&pdev->dev, "computer-cores: %d dm-cores: %d cluster: %d quadrant: %d\n",
           sc->sci.compute_num, sc->sci.dm_num, sc->sci.cluster_idx, sc->sci.quadrant_idx);

  INIT_LIST_HEAD(&sc->list);
  // mutex_lock(&sn_mtx);

  // Get resource and remap to kernel space
  // the snitch node should have two reg properties, one for TCDM the other for peripherals

  // TCDM is mapped as memory
  res = platform_get_resource(pdev, IORESOURCE_MEM, 0);
  sc->l1.pbase = res->start;
  sc->l1.size = resource_size(res);
  sc->l1.vbase = memremap(res->start, resource_size(res), MEMREMAP_WT);
  if (!sc->l1.vbase) {
    dev_err(&pdev->dev, "memremap of TCDM failed\n");
    err = -ENOMEM;
    goto out;
  }
  dev_info(&pdev->dev, "Remapped cluster's TCDM\n");
  info("TCDM : phys=%px virt=%px size=%px\n", (void *)sc->l1.pbase, (void *)sc->l1.vbase, (unsigned int)sc->l1.size);

  // Cluster peripheral is mapped as resource
  res = platform_get_resource(pdev, IORESOURCE_MEM, 1);
  sc->pbase = devm_ioremap_resource(&pdev->dev, res);
  if (IS_ERR(sc->pbase)) {
    err = PTR_ERR(sc->pbase);
    goto out;
  }
  sc->sci.periph_size = resource_size(res);
  dev_info(&pdev->dev, "Remapped cluster's PERIPHERALS\n");
  info("PERIPHERALS : phys=%px virt=%px size=%px\n", (void *)res->start, (void *)sc->pbase, resource_size(res));

  // SoC control
  if (!soc_regs) {
    spin_lock_init(&soc_lock);
    np = of_parse_phandle(pdev->dev.of_node, "eth,soc-ctl", 0);
    if (!np) {
      dev_err(&pdev->dev, "No %s specified\n", "eth,soc-ctl");
      err = -EINVAL;
      goto out;
    }
    ret = of_address_to_resource(np, 0, &socres);
    soc_regs = devm_ioremap_resource(&pdev->dev, &socres);
    if (IS_ERR(soc_regs)) {
      dev_err(&pdev->dev, "could not map soc-ctl regs\n");
      err = PTR_ERR(soc_regs);
      goto out;
    }
  }
  dev_info(&pdev->dev, "Remapped SOC_CTL\n");
  info("SOC_CTL : phys=%px virt=%px size=%px\n", (void *)socres.start, soc_regs, (resource_size(&socres)));

  // CLINT
  if (!clint_regs) {
    spin_lock_init(&clint_lock);
    np = of_parse_phandle(pdev->dev.of_node, "eth,clint", 0);
    if (!np) {
      dev_err(&pdev->dev, "No %s specified\n", "eth,clint");
      err = -EINVAL;
      goto out;
    }
    ret = of_address_to_resource(np, 0, &clintres);
    clint_regs_p = (void __iomem *)clintres.start;
    clint_regs = devm_ioremap_resource(&pdev->dev, &clintres);
    if (IS_ERR(clint_regs)) {
      dev_err(&pdev->dev, "could not map clint regs\n");
      err = PTR_ERR(clint_regs);
      goto out;
    }
  }
  dev_info(&pdev->dev, "Remapped CLINT\n");
  info("CLINT : phys=%px virt=%px size=%px\n", (void *)clintres.start, clint_regs, (resource_size(&clintres)));

  // Quadrant control
  qc = get_quadrant_ctrl(sc->sci.quadrant_idx);
  if (!qc) {
    dev_info(&pdev->dev, "quadrantr ctrl not found, mapping new\n");
    np = of_parse_phandle(pdev->dev.of_node, "eth,quadrant-ctrl", 0);
    if (!np) {
      dev_err(&pdev->dev, "No %s specified\n", "eth,quadrant-ctrl");
      err = -EINVAL;
      goto out;
    }
    qc = devm_kmalloc(&pdev->dev, sizeof(*qc), GFP_KERNEL);
    if (!qc) {
      err = -ENOMEM;
      goto out;
    }
    qc->quadrant_idx = sc->sci.quadrant_idx;
    list_add(&qc->list, &quadrant_ctrl_list);
    ret = of_address_to_resource(np, 0, &quadctrlres);
    qc->regs = devm_ioremap_resource(&pdev->dev, &quadctrlres);
    if (IS_ERR(qc->regs)) {
      dev_err(&pdev->dev, "could not map quadrant-ctrl regs\n");
      err = PTR_ERR(qc->regs);
      goto out;
    }
  }
  sc->quadrant_ctrl = qc;
  dev_info(&pdev->dev, "Remapped Quadrant's CTL\n");
  info("QUAD CTL : phys=%px virt=%px size=%px\n", (void *)quadctrlres.start, qc->regs, (resource_size(&quadctrlres)));

  // Get reserved memory region from Device-tree
  np = of_parse_phandle(pdev->dev.of_node, "memory-region", 0);
  if (!np) {
    dev_err(&pdev->dev, "No %s specified\n", "memory-region");
    err = -EINVAL;
    goto out;
  }
  // map it to kernel space
  ret = of_address_to_resource(np, 0, &memres);
  if (ret) {
    dev_err(&pdev->dev, "No memory address assigned to the region\n");
    err = -EINVAL;
    goto out;
  }
  sc->l3.pbase = memres.start;
  sc->l3.size = resource_size(&memres);
  sc->l3.vbase = memremap(memres.start, resource_size(&memres), MEMREMAP_WB);
  // sc->l3.vbase = devm_ioremap_resource(&pdev->dev, &memres);
  if (!sc->l3.vbase) {
    dev_err(&pdev->dev, "memremap failed\n");
    err = -ENOMEM;
    goto out;
  }
  dev_info(&pdev->dev, "Remapped cluster's program MEM\n");
  info("CLUSTER L3 : phys=%px virt=%px size=%px\n", (void *)sc->l3.pbase, (void *)sc->l3.vbase, sc->l3.size);

  sc->sci.periph_size = sc->l3.size;
  sc->sci.l1_size = sc->l1.size;
  sc->sci.l3_size = sc->l3.size;
  sc->sci.l3_paddr = (void *)sc->l3.pbase;
  sc->sci.l1_paddr = (void *)sc->l1.pbase;
  sc->sci.clint_base = (uint64_t)clint_regs_p;

  list_add(&sc->list, &sc_list);
out:
  // mutex_unlock(&sn_mtx);
  info("<-------SNITCH PROBE ENDS------->\n");
  return err;
}

/**
 * @brief Cleanup
 * @pdev:	Pointer to platform device structure.
 *
 * Return: 0, on success
 *	    Non-zero error value on failure.
 */
static int snitch_remove(struct platform_device *pdev) { return 0; }

static struct platform_driver snitch_driver = {
    .probe = snitch_probe,
    .remove = snitch_remove,
    .driver =
        {
            .name = "eth_snitch_cluster",
            .of_match_table = snitch_of_match,
        },
};

static char *snitch_devnode(struct device *dev, umode_t *mode) {
  struct sn_cluster *sc = dev_get_drvdata(dev);

  if (mode && sc->mode)
    *mode = sc->mode;
  if (sc->nodename)
    return kstrdup(sc->nodename, GFP_KERNEL);
  return NULL;
}

// ----------------------------------------------------------------------------
//
//   Init Module
//
// ----------------------------------------------------------------------------

int snitch_init(void) {
  int ret;
  char devname[12];
  struct sn_cluster *sc;

  info("Loading Snitch module\n");

  // Create /sys/class/snitch in preparation of creating /dev/snitch
  sn_dev.class = class_create(THIS_MODULE, CLASS_NAME);
  if (IS_ERR(sn_dev.class)) {
    info(KERN_WARNING "can't create class\n");
    return -1;
  }

  // register character device and optain major number so that accesses on the char device are
  // mapped to this module. Request major 0 to get a dynamically assigned major number
  sn_dev.major = register_chrdev(0, DEVICE_NAME, &snitch_fops);
  if (sn_dev.major < 0) {
    info(KERN_ALERT "Registering char device failed with %d\n", sn_dev.major);
    return sn_dev.major;
  }
  sn_dev.class->devnode = snitch_devnode;

  // Discover clusters from devicetree and register
  ret = platform_driver_register(&snitch_driver);
  if (ret) {
    info(KERN_ALERT "Registering platform driver failed: %d\n", ret);
    return ret;
  }

  list_for_each_entry(sc, &sc_list, list) {
    // Use same file operations for all clusters
    sc->fops = &snitch_fops;

    // Use cluster index as device minor number
    sc->minor = sc->sci.cluster_idx;

    // Create file in /dev/
    snprintf(devname, sizeof(devname), DEVICE_NAME "%d", sc->minor);
    sc->this_device = device_create_with_groups(sn_dev.class, NULL, MKDEV(sn_dev.major, sc->minor),
                                                sc, NULL, devname);
    if (IS_ERR(sc->this_device)) {
      info(KERN_WARNING "can't create device in /dev/\n");
    } else {
      info("Created char device /dev/%s\n", devname);
    }
  }

  return 0;
}

// ----------------------------------------------------------------------------
//
//   Cleanup module
//
// ----------------------------------------------------------------------------

void snitch_exit(void) {
  struct sn_cluster *sc;

  // mutex_lock(&sn_mtx);

  list_for_each_entry(sc, &sc_list, list) {
    device_destroy(sn_dev.class, MKDEV(sn_dev.major, sc->minor));
  }

  class_destroy(sn_dev.class);
  unregister_chrdev(sn_dev.major, DEVICE_NAME);

  platform_driver_unregister(&snitch_driver);

  // mutex_unlock(&sn_mtx);

  info("unload complete\n");
}

module_init(snitch_init);
module_exit(snitch_exit);
