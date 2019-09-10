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
#ifndef _PULP_SMMU_H_
#define _PULP_SMMU_H_

#include <linux/iommu.h> /* iommu stuff */

#include "pulp_module.h"

#define PULP_SMMU_GLOBAL_BYPASS // enable global SMMU bypassing for maximum bypass performance

// constants
#define SMMU_GR0_OFFSET_B 0x0
#define SMMU_SMR_OFFSET_B 0x800
#define SMMU_S2CR_OFFSET_B 0xC00
#define SMMU_CBAR_OFFSET_B 0x1000

#define SMMU_CB_SCTLR_OFFSET_B 0x0
#define SMMU_CB_RESUME_OFFSET_B 0x8
#define SMMU_CB_MAIR0_OFFSET_B 0x38
#define SMMU_CB_MAIR1_OFFSET_B 0x3C
#define SMMU_CB_FSR_OFFSET_B 0x58

#define SMMU_GR0_CLIENTPD 0
#define SMMU_GR0_TRANSIENTCFG 6
#define SMMU_GR0_MEMATTR 16
#define SMMU_GR0_MTCFG 20
#define SMMU_GR0_SHCFG 22
#define SMMU_GR0_RACFG 24
#define SMMU_GR0_WACFG 26
#define SMMU_GR0_NSCFG 28

#define SMMU_S2CR_SHCFG 8
#define SMMU_S2CR_MTCFG 11
#define SMMU_S2CR_MEMATTR 12
#define SMMU_S2CR_TYPE 16
#define SMMU_S2CR_NSCFG 18
#define SMMU_S2CR_RACFG 20
#define SMMU_S2CR_WACFG 22
#define SMMU_S2CR_TRANSIENTCFG 28

#define SMMU_CBAR_BPSHCFG 8

#define SMMU_CB_FSR_TF 1

#define SMMU_SCTLR_CFIE (1 << 6)

#define SMMU_N_BITS_STREAM_ID 14

#define SMMU_FLAGS_CC 0b00000001
#define SMMU_FLAGS_SHPT_EMU 0b00000010

// type definitions
typedef enum {
  READY = 0,
  WAIT = 1,
} WorkerStatus;

typedef struct SmmuPage SmmuPage;
struct SmmuPage {
  unsigned long iova;
  struct page *page_ptr;
  struct SmmuPage *previous;
};

/** @name SMMU configuration functions
 *
 * @{
 */

/** Initialize SMMU.

 *  This function initializes the SMMU. In particular, it extracts the stream matching registers
 *  and entries assigned at startup based on the known stream IDs, and then enables bypassing for
 *  these stream matching entries.

  \param    pulp_ptr Pointer to PulpDev structure.

  \return   0 on success, a nonzero errno on errors.
 */
int pulp_smmu_init(PulpDev *pulp_ptr);

/** Enable SMMU.

 *  This function enables and sets up the SMMU for virtual-to-physical address translation for
 *  PULP. To this end, it disables all user-space mappings in the RAB, sets up the RAB for
 *  bypassing and sets up the SMMU through the Linux IOMMU API.

  \param    pulp_ptr Pointer to PulpDev structure.
  \param    flags    Control flags for the RAB and SMMU.

  \return   0 on success, a nonzero errno on errors.
 */
int pulp_smmu_ena(PulpDev *pulp_ptr, unsigned flags);

/** Disable SMMU.

 *  This function disables virtual-to-physical address translation for PULP by the SMMU.
 *  It disables the RAB bypassing and enables SMMU bypassing.

  \param    pulp_ptr Pointer to PulpDev structure.

  \return   0 on success, a nonzero errno on errors.
 */
int pulp_smmu_dis(PulpDev *pulp_ptr);

//!@}

/** @name SMMU fault management functions
 *
 * @{
 */

/** Schedule the SMMU bottom-half fault handler.

 *  This function is the top-half SMMU fault handler registered to the Linux IOMMU API.
 *  On a translation fault, it is called in interrupt context and then schedules the
 *  bottom half in process context.

  \param    see linux include/linux/iommu.h

  \return   0 on success.
 */
int pulp_smmu_fh_sched(struct iommu_domain *smmu_domain_ptr, struct device *dev_ptr, unsigned long iova, int flags,
                       void *smmu_token_ptr);

/** Handle SMMU translation faults.

 *  This function is the bottom-half SMMU fault handler scheduled in process context by the top
 *  half. It handles translation faults by pinning the requested user-space pages an mapping them
 *  to the IOMMU context or I/O virtual address space.

 */
void pulp_smmu_handle_fault(void);

//!@}

#endif /*_PULP_SMMU_H_*/
