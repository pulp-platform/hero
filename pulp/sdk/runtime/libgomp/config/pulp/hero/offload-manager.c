/*
 * Copyright (C) 2018 ETH Zurich and University of Bologna
 *
 * Authors:
 *    Alessandro Capotondi, UNIBO, (alessandro.capotondi@unibo.it)
 */

/* Copyright (C) 2005-2014 Free Software Foundation, Inc.
 *
 * This file is part of the GNU OpenMP Library (libgomp).
 *
 * Libgomp is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3, or (at your option)
 * any later version.
 *
 * Libgomp is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 * more details.
 *
 * Under Section 7 of GPL version 3, you are granted additional
 * permissions described in the GCC Runtime Library Exception, version
 * 3.1, as published by the Free Software Foundation.
 *
 * You should have received a copy of the GNU General Public License and
 * a copy of the GCC Runtime Library Exception along with this program;
 * see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see
 * <http://www.gnu.org/licenses/>.
 */

#include <stdint.h>
#include "hal/pulp.h"
#include "vmm/vmm.h"
#include "hal/rab/rab_v1.h"

#include "hero/offload-manager.h"

//FIXME consider to move these variables to L1 (vars it is ususally Empty when OpenMP4 Offload is used)
void** offload_func_table;
uint32_t nb_offload_funcs;
void** offload_var_table;
uint32_t nb_offload_vars;

void
target_register_lib (const void *target_table)
{
    return;
}

// Shrinked gomp_team_t descriptor
typedef struct offload_rab_miss_handler_desc_s
{
    void (*omp_task_f) (void *data);
    void *omp_args;
    int barrier_id;
} offload_rab_miss_handler_desc_t;


void
offload_rab_misses_handler(uint32_t *status)
{
    if (DEBUG_LEVEL_OFFLOAD_MANAGER > 0)
        rt_debug("offload_rab_misses_handler: synch @%p (0x%x)\n", status, *(volatile unsigned int *) status);
    do {
        handle_rab_misses();
    } while (*((volatile uint32_t *) status) != 0xdeadbeefU);
    if (DEBUG_LEVEL_OFFLOAD_MANAGER > 0)
        rt_debug("offload_rab_misses_handler: synch @%p (0x%x)\n", status, *(volatile unsigned int *) status);
}

int
gomp_offload_manager ( )
{
    //Init the manager (handshake btw host and accelerator is here)
    gomp_init_offload_manager();

    //FIXME For the momenent we are not using the cmd sended as trigger.
    // It should be used to perform the deactivation of the accelerator,
    // as well as other operations, like local data allocation or movement.
    //FIXME Note that the offload at the moment use several time the mailbox.
    // We should compact the offload descriptor and just sent a pointer to
    // that descriptor.
    uint32_t cmd = (uint32_t)NULL;

    // Offloaded function pointer and arguments
    void (*offloadFn)(void **) = NULL;
    void **offloadArgs = NULL;
    int nbOffloadRabMissHandlers = 0x0;
    uint32_t offload_rab_miss_sync = 0x0U;
    offload_rab_miss_handler_desc_t rab_miss_handler = {(void (*) (void *)) offload_rab_misses_handler, (void *) &offload_rab_miss_sync, -1};

    int cycles = 0;
    rab_miss_t rab_miss;
    reset_vmm();

    while(1) {
        if (DEBUG_LEVEL_OFFLOAD_MANAGER > 0)
            rt_debug("Waiting for command...\n");

        // (1) Wait for the offload trigger.
        mailbox_read((unsigned int *)&cmd);
        if (PULP_STOP == cmd) {
            if (DEBUG_LEVEL_OFFLOAD_MANAGER > 0)
                rt_debug("Got PULP_STOP from host, stopping execution now.\n");
            break;
        }

        // (2) The host sends through the mailbox the pointer to the function that should be
        // executed on the accelerator.
        mailbox_read((unsigned int *)&offloadFn);

        if (DEBUG_LEVEL_OFFLOAD_MANAGER > 0)
            rt_debug("tgt_fn @ 0x%x\n",(unsigned int)offloadFn);

        // (3) The host sends through the mailbox the pointer to the arguments that should
        // be used.
        mailbox_read((unsigned int *)&offloadArgs);

        if (DEBUG_LEVEL_OFFLOAD_MANAGER > 0)
            rt_debug("tgt_vars @ 0x%x\n",(unsigned int)offloadArgs);

        // (3b) The host sends through the mailbox the number of rab misses handlers threads
        mailbox_read((unsigned int *)&nbOffloadRabMissHandlers);

        if (DEBUG_LEVEL_OFFLOAD_MANAGER > 0)
            rt_debug("nbOffloadRabMissHandlers %d\n", nbOffloadRabMissHandlers);

        // (3c) Spawing nbOffloadRabMissHandlers
        nbOffloadRabMissHandlers = nbOffloadRabMissHandlers < rt_nb_pe()-1 ? nbOffloadRabMissHandlers : rt_nb_pe()-1;
        if(nbOffloadRabMissHandlers) {
            offload_rab_miss_sync = 0x0U;
            for(int pid = rt_nb_pe()-1, i = nbOffloadRabMissHandlers; i > 0; i--, pid--){
                if (DEBUG_LEVEL_OFFLOAD_MANAGER > 0)
                    rt_debug("waking up RAB miss handler %d\n", pid);
                gomp_set_curr_team(pid, (gomp_team_t *) &rab_miss_handler);
                gomp_hal_hwTrigg_core( 0x1U << pid);
            }
            gomp_atomic_del_thread_pool_idle_cores(nbOffloadRabMissHandlers);   
        }

        // (4) Ensure access to offloadArgs. It might be in SVM.
        if(offloadArgs!=NULL)
            pulp_tryread((unsigned int *)offloadArgs);

        reset_timer();
        start_timer();

        // (5) Execute the offloaded function.
        offloadFn(offloadArgs);
        stop_timer();
        cycles = get_time();

        mailbox_write(TO_RUNTIME | 2);
        mailbox_write(PULP_DONE);
        mailbox_write(cycles);

        if (DEBUG_LEVEL_OFFLOAD_MANAGER > 0)
            rt_debug("Kernel execution time [PULP cycles] = %d\n", cycles);

        if(nbOffloadRabMissHandlers) {
            offload_rab_miss_sync = 0xdeadbeefU;
            gomp_atomic_add_thread_pool_idle_cores(nbOffloadRabMissHandlers);
        }
    }

    return 0;
}

