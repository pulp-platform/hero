/*
 * Copyright (C) 2018 ETH Zurich and University of Bologna
 * 
 * Authors: 
 *    Alessandro Capotondi, UNIBO, (alessandro.capotondi@unibo.it)
 *    Germain Haugou,       ETH,   (germain.haugou@iis.ee.ethz.ch)
 */

/* Copyright (C) 2005-2014 Free Software Foundation, Inc.
 * C ontributed by Richard Henderson <r*th@redhat.com>.
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

/* LIBGOMP main entry point.  */

#include "libgomp.h"

/*Application Entry Point*/
#if PULP_CHIP == CHIP_HERO_Z_7045
int main(int argc, char **argv, char **envp){
    return 0;
}
#else
extern int main(int argc, char **argv, char **envp);
#endif

/* Private vars */
int _argc;
char **_argv;
char **_envp;

/* omp_initenv() - initialize environment & synchronization constructs */
ALWAYS_INLINE void
omp_initenv( )
{
    uint32_t i, nprocs;
    nprocs = get_num_procs();

    /* Init Thread Pool Information */
    gomp_set_thread_pool_idle_cores( nprocs - 1);
    gomp_set_thread_pool( 0x1U );
    gomp_thread_pool_lock_init();
    
    /* Init Curr Team for each threads Thread Pool Information */
    for(i = 0; i < nprocs; ++i)
        gomp_set_curr_team(i, (gomp_team_t *) NULL);

    /* Init Team Descriptor Pre-allocated Pool */
    gomp_team_pool_init();

    /* Init WS Descriptor Pre-allocated Pool */
    gomp_ws_pool_init();

    /* Set NULL lru team */
    gomp_set_lru_team((gomp_team_t *) NULL);

    gomp_print_thread_info();
    return;
}


/* omp_SPMD_worker() - worker threads spin until work provided via GOMP_parallel_start() */
ALWAYS_INLINE int
omp_SPMD_worker()
{
    uint32_t i;
    int retval = 0;
    uint32_t pid = get_proc_id();
    
    if (pid == MASTER_ID)
    {
        gomp_team_t *root_team;
        
        /* Create "main" team descriptor. This also intializes master core's curr_team descriptor */
        gomp_master_region_start( NULL, NULL, 0x0, &root_team );

        /* Warm LRU team */
        gomp_init_lru_team();

        /* wait all the threads */
        MSGBarrier_Wait( root_team->nthreads, root_team->proc_ids );

        if( get_cl_id() == MASTER_ID )
        {

#if PULP_CHIP == CHIP_HERO_Z_7045
            retval = gomp_offload_manager();
#else
            /* Enter to the application Main */
            retval = main(_argc, _argv, _envp);
#endif
            target_desc.fn = (void (*) (void *)) OMP_SLAVE_EXIT;
            for( i = 1; i < DEFAULT_TARGET_MAX_NTEAMS; ++i )
                gomp_hal_hwTrigg_Team( i );
        }
        else
        {
            MSGBarrier_swDocking( pid );
            while (1)
            {
                void (*targetFn) (volatile void *) = (void (*) (volatile void *)) target_desc.fn;
                volatile void * args = (volatile void *) target_desc.hostaddrs;

                /* Exit runtime loop... */
                if ( (uint32_t) targetFn == (uint32_t) OMP_SLAVE_EXIT) 
                {
                    // we are done!!
                    break;
                }      
                /* Have work! */
                else
                {
                    targetFn(args);
                }
                MSGBarrier_swDocking( pid );
            }
        }

        /* Release All the Threads to conclude the runtime */
        for( i = 1; i < root_team->nthreads; ++i)
            gomp_set_curr_team(i, OMP_SLAVE_EXIT);
        
         MSGBarrier_hwRelease( root_team->team^(0x1<<pid) );
    } // MASTER
    else
    {
        MSGBarrier_hwDocking( pid );
        while (1)
        {
            volatile gomp_team_t *curr_team = (volatile gomp_team_t *) gomp_get_curr_team( pid );

            /* Exit runtime loop... */
            if ( curr_team ==  OMP_SLAVE_EXIT) 
            {
                // we are done!!
                break;
            }      
            /* Have work! */
            else
            {
                volatile task_f * omp_task_f;
                volatile int **omp_args;

                #if defined(PROFILE0) && defined(TRACE_BASE_ADDR)
                pulp_trace(TRACE_OMP_PARALLEL_ENTER);
                #endif
                
                gomp_init_thread( pid, (gomp_team_t *)curr_team);
                omp_task_f = (void*) (&curr_team->omp_task_f);
                omp_args = (void*) (&curr_team->omp_args);
                (**omp_task_f)((int) *omp_args);

                #if defined(PROFILE0) && defined(TRACE_BASE_ADDR)
                pulp_trace(TRACE_OMP_PARALLEL_EXIT);
                #endif
            }
            MSGBarrier_hwSlaveEnter( curr_team->barrier_id );
        }
    }
    
    // Restore barrier 0 as it is used in crt0
#if EU_VERSION == 1
    pulp_barrier_setup(0, get_core_num(), (1<<get_core_num()) - 1);
#endif

    return retval;
}

/* main routine */
void
omp_init ()
{
    /* init HAL */
    gomp_hal_init();

    /* The MASTERs (one per-cluster) execute omp_initenv().. */
    if (get_proc_id() == MASTER_ID)
        omp_initenv();
    
    int err = omp_SPMD_worker();

    if (get_proc_id() == MASTER_ID) exit(err);
}


static void omp_entry()
{
    rt_team_fork(rt_nb_pe(), omp_init, NULL);
}
    
RT_BOOT_CODE __attribute__((constructor))  void omp_constructor()
{
  __rt_cluster_entry =  omp_entry;
}
