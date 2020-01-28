/*
 * Copyright (C) 2019 ETH Zurich, University of Bologna
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


#include "pulp.h"

#include "io.h"


typedef void (*fptr)(void);

static fptr ctor_list[1] __attribute__((section(".ctors.start"))) = { (fptr) -1 };
static fptr dtor_list[1] __attribute__((section(".dtors.start"))) = { (fptr) -1 };


static void pos_init_do_ctors(void)
{
    fptr *fpp;

    for(fpp = ctor_list+1;  *fpp != 0;  ++fpp)
    {
        (**fpp)();
    }
}



static void pos_init_do_dtors(void)
{
    fptr *fpp;
    for(fpp = dtor_list + 1;  *fpp != 0;  ++fpp)
    {
        (**fpp)();
    }
}


extern int main(int argc, const char * const argv[]);


void pos_init_start()
{
#if PULP_CHIP_FAMILY == CHIP_GAP
  // Always allow JTAG accesses for now as security is not implemented
  hal_pmu_bypass_set (ARCHI_REG_FIELD_SET (hal_pmu_bypass_get (), 1, 11, 1) );
#endif

  pos_soc_init();

  pos_irq_init();

  pos_soc_event_init();

  // Initialize first the memory allocators and the utils so that they are
  // available for constructors, especially to let them declare
  // callbacks
  //__rt_utils_init();
  pos_allocs_init();

  // Call global and static constructors
  // Each module may do private initializations there
  pos_init_do_ctors();

  // Now that the system is ready, activate IO
  pos_io_start();

  // Now now the minimal init are done, we can activate interruptions
  hal_irq_enable();

  if (!hal_is_fc())
  {
      cluster_start(hal_cluster_id(), main);
  }
}


void pos_init_stop()
{
    // Close IO to flush them
    pos_io_stop();

    /* Call global and static destructors */
    pos_init_do_dtors();
}