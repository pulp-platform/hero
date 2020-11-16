# Virtual Memory Management (VMM) Library for PULP

This library, together with a [software-controlled IOMMU called *RAB*][rab], allows PULP to
share the virtual memory space with an application running on a host processor in a Heterogeneous
SoC.

## Usage

The API is documented in-line in the [main header file of the library][vmm.h].  At the highest
level, you can statically designate one PE to handle all RAB misses:
```c
#include "pulp.h"

// Define shared variable to communicate end of application.
RT_L1_DATA volatile unsigned done = 0;

int main()
{
    // Designate PE 0 to run the miss handler.
    if (rt_core_id() == 0) {
        do {
            // Handle all outstanding RAB misses.
            const int ret = handle_rab_misses();
            // If the function does not report success or that no misses needed handling, that's an
            // error.
            if (!(ret == 0 || ret == -ENOENT)) {
                rt_error("RAB miss handling returned error: %d\n", -ret);
                break;
            }
        // Stop handling misses when the other PEs are done.
        } while (!done);
    } else {
        /* Insert application code run by other PEs. */
        // Signal completion to the miss handler.
        done = 1;
    }
}
```

The lower-level functions allow you to translate an individual virtual address and to map individual
pages.

## Internals

The main architecture of this library is described in a [paper we published in 2017][paper].

## Maintainers

- Andreas Kurth (akurth@iis.ee.ethz.ch)
- Pirmin Vogel (vogelpi@iis.ee.ethz.ch)

[rab]: https://github.com/pulp-platform/axi_rab
[paper]: https://dl.acm.org/citation.cfm?doid=3145508.3126560
[vmm.h]: https://github.com/pulp-platform/libvmm/blob/master/include/vmm/vmm.h
