# Host Architecture Abstractions for PULP

This library offers PULP a uniform interface to co-operate with various host processor architectures
in a Heterogeneous SoC.  Currently, the ARMv7 and ARMv8 (64-bit) architectures are implemented.

## API

The current API offers functions and definitions to work with [virtual addresses][virt_addr.h],
[physical addresses][phys_addr.h], and the [page table][pgtable_hwdef.h] of a process running on the
host.  The API is documented in-line in the files linked above.

## Maintainers

- Andreas Kurth (akurth@iis.ee.ethz.ch)
- Pirmin Vogel (vogelpi@iis.ee.ethz.ch)

[pgtable_hwdef.h]: https://github.com/pulp-platform/archi-host/tree/master/include/archi-host/pgtable_hwdef.h
[phys_addr.h]: https://github.com/pulp-platform/archi-host/tree/master/include/archi-host/phys_addr.h
[virt_addr.h]: https://github.com/pulp-platform/archi-host/tree/master/include/archi-host/virt_addr.h
