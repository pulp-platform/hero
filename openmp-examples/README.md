# HERO OpenMP Examples
This directory contains a set of examples of OpenMP applications for the HERO platform. You can find additional information about the OpenMP accelerator model inside the [OpenMP 4.5 Specs](https://www.openmp.org/wp-content/uploads/openmp-examples-4.5.0.pdf).

# Applications
The applications are split in several basic heterogeneous examples together with a set of customized [Polybench-ACC](https://cavazos-lab.github.io/PolyBench-ACC/) benchmarks extended with a variant to operate on the accelerator-local data using DMA engines. 

Applications can be built by running `make` in the respective directory. Various options are supported to adjust the compilation flow which are as follows:
 * `only`: Set to `pulp` to create standalone applications, otherwise heterogeneous applications are built (default).
 * `opt`: determines the level of optimizations between all passes, default to `3` (`-O3`).
 * `cflags`: additional compilation flags to pass during compilation (can for example be used in the benchmarks to change the dataset).

Additionally extra flags are supported for the Polybench-ACC benchmarks:
 * `threads`: Number of threads to run in parallel (bound by the number of accelerator cores)
 * `mem`: Place to allocate local memory from either `1` for L1 (cluster-local memory), `2` L2 (accelerator-local memory) or `3` for L3 (global shared main memory).
 * `dma`: If a variant with DMA copy to local memory should be used. Either `n`, to not use local memory, `y` to use DMA to local memory with automatic optimizations to the device address space or `optnone` to use DMA to local memory but not to optimize the access to global memory.
 * `dump`: Dump the output of the computation to standard output, `y` for yes and `n` for no.
 * `offload-target`: Target device for offloading, either `copy` for copy-based offloading, otherwise shared virtual memory (SVM) is used.
