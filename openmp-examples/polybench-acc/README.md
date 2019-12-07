# PolyBench-ACC Benchmarks ported to HERO

This is a collection of kernels from the OpenMP part of the [PolyBench-ACC][] benchmark suite ported to HERO.

More kernels can be added as needed, but please do not add `durbin` because its OpenMP parallelization is mathematically wrong (dependency on previous iteration in parallelized loop).

[PolyBench-ACC]: https://cavazos-lab.github.io/PolyBench-ACC/
