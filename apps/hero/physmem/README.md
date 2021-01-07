# Physical Memory Accessing Library (Header-Only) for Linux

This header-only library provides a simple means to access physical memory on
Linux, without having to `mmap` with the correct flags, dealing with `volatile`
pointers, and the like.

The API is [documented in the header file](./inc/physmem.hpp) in Doxygen syntax.

## Usage

Minimal C++ example application:
```cpp
#include "physmem.hpp"

int main() {
    PhysMem mem(0x10002000, 0x1000); // map 4 KiB starting at 0x10002000
    mem.write_u32(0x10002020, 0x37703770); // write to 0x10002020
    return 0;
}
```
Compile with at least C++11 enabled and add the `inc/` directory in this folder
to the include paths.

The [`Makefile`](./Makefile) and [`example.cc`](./example.cc) in this directory
contain a more complete example.

When cross-compiling, ensure that the `CXX` environment variable is set to the
C++ compiler for the target.
