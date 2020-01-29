# Toolchains
Contains the configuration for the base toolchains built using Crosstool-NG as well as the heterogeneous toolchain based on LLVM.

# Crosstool base toolchains
Configuration for Crosstool toolchain is in the different `.config` files and built using the `build.sh` script. Currently toolchains are available for the following setups:
* `har-obare`: bare-metal toolchain for AArch64
* `har-olinux`: Linux toolchain for AArch64
* `hrv-obare`: bare-metal toolchain for RISC-V
* `hrv-olinux`: Linux toolchain for RISC-V

# Heterogeneous toolchains
The heterogeneous toolchain is based on LLVM with several custom patches for our needs as well as a libomptarget plugin for PULP and several LLVM passes to implement our mixed-data-model logic as well as to provide a wrapper for OpenMP to allow for easier integration with the original GCC based offloading stack. 
