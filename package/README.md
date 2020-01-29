# Buildroot packages
Contains package scripts to conveniently build HEROi host setup and other board support infrastructure as part of the Buildroot build process. Currently includes the following packages:
* ariane-support: support library for Ariane to initialize random numbers
* hero-apps: the applications shipped with HERO (see the `apps` subdirectory)
* hero-openmp: the LLVM libomptarget support library for the HERO host platform (see the `toolchain` subdirectory)
* libhero-target: hero-target support library (might be deprecated in the future)
* libpulp: userspace support library for PULP accelerator (see the `support` subdirectory)
* pulp-driver: Linux kernel driver for PULP accelerator (see the `support` subdirectory)
* riscv-pk-ariane: the custom bbl bootloader for Ariane
* vitetris: tetris game to play on Ariane
* zynq-fclkcfg: driver for clock configuration on Zynq(MP) boards
* zynq-mkbootimage: creates required boot.bin image for booting Zynq(MP)
