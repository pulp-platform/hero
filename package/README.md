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

To work with the packages during development it is useful to go to the respective output directory (for example `output/br-har`) and rebuild the respective packages there before transferring them back to the NFS or to the device. This can be done as follows for the core HERO infrastructure:
```
make pulp-driver-rebuild libpulp-rebuild hero-openmp-rebuild hero-apps-rebuild
scp target/lib/modules/<kernel_version>/extra/pulp.ko <root_dir>/mnt/root
scp target/usr/lib/libpulp.so <root_dir>/usr/lib/
scp target/usr/lib/libomp* <root_dir>/usr/lib/
scp target/usr/bin/pulp-standalone <root_dir>/usr/bin
```
