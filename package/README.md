# Buildroot packages
Contains package scripts to conveniently build HEROi host setup and other board support infrastructure as part of the Buildroot build process. Currently includes the following packages:
* hero-apps: the applications shipped with HERO (see the `apps` subdirectory)
* hero-openmp: the LLVM libomptarget support library for the HERO host platform (see the `toolchain` subdirectory)
* libhero-target: hero-target support library (might be deprecated in the future)
* libpulp: userspace support library for PULP accelerator (see the `support` subdirectory)
* pulp-driver: Linux kernel driver for PULP accelerator (see the `support` subdirectory)
* zynq-mkbootimage: creates required boot.bin image for booting Zynq(MP)

To work with the packages during development it is useful to go to the respective output directory (for example `output/br-har`) and rebuild the respective packages there before transferring them back to the NFS or to the device. This can be done as follows for the core HERO infrastructure:
```
make pulp-driver-rebuild libpulp-rebuild hero-openmp-rebuild hero-apps-rebuild
scp target/lib/modules/<kernel_version>/extra/pulp.ko <root_dir>/mnt/root
scp target/usr/lib/libpulp.so <root_dir>/usr/lib/
scp target/usr/lib/libomp* <root_dir>/usr/lib/
scp target/usr/bin/pulp-standalone <root_dir>/usr/bin
```

## References
Every package has a `Config.in` and a `*.mk` file.  The [`Config.in` file][1] defines the configuration options and dependencies of the package.  It is written in the [`Kconfig` language][2] of the Linux kernel.  The [`*.mk` file][3] describes how the package is downloaded, configured, built, and installed.

[1]: https://buildroot.org/downloads/manual/manual.html#_config_files
[2]: https://www.kernel.org/doc/Documentation/kbuild/kconfig-language.txt
[3]: https://buildroot.org/downloads/manual/manual.html#_the_literal_mk_literal_file
