## Toolchain
Make sure `riscv64-buildroot-linux-gnu-gcc` is present in your `HERO_INSTALL/bin` as well as `riscv32-unknown-elf-clang`.

Make sure that clang works by running `riscv32-unknown-elf-clang --version`, in case of error `version GLIBCXX_3.4.21 not found` it is possible that 
buildroot overwrote some libraries. Please re-run `make tc-llvm tc-snitch` to re-write these (should be fast).

## Compiling

Now you can compile the offloader script in `cva6-app` and the snitch app in `snitch-app`.

Or run from here :

```bash
make all
make deploy -B
```

You may now ssh on the fpga and run

```bash
cd deploy_standalone
./bringup hello_world.bin file_to_offload.txt
```