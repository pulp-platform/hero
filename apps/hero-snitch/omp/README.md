## Toolchain
Make sure `riscv64-buildroot-linux-gnu-ld` is present in your `HERO_INSTALL/bin` as well as `riscv32-unknown-elf-clang`.

Make sure that clang works by running `riscv32-unknown-elf-clang --version`, in case of error `version GLIBCXX_3.4.21 not found` it is possible that 
buildroot overwrote some libraries. Please re-run `make tc-llvm tc-snitch` to re-write these (should be fast).

## Compiling

Now you can compile the helloworld app in `helloworld` :

```bash
cd helloworld
make
make deploy
```

You may now ssh on the fpga and run `./helloworld`

```bash
SNITCH_DEBUG=0 LIBSNITCH_DEBUG=0 LIBOMPTARGET_INFO=0 LIBOMPTARGET_DEBUG=0 ./helloworld
```