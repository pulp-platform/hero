#!/bin/tcsh -f

setenv HERO_INSTALL /home/astrohan/utils/pulp/hero_toolchain
if (!(-d $HERO_INSTALL)) then
    sudo mkdir $HERO_INSTALL
endif
unsetenv LD_LIBRARY_PATH 

#git submodule update --init --recursive
git pull --recurse-submodule

make prem-unset
make tc-pulp -j
touch done_tc-pulp

make tc-hrv-olinux
touch done-tc-hrv

set path = ($HERO_INSTALL/bin $path)
set path = ($HERO_INSTALL/lib $path)
set path = ($HERO_INSTALL/riscv-gcc/bin $path)
set path = ($HERO_INSTALL/riscv-gcc/lib $path)
set path = ($HERO_INSTALL/riscv32-unknown-elf/bin $path)
set path = ($HERO_INSTALL/riscv32-unknown-elf/lib $path)

# pip3 install artifactory sqlalchemy openpyxl build
make sdk-pulp
touch sdk-pulp

make sdk-hrv


