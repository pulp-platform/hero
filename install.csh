#!/bin/tcsh -f

if (!(-d hero_toolchain)) then
    mkdir hero_toolchain
endif
setenv GIT_TOP      `git rev-parse --show-toplevel`
setenv HERO_INSTALL $GIT_TOP/hero_toolchain
unsetenv LD_LIBRARY_PATH 

#git submodule update --init --recursive
git pull --recurse-submodule

make prem-unset
make tc-pulp -j
touch done_tc-pulp

make tc-hrv-olinux -j
touch done-tc-hrv

set path = ($HERO_INSTALL/bin $path)
set path = ($HERO_INSTALL/lib $path)
set path = ($HERO_INSTALL/riscv-gcc/bin $path)
set path = ($HERO_INSTALL/riscv-gcc/lib $path)
set path = ($HERO_INSTALL/riscv32-unknown-elf/bin $path)
set path = ($HERO_INSTALL/riscv32-unknown-elf/lib $path)

# # pip3 install artifactory sqlalchemy openpyxl build
# make sdk-pulp -j
# touch sdk-pulp
# 
# make sdk-hrv


