#!/bin/tcsh -f

if (!(-d hero_toolchain)) then
    mkdir hero_toolchain
endif

#git submodule update --init --recursive
git pull --recurse-submodule

make prem-unset
make tc-pulp -j
touch done_tc-pulp

make tc-hrv-olinux -j
make tc-hrv-obare -j
touch done-tc-hrv

# pip install artifactory sqlalchemy openpyxl build
make sdk-pulp -j
touch sdk-pulp

make sdk-hrv

