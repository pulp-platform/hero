# Copyright 2020 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

cmake_minimum_required(VERSION 3.13)

################################################################################
# PATHS AND SETTINGS
################################################################################

# Path to snitch/sw directory from which snRuntime & co are derived
set(SNITCH_SOFTWARE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../../../vendor/snitch/sw)

# Include cmake files for toolchain
list(APPEND CMAKE_MODULE_PATH ${SNITCH_SOFTWARE_DIR}/cmake)

# snRuntime-cluster to include start_cluster.S/.c
set(SNITCH_RUNTIME snRuntime-cluster CACHE STRING "")

# We want to use the LLVM toolchain
set(CMAKE_TOOLCHAIN_FILE toolchain-llvm CACHE STRING "")

# Link the snitch binary to 0xc0000000 which is a reserved memory region
set(MEM_DRAM_ORIGIN "0xc0000000" CACHE STRING "Base address of external memory")
set(MEM_DRAM_SIZE "512M" CACHE STRING "Size of external memory")


################################################################################
# MACROS
################################################################################

################################################################################
# SOURCES
################################################################################

set(sn_common_src
  ${SNITCH_SOFTWARE_DIR}/snRuntime/src/snitch_hero_support.c
  hier_wake.c
)
set(sn_common_include
  .
)


################################################################################
# PROJECT
################################################################################

# Create project
project(snitch_cluster LANGUAGES C ASM)
add_compile_options(-g -O3)

# Pull snRuntime
include(SnitchUtilities)
add_subdirectory(${SNITCH_SOFTWARE_DIR}/snRuntime snRuntime)
add_subdirectory(${SNITCH_SOFTWARE_DIR}/snBLAS snBLAS)
# add_subdirectory(${SNITCH_SOFTWARE_DIR}/benchmark benchmark)

include_directories(${SNRUNTIME_INCLUDE_DIRS} ${sn_common_include})
include_directories(${SNBLAS_INCLUDE_DIRS})

add_compile_options(-g -O3)
add_definitions(-DSNITCH_HERO)

################################################################################
# LIBRARIES
################################################################################

include_directories(
  ${SNITCH_SOFTWARE_DIR}/applications/include
  ${SNITCH_SOFTWARE_DIR}/applications/data
  ${SNITCH_SOFTWARE_DIR}/applications/src/layers
  ${SNITCH_SOFTWARE_DIR}/applications/src/kernels
  ${SNITCH_SOFTWARE_DIR}/applications/src/utils )
add_library(kernels
  ${SNITCH_SOFTWARE_DIR}/applications/src/kernels/batchnorm.c
  ${SNITCH_SOFTWARE_DIR}/applications/src/kernels/maxpool.c
  ${SNITCH_SOFTWARE_DIR}/applications/src/kernels/gemm.c )
add_library(layers
  ${SNITCH_SOFTWARE_DIR}/applications/src/layers/batchnorm_layer.c
  ${SNITCH_SOFTWARE_DIR}/applications/src/layers/maxpool_layer.c
  ${SNITCH_SOFTWARE_DIR}/applications/src/layers/conv2d_layer.c )
add_library(utils
  ${SNITCH_SOFTWARE_DIR}/applications/src/utils/utils.c )
target_link_libraries(kernels ${SNITCH_RUNTIME})
target_link_libraries(layers ${SNITCH_RUNTIME} kernels utils)
target_link_libraries(utils ${SNITCH_RUNTIME})

################################################################################
# Applications
################################################################################

# Target applications
add_snitch_executable(hello_world ${sn_common_src} snitch_hello_world.c)

