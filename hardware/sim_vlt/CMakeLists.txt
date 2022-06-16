######################################################################
#
# DESCRIPTION: Verilator CMake Example: Small CMakeLists.txt with SystemC tracing
#
# This is an top cmake script to build a verilog to SystemC project
# using CMake and Verilator.
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2020 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0
#
######################################################################

# This top builds the tracing_sc example using CMake
# To use it, run the following:

# cd /path/to/verilator/tops/cmake_tracing_sc
# rm -rf build && mkdir build && cd build
# cmake ..
# cmake --build .

cmake_minimum_required(VERSION 3.8)
project(cmake_tracing_sc_top CXX)

find_package(verilator REQUIRED)
if (NOT verilator_FOUND)
  message(FATAL_ERROR "Verilator was not found. Either install it, or set the VERILATOR_ROOT environment variable")
endif()

# SystemC dependencies
set(THREADS_PREFER_PTHREAD_FLAG ON)
find_package(Threads REQUIRED)

# Find SystemC using SystemC's CMake integration
find_package(SystemCLanguage QUIET)

# Create a new executable target that will contain all your sources
add_executable(top ./top.cpp)

set_property(
  TARGET top
  PROPERTY CXX_STANDARD ${SystemC_CXX_STANDARD}
  )

# Add the Verilated circuit to the target
verilate(top SYSTEMC COVERAGE TRACE
  #INCLUDE_DIRS "../make_tracing_sc"
  VERILATOR_ARGS -sv +1800-2017ext+ --assert --autoflush --sc +notimingchecks --top-module top  +define+SYNTHESIS +define+TARGET_SYNTHESIS
  SOURCES -f vcode.f
)

verilator_link_systemc(top)
