set(DESIGN pulp_cluster)

cmake_minimum_required(VERSION 3.8)
project(${DESIGN} CXX)

find_package(verilator REQUIRED)

# SystemC dependencies
set(THREADS_PREFER_PTHREAD_FLAG ON)
find_package(Threads REQUIRED)

# Find SystemC using SystemC's CMake integration
find_package(SystemCLanguage QUIET)

# Create a new executable target that will contain all your sources
add_executable(${DESIGN} pulp_cluster.cpp)

set_property(
    TARGET ${DESIGN}
    PROPERTY CXX_STANDARD ${SystemC_CXX_STANDARD}
  )

# Add the Verilated circuit to the target
verilate(${DESIGN} TOP_MODULE pulp_cluster
    VERILATOR_ARGS -lint-only 
    SOURCES -f vcode.xt.f
)

verilator_link_systemc(${DESIGN})
