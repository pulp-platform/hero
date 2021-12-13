# Copyright (C) Eta Scale AB. Licensed under the Eta Scale Open Source License. See the LICENSE file for details.

#------------------------------------------------------------------------------
# CMakeLists.txt
#------------------------------------------------------------------------------
# This file was taken and adapted from a tutorial at the Imperial College London
#
# [1] https://github.com/delcypher/srg-llvm-pass-tutorial
#  
cmake_minimum_required(VERSION 2.8.12)
project(hero-llvm-support)

#------------------------------------------------------------------------------
# FindLLVM
#------------------------------------------------------------------------------
# If building against a locally built version of LLVM (this must be built with
# CMake not and not the Autoconf/Makefile build system) you need to set the
# LLVM_DIR cache variable that find_package(LLVM ...) introduces.
# E.g.
# cmake -DLLVM_DIR:PATH=/path/to/llvm/build/share/llvm/cmake /path/to/this_projects_source_directory
find_package(LLVM REQUIRED)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")

if ( "${LLVM_PACKAGE_VERSION}" VERSION_LESS "3.5" )
    message(FATAL_ERROR "Need LLVM >=3.5")
endif()

include_directories("${LLVM_INCLUDE_DIRS}")
message(STATUS "LLVM_INCLUDE_DIRS is ${LLVM_INCLUDE_DIRS}")

message(STATUS "LLVM_TOOLS_BINARY_DIR is ${LLVM_TOOLS_BINARY_DIR}")

#------------------------------------------------------------------------------
# Set compiler flags
#------------------------------------------------------------------------------
# This unfortunately doesn't add much
add_definitions(${LLVM_DEFINITIONS})

include(CheckCXXCompilerFlag)
macro(add_cxx_flag flag name)
    CHECK_CXX_COMPILER_FLAG(${flag} "${name}_SUPPORTED")
    if("${name}_SUPPORTED")
        add_definitions(${flag})
    else()
        message(FATAL_ERROR "${flag} flag is not supported by ${CMAKE_CXX_COMPILER}")
    endif()
endmacro()

# FIXME: Setting flags this way isn't very portable
if (NOT LLVM_ENABLE_RTTI)
    message(STATUS "LLVM was built without RTTI, so we must disable it too for linking to work properly")
    add_cxx_flag(-fno-rtti RTTI) # Can't use LLVMSupport properly if we have rtti
endif()
add_cxx_flag(-std=c++14 CXX14)

#------------------------------------------------------------------------------
# Handy macro to copy files matching a globbing pattern in the current source
# source directory to the current build directory
#------------------------------------------------------------------------------
macro(copy_files_to_build_dir GLOBS)
    file(GLOB ABSOLUTE_PATH_TO_FILES_TO_COPY ${ARGV})

    foreach(file ${ABSOLUTE_PATH_TO_FILES_TO_COPY})
        get_filename_component(filename ${file} NAME)
        configure_file(${filename} ${filename} COPYONLY)
    endforeach()
endmacro()

#------------------------------------------------------------------------------
# Warn if clang is not available
#------------------------------------------------------------------------------
if (NOT EXISTS "${LLVM_TOOLS_BINARY_DIR}/clang")
    message(WARNING "Clang was not found in LLVM_TOOLS_BINARY_DIR. Many of the demo scripts won't work without this")
  endif()

MESSAGE( STATUS "CMAKE_CURRENT_SOURCE_DIR = " ${CMAKE_CURRENT_SOURCE_DIR} )

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall")
#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -pedantic -Wextra")

set(PROJECTS_MAIN_SRC_DIR     ${CMAKE_CURRENT_SOURCE_DIR}/src)
set(PROJECTS_MAIN_INCLUDE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/include)

MESSAGE( STATUS "PROJECTS_MAIN_SRC_DIR = " ${PROJECTS_MAIN_SRC_DIR} )
MESSAGE( STATUS "PROJECTS_MAIN_INCLUDE_DIR = " ${PROJECTS_MAIN_INCLUDE_DIR} )

include_directories(${PROJECTS_MAIN_INCLUDE_DIR})

add_subdirectory(OmpHostPointerLegalizer)
add_subdirectory(OmpKernelWrapper)
