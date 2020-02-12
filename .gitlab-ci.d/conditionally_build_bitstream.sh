#!/bin/bash

BIT_CACHE_PATH="/usr/scratch/umbrail/bjoernf/gitlabci/hero_exilzcu102_wrapper.bit"
HDF_CACHE_PATH="/usr/scratch/umbrail/bjoernf/gitlabci/hero_exilzcu102_wrapper.hdf"

BIT_BUILD_PATH="hardware/fpga/hero_exilzcu102/hero_exilzcu102.sdk/hero_exilzcu102_wrapper.bit"
HDF_BUILD_PATH="hardware/fpga/hero_exilzcu102/hero_exilzcu102.sdk/hero_exilzcu102_wrapper.hdf"

CACHE_MAX_DAYS=7

FPGA_PATH="hardware/fpga"

REBUILD=YES

# THIS SCRIPT MUST BE RUN FROM THE ROOT OF THE HERO BASE REPO.
if [ ! -f "$FPGA_PATH/Makefile" ]; then
  echo "Cannot find the relevant Makefile for HW build!";
  exit 1;
fi

# Check if there is any diff at all.
DIFFLINES=$(git diff HEAD^ HEAD hardware/deps hardware/fpga hardware/src | wc -l)
if [ "$DIFFLINES" -eq "0" ]; then
  echo "There is no diff, don't need to rebuild";
  REBUILD=NO

  # Even if there is no diff, we need to rebuild if the files don't exist
  if [ ! -f "$BIT_CACHE_PATH" ]; then
    echo "Don't have cached BIT, rebuild!";
    REBUILD=YES
  fi
  if [ ! -f "$HDF_CACHE_PATH" ]; then
    echo "Don't have cached HDF, rebuild!";
    REBUILD=YES
  fi

  # We also want to rebuild if the files that do exist are very old (over 7 
  # days). We could check both files, but for now we are happy with just 
  # checking the BIT.
  if [[ $(find "$BIT_CACHE_PATH" -mtime +7 -print) ]]; then
    echo "File is very old, we should rebuild it for the fun of it!";
    REBUILD=YES
  fi
  
fi

echo "Should we rebuild? $REBUILD"

if [ "$REBUILD" = "YES" ]; then
  echo "Starting rebuild";
  make -C "$FPGA_PATH" all
  if [ $? -ne 0 ]; then
    echo "Build failed!";
    exit 1;
  fi

  # Copy successful build to output directory.
  cp "$BIT_BUILD_PATH" "$BIT_CACHE_PATH"
  cp "$HDF_BUILD_PATH" "$HDF_CACHE_PATH"
else
  echo "Fetching cached build";
  cp "$BIT_CACHE_PATH" "$BIT_BUILD_PATH"
  cp "$HDF_CACHE_PATH" "$HDF_BUILD_PATH"
fi

UPDATE_CONFIG=NO
if [ ! -f "local.cfg" ]; then
  UPDATE_CONFIG=YES
fi
if [ -z $(cat local.cfg | grep BR2_HERO_BITSTREAM) ]; then
  UPDATE_CONFIG=YES
fi

if [ "$UPDATE_CONFIG" = "YES" ]; then
  REALPATH=$(realpath $BIT_BUILD_PATH);
  echo "BR2_HERO_BITSTREAM=\"$REALPATH\"" >> local.cfg
fi
