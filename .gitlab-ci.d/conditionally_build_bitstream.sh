#!/bin/bash

# Script for use by the GitLab CI to avoid rebuilding the FPGA bitstream if
# we already built a version from the same (unchanged) source.
#
# Author: bjoernf, Feb 2020

# TODO: There is a potential race condition if one build is updating the cached
#       files while another is fetching them. We should fix this.

# The locations of the cached files. We store one cached build per branch, and
# keep track of the SHA of the commit that was used for the build.
CACHE_PATH="/usr/scratch/umbrail/bjoernf/gitlabci/$CI_COMMIT_BRANCH"
BIT_CACHE_PATH="$CACHE_PATH/hero_exilzcu102_wrapper.bit"
HDF_CACHE_PATH="$CACHE_PATH/hero_exilzcu102_wrapper.hdf"
SHA_CACHE_PATH="$CACHE_PATH/git_commit_sha.txt"

# The relative paths from the HERO base repo where the output files from the
# FPGA build should be put.
BIT_BUILD_LOC="hardware/fpga/hero_exilzcu102/hero_exilzcu102.runs/impl_1"
HDF_BUILD_LOC="hardware/fpga/hero_exilzcu102/hero_exilzcu102.sdk"
BIT_BUILD_PATH="$BIT_BUILD_LOC/hero_exilzcu102_wrapper.bit"
HDF_BUILD_PATH="$HDF_BUILD_LOC/hero_exilzcu102_wrapper.hdf"

# The relative path from the HERO base repo where the FPGA build Makefile is
# located.
FPGA_PATH="hardware/fpga"

# The SHA of the new commit that we are doing the CI for.
NEWSHA=$CI_COMMIT_SHA;

# The main decision variable, if YES, we rebuild the bitstream, if NO, we use
# the versions that are stored in CACHE_PATH. We must default to rebuilding,
# conservatively.
REBUILD=YES

# THIS SCRIPT MUST BE RUN FROM THE ROOT OF THE HERO BASE REPO. Check that the
# file structure looks like expected. TODO: Make check stronger.
if [ ! -f "$FPGA_PATH/Makefile" ]; then
  echo "Cannot find the relevant Makefile for HW build!";
  exit 1;
fi

# This script is intended to run from the CI. Make sure we have the environment
# we expect.
if [ -z "$CI_COMMIT_BRANCH" ]; then
  echo "CI_COMMIT_BRANCH not set";
  exit 1;
fi
if [ -z "$CI_COMMIT_SHA" ]; then
  echo "CI_COMMIT_SHA not set";
  exit 1;
fi

# Check if there is a previous build. If there is none we need to rebuild, and
# if there is, we need the SHA of the commit used to build to figure out if we
# can reuse the output bitstream.
if [ -f "$SHA_CACHE_PATH" ]; then
  OLDSHA=$(cat "$SHA_CACHE_PATH");

  # Check that this commit still exists in the repo, otherwise we cannot make
  # a diff against it.
  if git cat-file -e $OLDSHA; then

    echo "Will compare old commit $OLDSHA with new $NEWSHA"

    # We found a cached version of the bitstream that could potentially be used.
    # Use the SHA of the old commit used to build to figure out if there have
    # been any changes that mean we have to rebuild.
    DIFFLINES=$(git diff $OLDSHA $NEWSHA -- hardware/deps hardware/fpga hardware/src | wc -l)
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

      # We also want to rebuild if the files that do exist are very old
      # (currently over 7 days). We could check both files, but for now we are
      # happy with just checking the BIT.
      if [[ $(find "$BIT_CACHE_PATH" -mtime +7 -print) ]]; then
        echo "File is very old, we should rebuild it for the fun of it!";
        REBUILD=YES
      fi
    fi
  else
    echo "The cached SHA does not exist in the repo (any more?). Must rebuild."
  fi
else
  echo "No old commit for branch -- need to rebuild";
fi

# Be verbose, it will be helpful when reading the CI logs.
echo "Should we rebuild? $REBUILD"

# Trigger the rebuild and update the cache if we decided to do so, otherwise
# fetch the cached files.
if [ "$REBUILD" = "YES" ]; then
  echo "Starting rebuild";
  make -C "$FPGA_PATH" all
  if [ $? -ne 0 ]; then
    echo "Build failed!";
    exit 1;
  fi

  # Copy successful build to output directory.
  echo "Updating cache";
  mkdir -p "$CACHE_PATH"
  cp "$BIT_BUILD_PATH" "$BIT_CACHE_PATH"
  cp "$HDF_BUILD_PATH" "$HDF_CACHE_PATH"
  echo $NEWSHA > "$SHA_CACHE_PATH"

  # We want to be able to clean up the mess from our own account afterwards.
  chmod -R a+rwx $CACHE_PATH
else
  echo "Fetching cached build from $OLDSHA";
  mkdir -p "$BIT_BUILD_LOC"
  mkdir -p "$HDF_BUILD_LOC"
  cp "$BIT_CACHE_PATH" "$BIT_BUILD_PATH"
  cp "$HDF_CACHE_PATH" "$HDF_BUILD_PATH"
fi

# Update the local config file to point to the bitstream, but only if there
# isn't already a configuration in the local configuration file.
UPDATE_CONFIG=NO
if [ ! -f "local.cfg" ]; then
  UPDATE_CONFIG=YES
fi
if [ -z $(cat local.cfg | grep BR2_HERO_BITSTREAM) ]; then
  UPDATE_CONFIG=YES
fi

# If the previous checks told us to update the local config, do it here.
if [ "$UPDATE_CONFIG" = "YES" ]; then
  REALPATH=$(realpath $BIT_BUILD_PATH);
  echo "Appending new BR2_HERO_BITSTREAM config to local.cfg";
  echo "BR2_HERO_BITSTREAM=\"$REALPATH\"" >> local.cfg
fi

# EOF
