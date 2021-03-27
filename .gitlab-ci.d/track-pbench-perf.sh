#!/usr/bin/env bash

HERE=$(dirname "$(readlink -f "$0")")
BENCH=$1

# Get the current execution time for the benchmark
NEW_TIME=$(cat "$HERE/../vsim-polybench-perf-stats.txt" | grep "^$BENCH:" | cut -d' ' -f2)

# Get the master execution time for the benchmark
OLD_TIME=
if [ -f "/usr/scratch/dolent4/gitlabci/hero-pbench-perf-tracker.txt" ]; then
  OLD_TIME=$(cat "/usr/scratch/dolent4/gitlabci/hero-pbench-perf-tracker.txt" | grep "^$BENCH:" | cut -d' ' -f2)
fi

# If we got no time, use OLD_TIME 1.
if [ "$OLD_TIME" = "" ]; then
  echo "Found no old time for $BENCH, using 1"
  OLD_TIME=1
fi

# Check that we are not more than 5% slower than the current master branch. If
# we are, exit with code 4 which GitLab CI should treat as a warning.
HAS_WARNINGS=0
REL_TIME=$(echo "${NEW_TIME}.0 / ${OLD_TIME}.0" | bc -l)
if (( $(echo "$REL_TIME > 1.05" | bc -l) )); then
  echo "WARNING: $BENCH: New cycle count $NEW_TIME is $REL_TIME times higher than old cycle count $OLD_TIME (threshold 1.05)."
  HAS_WARNINGS=1
else
  echo "NOTICE : $BENCH: New cycle count $NEW_TIME is within threshold of old cycle count $OLD_TIME."
fi

# If this is the master branch, keep these results as the baseline.
if [ "$CI_COMMIT_BRANCH" = "master" ]; then
  echo "This is the master branch, storing the new cycle counts as reference."
  cp "$HERE/../vsim-polybench-perf-stats.txt" "/usr/scratch/dolent4/gitlabci/hero-pbench-perf-tracker.txt"
fi

# Exit with "allow_failure" exit code if has warnings
if [ ! $HAS_WARNINGS -eq 0 ]; then
  exit 4
fi
