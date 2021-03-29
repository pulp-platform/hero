#!/usr/bin/env bash

HERE=$(dirname "$(readlink -f "$0")")
BENCH=$1

MASTER_REF_FILE=pbench-perf-tracker.txt
MASTER_REF_PATH=$HOME/hero

# Ensure the path where we store the reference counts from the master branch
# exists.
mkdir -p "$MASTER_REF_PATH"

# Get the current execution time for the benchmark
NEW_TIME=$(cat "$HERE/../vsim-polybench-perf-stats.txt" | grep "^$BENCH:" | cut -d' ' -f2)

# Get the master execution time for the benchmark
OLD_TIME=
if [ -f "$MASTER_REF_PATH/$MASTER_REF_FILE" ]; then
  OLD_TIME=$(cat "$MASTER_REF_PATH/$MASTER_REF_FILE" | grep "^$BENCH:" | cut -d' ' -f2)
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
  cp "$HERE/../vsim-polybench-perf-stats.txt" "$MASTER_REF_PATH/$MASTER_REF_FILE"
fi

# Exit with "allow_failure" exit code if has warnings
if [ ! $HAS_WARNINGS -eq 0 ]; then
  exit 4
fi
