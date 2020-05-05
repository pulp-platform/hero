#!/usr/bin/env bash

set -e

error_exit() {
  echo "Error: $1!"
  exit 1
}

assert_not_in_file() {
  local file="$2"
  local pattern="$1"
  test -r "$file" || error_exit "File '$file' is not readable"
  if grep -q "$pattern" "$file"; then
    error_exit "Found '$pattern' in '$file'"
  fi
}

assert_not_in_logfile() {
  assert_not_in_file "$1" "spyglass-1/pulp/Design_Read/spyglass.log"
}

spyglass-2019.06 sg_shell -tcl spyglass.tcl

assert_not_in_logfile 'FATAL'
assert_not_in_logfile 'completed with errors'
