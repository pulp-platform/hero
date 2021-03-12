# Copyright (c) 2020 ETH Zurich, University of Bologna
# Licensed under the Apache License, Version 2.0.
# SPDX-License-Identifier: Apache-2.0
#
# Authors:
# - Andreas Kurth <akurth@iis.ee.ethz.ch>

if test -z ${HERO_ROOT+x}; then
  readonly HERO_ROOT="$(readlink -f "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")/../..")"
fi

say() {
  echo "$@" >&2
}

defined_or_warning_and_exit() {
  if test -z ${!1+x}; then
    say "Warning: '$1' environment variable not defined.  ${@:2}"
    return 1
  fi
  return 0
}

scpv() {
  say "'$1' -> '${@:2}'"
  scp "$@"
}
