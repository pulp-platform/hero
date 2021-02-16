#!/usr/bin/env bash

set -euo pipefail

readonly HERO_ROOT="$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")"

ARCHIVE="$1"
if ! test -f "$ARCHIVE"; then
  echo 'Fatal: First argument must be an existing archive!'
  exit 1
fi

if [[ "$ARCHIVE" =~ \.gz$ ]]; then
  readonly COMPRESSED=true
  gunzip "$ARCHIVE"
  ARCHIVE="${ARCHIVE%.gz}"
else
  readonly COMPRESSED=false
fi
readonly ARCHIVE

append() {
  tar --append -f "$ARCHIVE" "$@"
}

append --transform 's|petalinux/zcu102/images/linux/||' \
    petalinux/zcu102/images/linux/{BOOT.BIN,image.ub}

append output/br-har-exilzcu102/target/{lib/modules/4.19.0/extra/pulp.ko,usr/lib}

append cmux/bin/cmux

append openmp-examples/baby_gemm/baby_gemm
append openmp-examples/darknet/darknet

if $COMPRESSED; then
  gzip "$ARCHIVE"
fi
