#!/usr/bin/env bash
ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)

set -e

if [ -z "$HERO_INSTALL" ]; then
  echo "Fatal: 'HERO_INSTALL' environment variable is not set!"
  exit 1
fi

make -C "$ROOT" tc-pulp
make -C "$ROOT" tc-har-olinux
make -C "$ROOT" sdk-pulp
make -C "$ROOT" sdk-har
make -C "$ROOT" tc-llvm
make -C "$ROOT" br-har-exilzcu102
