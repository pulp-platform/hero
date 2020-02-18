#!/usr/bin/env bash
ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)

set -e

if [ -z "$HERO_INSTALL" ]; then
  echo "Fatal: 'HERO_INSTALL' environment variable is not set!"
  exit 1
fi

make -C "$ROOT" tc-pulp

# Install Bender
make -C "$ROOT/hardware" bender

# Install scripts via symlink
chmod -R u+w "$HERO_INSTALL/bin"
ln -sf "$(realpath --relative-to="$HERO_INSTALL/bin/" "$ROOT/hardware/bender")" "$HERO_INSTALL/bin/"
ln -sf "$(realpath --relative-to="$HERO_INSTALL/bin/" "$ROOT/example-apps/common/one_word_per_line.py")" "$HERO_INSTALL/bin/"
ln -sf "$(realpath --relative-to="$HERO_INSTALL/bin/" "$ROOT/hardware/test/gen_slm_files.sh")" "$HERO_INSTALL/bin/"
chmod -R u-w "$HERO_INSTALL/bin"
