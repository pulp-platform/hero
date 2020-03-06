#!/usr/bin/env bash
ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)

set -e

if [ -z "$HERO_INSTALL" ]; then
  echo "Fatal: 'HERO_INSTALL' environment variable is not set!"
  exit 1
fi

SCRIPT_SYMLINKS=1
SDK_PULP=1
TC_PULP=1
BUILD_VP=1
while (( "$#" )); do
  case "$1" in
    --no-tc-pulp)
      TC_PULP=0
      shift 1
      ;;
    --no-script-symlinks)
      SCRIPT_SYMLINKS=0
      shift 1
      ;;
    --no-sdk-pulp)
      SDK_PULP=0
      shift 1
      ;;
    --no-vp)
      BUILD_VP=0
      shift 1
      ;;
    *)
      echo "Error: Unsupported argument '$1'" >&2
      exit 1
      ;;
  esac
done

# Build toolchain
if [ $TC_PULP = 1 ]; then
  make -C "$ROOT" tc-pulp
fi

# Install scripts via symlink
if [ $SCRIPT_SYMLINKS = 1 ]; then
  chmod -R u+w "$HERO_INSTALL/bin"
  ln -sf "$(realpath --relative-to="$HERO_INSTALL/bin/" "$ROOT/example-apps/common/one_word_per_line.py")" "$HERO_INSTALL/bin/"
  ln -sf "$(realpath --relative-to="$HERO_INSTALL/bin/" "$ROOT/hardware/test/gen_slm_files.sh")" "$HERO_INSTALL/bin/"
  chmod -R u-w "$HERO_INSTALL/bin"
fi

# Build PULP SDK.
if [ $SDK_PULP = 1 ]; then
  make -C "$ROOT" sdk-pulp
fi

# Build virtual platform
if [ $BUILD_VP = 1 ]; then
  make -C "$ROOT" virtual-platform
fi
