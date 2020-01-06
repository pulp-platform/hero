#!/usr/bin/env bash

set -e

if [ -z "$HERO_INSTALL" ]; then
  echo "Fatal: 'HERO_INSTALL' environment variable is not set!"
  exit 1
fi

make tc-pulp
make pulp-sdk
