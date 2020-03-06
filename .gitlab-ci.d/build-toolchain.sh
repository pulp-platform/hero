#!/usr/bin/env bash
ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)

# Make sure some variables exist
[[ -z "$HERO_INSTALL" ]]  && echo "HERO_INSTALL not set!"  && exit 1
[[ -z "$DEPLOY_TARGET" ]] && echo "DEPLOY_TARGET not set!" && exit 1
[[ -z "$DEPLOY_REMOTE" ]] && echo "DEPLOY_REMOTE not set!" && exit 1
[[ -z "$DEPLOY_PATH" ]]   && echo "DEPLOY_PATH not set!"   && exit 1

echo "FULL_CI_TEST:  $FULL_CI_TEST"
echo "DEPLOY_TARGET: $DEPLOY_TARGET"
echo "DEPLOY_REMOTE: $DEPLOY_REMOTE"
echo "DEPLOY_PATH:   $DEPLOY_PATH"

# Store the info about the build in a tag
TAG="$HERO_INSTALL/tag"

if [[ -n "$FULL_CI_TEST" ]] || ssh "$DEPLOY_REMOTE" "test ! -x \"$DEPLOY_PATH/bin/riscv32-unknown-elf-gcc\""; then
    # Build the toolchain like it's done in the regular setup
    echo "Build the full toolchain"
    "$ROOT/../setup.sh" --no-sdk-pulp --no-vp
    make -C "$ROOT/../" bender
    # Create a tag just to debug CI
    echo "Create a tag"
    chmod u+w "$HERO_INSTALL"
    echo $(date) > "$TAG"
    echo "Commit: $CI_COMMIT_SHA" >> "$TAG"
    # Copy the built toolchain to a folder per branch to enable fast-path
    echo "Deploy to $DEPLOY_TARGET"
    # Sanity check to not delete everything
    [[ -z "$DEPLOY_TARGET" ]] && echo "DEPLOY_TARGET not set!" && exit 1
    rsync -av --delete-before "$HERO_INSTALL/" "$DEPLOY_TARGET/"
else
    echo "Use fast path to install toolchain (copy prebuilt toolchain)"
    rsync -av "$DEPLOY_TARGET/" "$HERO_INSTALL/"
    echo "Use toolchain from:"
    if [[ -r "$TAG" ]]; then
        cat "$TAG"
    else
        echo "No tag available!"
    fi
fi
