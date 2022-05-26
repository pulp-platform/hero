#!/usr/bin/env bash

# Copyright (c) 2020 ETH Zurich, University of Bologna
# SPDX-License-Identifier: Apache-2.0
# Author: Andreas Kurth
#
# Update the `hero` branch of the `llvm-project` subrepository, but only in a CI/CD job running on
# `master`.

if test -z "$CI"; then
  echo "Error: This script is intended to be run in a CI/CD job!"
  exit 1
fi

if test "$DOWNSTREAM" != "false"; then
  echo "Aborting because a downstream pipeline must not update the branch."
  exit 0
fi

exitcode=0
if test "$CI_COMMIT_BRANCH" = "master"; then
  # Initialize SSH agent and add deployment key.
  eval $(ssh-agent -s)
  echo "$SSH_PRIVATE_KEY" | base64 -d | ssh-add -
  # Push current commit of `llvm-project` to the `hero` branch.
  if cd toolchain/llvm-project; then
    if git checkout -B hero; then
      readonly remote_url="$(git remote get-url --push origin)"
      if echo "$remote_url" | grep -q '^https://'; then
        readonly new_remote_url="$(echo "$remote_url" \
            | sed -e 's/https:\/\//git@/' \
            | sed -e 's/\//:/')"
        echo "Changing remote URL from '$remote_url' to '$new_remote_url' to enable push access."
        git remote set-url origin "$new_remote_url"
      fi
      if git push origin hero; then
        echo "Updated the 'hero' branch of 'llvm-project' to '$(git rev-parse HEAD)'."
      else
        echo "Error: Failed to push to remote!"
        exitcode=1
      fi
    else
      echo "Error: Failed to update local 'hero' branch!"
      exitcode=1
    fi
  else
    echo "Error: Failed to change directory to LLVM!"
    exitcode=1
  fi
  # Terminate SSH agent.
  kill $SSH_AGENT_PID
fi

exit $exitcode
