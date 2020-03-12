#!/usr/bin/env bash


if [ -n "$CI" -o -z "$DISPLAY" ]; then
    # Run in console-only mode.
    ./simv | tee vcs.log
    # Error out if simulation had fatals.
    if grep -q '^Fatal:' vcs.log; then
      echo "Simulation had fatal(s)!"
      exit 1
    fi
    # Error out if simulation had failed assertions.
    if grep -q 'started at .* failed at .*$' vcs.log; then
      echo "Simulation had failed assertion(s)!"
      exit 1
    fi
else
    # Run in GUI mode and silence console output.
    ./simv -gui
fi
