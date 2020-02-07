#!/usr/bin/env bash


if [ -n "$CI" -o -z "$DISPLAY" ]; then
    # Run in console-only mode.
    ./simv
else
    # Run in GUI mode and silence console output.
    ./simv -gui
fi
