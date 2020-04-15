if [ -n "$CI" -o -z "$DISPLAY" ]; then
    # Run in console-only mode.
    vsim-10.7b -c -do "source $SIMSCRIPT; quit -code \$quitCode"
else
    # Run in GUI mode
    # Don't silence stdout because there might be useful stdout from dpi libraries
    vsim-10.7b -do "source $SIMSCRIPT"
fi
