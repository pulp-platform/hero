# extract vsim flags passed by make (need to do this via env vars)
if {[info exists ::env(VSIM_FLAGS)]} {
    quietly set vsimFlagsTcl $::env(VSIM_FLAGS)
} {
    quietly set vsimFlagsTcl ""
}

set StdArithNoWarnings 1
set NumericStdNoWarnings 1
set BreakOnAssertion 2;# break also on assertion errors
