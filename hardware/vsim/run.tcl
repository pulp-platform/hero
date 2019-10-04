vsim -voptargs="+acc" -t 1ps -warning 3009 hero_tb
set StdArithNoWarnings 1
set NumericStdNoWarnings 1

source ../test/hero_tb.wave.do

onfinish stop
run -a

# Set `quitCode` variable (to be used for the exit code) to `1` if the simulation terminated in an
# unknown state (e.g., due to a `$fatal`) and to `0` otherwise.
quietly set quitCode [expr [string match "*unknown" [runStatus -full]] ? 1 : 0]
