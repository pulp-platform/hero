vsim -voptargs="+acc" -t 1ps -warning 3009 hero_tb
set StdArithNoWarnings 1
set NumericStdNoWarnings 1

source ../test/hero_tb.wave.do

run -a
