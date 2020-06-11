#!/bin/bash

#################################################
######       PARAMETER DEFINITIONS        #######
#################################################

prog=3mm
cores=(0 1 2 3)

samples=128
out="measurements"

#################################################
######        FUNCTION DEFINITIONS        #######
#################################################

# Function to launch CMUX in the background
launch_cmux() {
  taskset -c ${cmux_core} ./cmux &
  cmux_pid=$!
  echo "CMUX launched with pid ${cmux_pid} \
on core ${cmux_core}"
  sleep 1
}

# Function to kill CMUX
kill_cmux() {
   echo "Killing CMUX with pid ${cmux_pid}"
   kill ${cmux_pid}
}

# Function to perform measurements
run_benchmark() {
  echo "Running ${prog} on core ${prog_core}"
  for (( i=1; i<=${samples}; i++ )); 
  do 
    taskset -c ${proc_core} ./${prog}_PREM.elf \
>> ${out}/${prog}-${prog_core}_proc-${proc_core}_cmux-${cmux_core}
  done
}

#################################################
######             MAIN SCRIPT            #######
#################################################

# Prepare the platform
source ./sourceme.sh
mkdir ${out}
echo 0 > flag

# Test every configuration
for proc_core in ${cores[*]}
do
	echo "Migrating processes to core \
		${proc_core}"
	./prepare_board.sh ${proc_core} &> /dev/null
	renice -n -20 $$
	for cmux_core in ${cores[*]}
	do
		if [ ${cmux_core} != ${proc_core} ]
		then
			launch_cmux ${cmux_core}
			for prog_core in ${cores[*]}
			do
				if [ ${cmux_core} != ${prog_core} ] && [ ${proc_core} != ${prog_core} ]
				then
					run_benchmark
				fi
			done
			kill_cmux
		fi
	done
done

