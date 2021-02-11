#!/bin/zsh

#################################################
######       PARAMETER DEFINITIONS        #######
#################################################

#progs=(2mm 3mm atax axpy bicg conv2d gemm seq)
#progs=(axpy bicg conv2d seq)
progs=(axpy)
back=(seq)
samples=8
board="root@hero-zcu102-06"
routine="cd ${HERO_TARGET_PATH}; \
         source ./sourceme.sh; \
         ./prepare_board.sh &> /dev/null; \
         renice -n -20 \$$ &> /dev/null"
out="measurements"
mkdir ${out}

#################################################
######        FUNCTION DEFINITIONS        #######
#################################################

# Function to launch CMUX in the background
launch_cmux() {
  cmux_pid=$(ssh ${board} "${routine}; \
      taskset -c 1 ./cmux &> /dev/null & echo \$!")
  echo "CMUX launched with pid ${cmux_pid}"
}

# Function to kill CMUX
kill_cmux() {
   echo "Killing CMUX with pid ${cmux_pid}"
   ssh ${board} "kill ${cmux_pid}"
}

# Function to launch two programs in the background
launch_background() {
#  pid_one=$(ssh ${board} "${routine}; \
#      taskset -c 0 ./$1 &> /dev/null & echo \$!")
  pid_two=$(ssh ${board} "${routine}; \
      taskset -c 2 ./$1 &> /dev/null & echo \$!")
  echo "${bprog} launched with pids ${pid_one} and ${pid_two}"
}

# Function to kill the two background programs
kill_background() {
  echo "Killing ${bprog} with pids ${pid_one} and ${pid_two}"
  ssh ${board} "kill ${pid_one} ${pid_two}"
}

# Function to perform measurements
run_benchmark() {
  echo "Running ${prog} with background ${bprog}"
  ssh ${board} "${routine}; \
      for i in {1..${samples}}; \
      do taskset -c 3 ./${prog}_PREM.elf; \
      done" #>> ${out}/${prog}_${bprog}$1
}


#################################################
######             MAIN SCRIPT            #######
#################################################

# First, PREM without interference
launch_cmux
for prog in ${progs}
do
  run_benchmark "noint.csv"
done

# Second, PREM with non-PREM interference
for bprog in ${back}
do
  launch_background ${bprog}_noise.elf
  for prog in ${progs}
  do
    run_benchmark "_noPREM.csv"
  done
  kill_background
done
kill_cmux

# Third, PREM with PREM interference
for bprog in ${back}
do
  launch_cmux
  launch_background ${bprog}_noise_PREM.elf
  for prog in ${progs}
  do
    run_benchmark "_PREM.csv"
  done
  kill_background
  kill_cmux
done

