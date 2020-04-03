#!/bin/zsh

# The benchmarks to be executed as "interferers" from the APU.
EXPERIMENT_BENCHMARK_PATH=TODO_ADAPT_ME
EXPERIMENT_BENCHMARKS=(seq_noise.elf rand_noise.elf axpy_noise.elf) # 2mm_noise.elf 3mm_noise.elf atax_noise.elf bicg_noise.elf conv2d_noise.elf gemm_noise.elf)

# We can run the benchmark with the traffic generators at different frequencies.
# This is a list of the frequencies to try.
EXPERIMENT_FREQS=(250000000)

# Runname is just a unique name each time the script is started.
RUNNAME=TrafGenDump_$(date +"%Y%m%d-%H%M%S")

# Parameters for TG0
TG0_CMDRAM_READ_BASE=A0018000
TG0_CMDRAM_WRITE_BASE=A0019000
TG0_MASTERCONTROL_BASE=A0010000
TG0_ERRORSTATE_BASE=A0010008

TG_MASTERCONTROL_RUNNING=0x20B00000
TG_MASTERCONTROL_IDLE=0x20A00000
TG_MASTERCONTROL_LOOP=0x20A80000
TG_MASTERCONTROL_NOLOOP=0x20A00000

# Parameters for IC0
IC0_BASE=A0000000
IC_UNMASK_OFFSET=8
IC_MASTERENABLE_OFFSET=1C
IC_FIREOUTPUTINTERRUPT_OFFSET=0
IC_ACKINTERRUPT_OFFSET=C

# Parameters for PM0
PM0_BASE=A0020000
PM_CLEAR_OFFSET=0
PM_AXI_RD_CNT_OFFSET=2008
PM_AXI_WR_CNT_OFFSET=2000
PM_CLK_LSB_CNT_OFFSET=1000
PM_CLK_MSB_CNT_OFFSET=1008

# Experiment setup
EXPERIMENT_SAMPLES=500

get_addr()
{
    local BASE_ADDR=$1
    local ENTRY_LEN=$2
    local MAJOR_OFF=$3
    local MINOR_OFF=$4

    local THIS_ADDR=0x$(echo "obase=16;ibase=16;$BASE_ADDR + ($ENTRY_LEN * $MAJOR_OFF) + $MINOR_OFF" | bc)
    echo $THIS_ADDR
    return
}

hex_div_to_dec() {
    local TALJ=$(echo "$1" | sed "s/.*0x//")
    local NAMN=$(echo "$2" | sed "s/.*0x//")
    local KVOT=$(echo "obase=10;ibase=16;$TALJ/$NAMN" | bc)
    echo $KVOT
    return
}

echo_state()
{
    echo "TG0 READ CMDRAM line 0"
    echo $(read_word $TG0_CMDRAM_READ_BASE 10 0 0)
    echo $(read_word $TG0_CMDRAM_READ_BASE 10 0 4)
    echo $(read_word $TG0_CMDRAM_READ_BASE 10 0 8)
    echo $(read_word $TG0_CMDRAM_READ_BASE 10 0 C)
    echo "TG0 WRITE CMDRAM line 0"
    echo $(read_word $TG0_CMDRAM_WRITE_BASE 10 0 0)
    echo $(read_word $TG0_CMDRAM_WRITE_BASE 10 0 4)
    echo $(read_word $TG0_CMDRAM_WRITE_BASE 10 0 8)
    echo $(read_word $TG0_CMDRAM_WRITE_BASE 10 0 C)
    echo "Master register"
    echo $(read_word $TG0_MASTERCONTROL_BASE 0 0 0)
    echo "Error state"
    echo $(read_word $TG0_ERRORSTATE_BASE 0 0 0)
}

write_word()
{
    local BASE_ADDR=$1
    local ENTRY_LEN=$2
    local MAJOR_OFF=$3
    local MINOR_OFF=$4
    local WRITEWORD=$5
    local THIS_ADDR=$(get_addr $BASE_ADDR $ENTRY_LEN $MAJOR_OFF $MINOR_OFF)

    devmem $THIS_ADDR 32 $WRITEWORD
}

read_word()
{
    local BASE_ADDR=$1
    local ENTRY_LEN=$2
    local MAJOR_OFF=$3
    local MINOR_OFF=$4
    local THIS_ADDR=$(get_addr $BASE_ADDR $ENTRY_LEN $MAJOR_OFF $MINOR_OFF)

    echo $(devmem $THIS_ADDR 32)
    return
}

run_experiment()
{
    local benchmark=$1
    local freq=$2

    DEPS=(0 1 2 3 4 5 6 7 8 9 C) # Hex
    MINDEPS=0                   # Dec, this is the minimum idx in DEPS to exec
    MAXDEPS=0                   # Dec, this is the maximum idx in DEPS to exec

    # Make sure all traffic generators are off.
    write_word $TG0_MASTERCONTROL_BASE 0 0 0 $TG_MASTERCONTROL_IDLE
    while STATUS=$(read_word $TG0_MASTERCONTROL_BASE 0 0 0) && [ "$STATUS" != "$TG_MASTERCONTROL_IDLE" ]; do
        echo -n "."
        write_word $TG0_MASTERCONTROL_BASE 0 0 0 0x20A00000
        sleep 0.1
        TRIES=$((TRIES+1))
        if [ "$TRIES" -gt 20 ]; then
            write_word $TG0_MASTERCONTROL_BASE 0 0 0 $TG_MASTERCONTROL_IDLE
            echo "Error at experiment start"
            echo "Fail ($STATUS != $TG_MASTERCONTROL_IDLE)..."
            echo "Error $(read_word $TG0_MASTERCONTROL_BASE 0 0 8)"
            exit;
        fi
    done
    echo "Ready to start experiments"

    # Reset the CMDRAM command vector, use MAXDEPS as we want to reset ALL
    for ENTRY in `seq 0 $MAXDEPS`; do
        write_word $TG0_CMDRAM_READ_BASE 10 $ENTRY 0 0x00000000
        write_word $TG0_CMDRAM_READ_BASE 10 $ENTRY 4 0x00000000
        write_word $TG0_CMDRAM_READ_BASE 10 $ENTRY 8 0x00000000
        write_word $TG0_CMDRAM_READ_BASE 10 $ENTRY C 0x00000000
    done

    for MAXDEP in `seq $MINDEPS $MAXDEPS`; do

        # Make sure all traffic generators are off.
        write_word $TG0_MASTERCONTROL_BASE 0 0 0 $TG_MASTERCONTROL_IDLE
        while STATUS=$(read_word $TG0_MASTERCONTROL_BASE 0 0 0) && [ "$STATUS" != "$TG_MASTERCONTROL_IDLE" ]; do
            echo -n "."
            write_word $TG0_MASTERCONTROL_BASE 0 0 0 0x20A00000
            sleep 0.1
            TRIES=$((TRIES+1))
            if [ "$TRIES" -gt 20 ]; then
                write_word $TG0_MASTERCONTROL_BASE 0 0 0 $TG_MASTERCONTROL_IDLE
                echo "Error in MAXDEP loop"
                echo "Fail ($STATUS != $TG_MASTERCONTROL_IDLE)..."
                echo "Error $(read_word $TG0_MASTERCONTROL_BASE 0 0 8)"
                exit;
            fi
        done

        # Uniquely identify experiment
        RESULT_NAME=${RUNNAME}_${benchmark:t}_${freq}Hz_ops=${MAXDEP}_psvspl
        echo -n "Starting experiment $RESULT_NAME..."
        RESULT_DUMP=${RESULT_NAME}_datadump.txt

        # Repopulate CMDRAM command vector
        for DEP in ${DEPS[@]:0:$MAXDEP}; do

            READ_OFFSET=0x$(echo "obase=16;ibase=16;$DEP*1000" | bc)
            READ_ADDR=$(printf "0x%x\n" $((0x78000000 | $READ_OFFSET)))

            # Configure traffic generator
            write_word $TG0_CMDRAM_READ_BASE 10 0 0 $READ_ADDR
            write_word $TG0_CMDRAM_READ_BASE 10 0 4 0x800044FF
            write_word $TG0_CMDRAM_READ_BASE 10 0 8 0x0
            write_word $TG0_CMDRAM_READ_BASE 10 0 C 0x30       # Low prio!

        done

        local TpL_MAX=0
        local ZEROES_READ=0

        # Run experiment
        for i in `seq 1 $EXPERIMENT_SAMPLES`; do

            write_word $TG0_MASTERCONTROL_BASE 0 0 8 0x80000000

            # Ack interrupt
            write_word $IC0_BASE 0 0 $IC_ACKINTERRUPT_OFFSET 1

            # Clear performance monitor
            write_word $PM0_BASE 0 0 $PM_CLEAR_OFFSET 1
            write_word $PM0_BASE 0 0 $PM_CLEAR_OFFSET 0

            # Unmask interrupt
            write_word $IC0_BASE 0 0 $IC_UNMASK_OFFSET 1

            # Sleep for a short while to make sure state has propagated
            sleep 0.1

            # Enable master interrupt
            write_word $IC0_BASE 0 0 $IC_MASTERENABLE_OFFSET 1

            # Trigger master interrupt
            write_word $IC0_BASE 0 0 $IC_FIREOUTPUTINTERRUPT_OFFSET 1

            # Short sleep then measure.
            sleep 0.5

            TRIES=0
            while STATUS=$(read_word $TG0_MASTERCONTROL_BASE 0 0 0) && [ "$STATUS" != "$TG_MASTERCONTROL_IDLE" ]; do
                echo -n "."
                sleep 0.1
                TRIES=$((TRIES+1))
                if [ "$TRIES" -gt 20 ]; then
                    write_word $TG0_MASTERCONTROL_BASE 0 0 0 $TG_MASTERCONTROL_IDLE
                    echo -n "Fail ($STATUS != $TG_MASTERCONTROL_IDLE)..."
                    echo -n "Error $(read_word $TG0_MASTERCONTROL_BASE 0 0 8)"
                    break;
                fi
            done

            # Read the performance monitor counter
            READS=$(read_word $PM0_BASE 0 0 $PM_AXI_RD_CNT_OFFSET)
            TIME_LOW=$(read_word $PM0_BASE 0 0 $PM_CLK_LSB_CNT_OFFSET)
            TIME_HIGH=$(read_word $PM0_BASE 0 0 $PM_CLK_MSB_CNT_OFFSET)
            if [ "$READS" != "0x00000000" ]; then
                TIMEperLOAD=$(hex_div_to_dec $TIME_LOW $READS)
                if [ ! -z "$TIMEperLOAD" ]; then
                    echo $TIMEperLOAD >> $RESULT_DUMP
                    if [ "$TpL_MAX" -lt "$TIMEperLOAD" ]; then
                        TpL_MAX=$TIMEperLOAD
                    fi
                fi
            else
                ZEROES_READ=$(($ZEROES_READ+1))
            fi

        done;

        echo "Finished with $TpL_MAX ($ZEROES_READ)"

    done;

}



for FREQ in $EXPERIMENT_FREQS; do

    echo $FREQ > /sys/class/fclkcfg/fclk0/rate

    run_experiment "none" $FREQ

    for BENCHMARK in $EXPERIMENT_BENCHMARKS; do
        EXPERIMENT_BENCHMARK=$EXPERIMENT_BENCHMARK_PATH/$BENCHMARK

        $EXPERIMENT_BENCHMARK > /dev/null &
        $EXPERIMENT_BENCHMARK > /dev/null &
        $EXPERIMENT_BENCHMARK > /dev/null &
        $EXPERIMENT_BENCHMARK > /dev/null &

        sleep 1

        run_experiment $BENCHMARK $FREQ

        pkill -9 $BENCHMARK
    done;

done;
