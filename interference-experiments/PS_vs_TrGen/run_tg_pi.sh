#!bin/zsh


# Runname is just a unique name each time the script is started.
RUNNAME=TrafGenDump_$(date +"%Y%m%d-%H%M%S")

# Parameters for TG0
#   Should NOT be prefixed by 0x, that breaks hexadecimal arithmetic of bc
TG0_CMDRAM_READ_BASE=A0018000
TG0_CMDRAM_WRITE_BASE=A0019000
TG1_CMDRAM_READ_BASE=A0048000
TG1_CMDRAM_WRITE_BASE=A0049000
TG2_CMDRAM_READ_BASE=A0078000
TG2_CMDRAM_WRITE_BASE=A0079000
TG3_CMDRAM_READ_BASE=A00A8000
TG3_CMDRAM_WRITE_BASE=A00A9000

TG0_MASTERCONTROL_BASE=A0010000
TG0_ERRORSTATE_BASE=A0010008

TG1_MASTERCONTROL_BASE=A0040000
TG1_ERRORSTATE_BASE=A0040008

TG2_MASTERCONTROL_BASE=A0070000
TG2_ERRORSTATE_BASE=A0070008

TG3_MASTERCONTROL_BASE=A00A0000
TG3_ERRORSTATE_BASE=A00A0008

# Generic parameters to write into memory mapped registers.
#   Should be prefixed by 0x
#GENERIC_MASTERCONTROL_ENABLELOOP=0x20A80000
GENERIC_MASTERCONTROL_ENABLELOOP=0x20B80000
GENERIC_MASTERCONTROL_DISABLELOOP=0x20A00000

GENERIC_CMDRAM_WORD3_LOPRIO=0x30
GENERIC_CMDRAM_WORD3_HIPRIO=0xF0030

# For experiments
EXPERIMENT_SAMPLES=1000
EXPERIMENT_MAX_TRAFGENS=2   # System freezes with more than two.
EXPERIMENT_BENCHMARK_PATH=TODO_ADAPT_ME
EXPERIMENT_BENCHMARKS=(seq.elf rand.elf axpy.elf 2mm.elf 3mm.elf atax.elf bicg.elf conv2d.elf gemm.elf)
EXPERIMENT_QoS_CMDRAM_WORD3S=($GENERIC_CMDRAM_WORD3_LOPRIO $GENERIC_CMDRAM_WORD3_HIPRIO)

run_experiment() {
    local benchmark=$1
    local interferers=$2
    local qos=$3

    RESULT_NAME=${RUNNAME}_${benchmark:t}_${interferers}trafgen_word3qos${qos}
    echo -n "Starting experiment $RESULT_NAME..."
    RESULT_DUMP=${RESULT_NAME}_datadump.txt

    local TOTALTIME=0;
    for i in `seq 1 $EXPERIMENT_SAMPLES`; do
        local TIME=$(chrt -f 20 $benchmark)
        echo $TIME >> $RESULT_DUMP
        TOTALTIME=$(echo "$TOTALTIME + $TIME" | bc)
    done

    echo "Finished in $TOTALTIME."
}

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

    #echo "Would write $WRITEWORD to $THIS_ADDR"
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

# CMDRAM WORD 0
#   0x78000000 address LSB
# CMDRAM WORD 1
#   1  valid
#   000 last_addr
#   0000 reserved
#   000 prot
#   000000 id
#   100 size
#   01 burst
#   0 reserved
#   0 lock
#   11111111 len
# CMDRAM WORD 2
#   0 reserved
#   000000000 depend
#   000000000 other_depend
#   0000000000000 mstram index
# CMDRAM WORD 3
#   000000000000 reserved
#   0000/1111 QoS
#   00000000 user
#   0011 cache
#   0 reserved
#   000 expected response

# Make sure all traffic generators are off.
write_word $TG0_MASTERCONTROL_BASE 0 0 0 $GENERIC_MASTERCONTROL_DISABLELOOP
write_word $TG1_MASTERCONTROL_BASE 0 0 0 $GENERIC_MASTERCONTROL_DISABLELOOP
write_word $TG2_MASTERCONTROL_BASE 0 0 0 $GENERIC_MASTERCONTROL_DISABLELOOP
write_word $TG3_MASTERCONTROL_BASE 0 0 0 $GENERIC_MASTERCONTROL_DISABLELOOP

# Run all benchmarks without interference.
for BENCHMARK in $EXPERIMENT_BENCHMARKS; do
    EXPERIMENT_BENCHMARK=$EXPERIMENT_BENCHMARK_PATH/$BENCHMARK
    run_experiment $EXPERIMENT_BENCHMARK 0 0

    for QOS in $EXPERIMENT_QoS_CMDRAM_WORD3S; do

        # Configure traffic generator 0
        write_word $TG0_CMDRAM_READ_BASE 10 0 0 0x78000000
        write_word $TG0_CMDRAM_READ_BASE 10 0 4 0x800044FF
        write_word $TG0_CMDRAM_READ_BASE 10 0 8 0x00000000
        write_word $TG0_CMDRAM_READ_BASE 10 0 C $QOS

        # Configure traffic generator 1
        write_word $TG1_CMDRAM_READ_BASE 10 0 0 0x78000000
        write_word $TG1_CMDRAM_READ_BASE 10 0 4 0x800044FF
        write_word $TG1_CMDRAM_READ_BASE 10 0 8 0x00000000
        write_word $TG1_CMDRAM_READ_BASE 10 0 C $QOS

        # Configure traffic generator 2
        write_word $TG2_CMDRAM_READ_BASE 10 0 0 0x78000000
        write_word $TG2_CMDRAM_READ_BASE 10 0 4 0x800044FF
        write_word $TG2_CMDRAM_READ_BASE 10 0 8 0x00000000
        write_word $TG2_CMDRAM_READ_BASE 10 0 C $QOS

        # Configure traffic generator 3
        write_word $TG3_CMDRAM_READ_BASE 10 0 0 0x78000000
        write_word $TG3_CMDRAM_READ_BASE 10 0 4 0x800044FF
        write_word $TG3_CMDRAM_READ_BASE 10 0 8 0x00000000
        write_word $TG3_CMDRAM_READ_BASE 10 0 C $QOS

        for NUM_TRAFGENS in `seq 1 $EXPERIMENT_MAX_TRAFGENS`; do

            # Start the correct number of traffic generators
            if [ "$NUM_TRAFGENS" -ge "1" ]; then
                echo "Enabling trafgen 0"
                write_word $TG0_MASTERCONTROL_BASE 0 0 0 $GENERIC_MASTERCONTROL_ENABLELOOP
            fi
            if [ "$NUM_TRAFGENS" -ge "2" ]; then
                echo "Enabling trafgen 1"
                write_word $TG1_MASTERCONTROL_BASE 0 0 0 $GENERIC_MASTERCONTROL_ENABLELOOP
            fi
            if [ "$NUM_TRAFGENS" -ge "3" ]; then
                echo "Enabling trafgen 2"
                write_word $TG2_MASTERCONTROL_BASE 0 0 0 $GENERIC_MASTERCONTROL_ENABLELOOP
            fi
            if [ "$NUM_TRAFGENS" -ge "4" ]; then
                echo "Enabling trafgen 3"
                write_word $TG3_MASTERCONTROL_BASE 0 0 0 $GENERIC_MASTERCONTROL_ENABLELOOP
            fi

            run_experiment $EXPERIMENT_BENCHMARK $NUM_TRAFGENS $QOS

            sleep 1

            # Stop all traffic generators.
            write_word $TG0_MASTERCONTROL_BASE 0 0 0 $GENERIC_MASTERCONTROL_DISABLELOOP
            write_word $TG1_MASTERCONTROL_BASE 0 0 0 $GENERIC_MASTERCONTROL_DISABLELOOP
            write_word $TG2_MASTERCONTROL_BASE 0 0 0 $GENERIC_MASTERCONTROL_DISABLELOOP
            write_word $TG3_MASTERCONTROL_BASE 0 0 0 $GENERIC_MASTERCONTROL_DISABLELOOP

            sleep 1

        done;
    done;
done;
