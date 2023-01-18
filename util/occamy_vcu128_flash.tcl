# Copyright 2020 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51
#
# Nils Wistoff <nwistoff@iis.ee.ethz.ch>
# Noah Huetter <huettern@iis.ee.ethz.ch>
# 
# Programs the SPI Flash of the VCU128 board with with two partitions
# 
# HW_SERVER  host:port URL to the server where the FPGA board is connected to 
# FPGA_ID    Serial of the FPGA to target
# MCS        Output flash configuration file
# OFFSET0    Address offset of partition 0
# FILE0      File to program to partition 0

# Parse arguments
if {$argc < 5} {
    error "usage: occamy_vcu_138_flash.tcl HW_SERVER FPGA_ID MCS OFFSET0 FILE0"
}
set HW_SERVER [lindex $argv 0]
set FPGA_ID   [lindex $argv 1]
set MCS       [lindex $argv 2]
set OFFSET0   [lindex $argv 3]
set FILE0     [lindex $argv 4]
set BIT0      [lindex $argv 5]
# Optional arguments
set BOOTROM0  ""
if {$argc > 6} { set BOOTROM0 [lindex $argv 6] }

set IS_GUI [expr {$rdi::mode == "gui" ? true: false}]
set LTX0 [string map {".bit" ".ltx"} $BIT0]

# Open and connect HW manager
open_hw_manager
connect_hw_server -url ${HW_SERVER}
# Open and connect target
set_property PARAM.FREQUENCY 5000000 [get_hw_targets "*/xilinx_tcf/Xilinx/$FPGA_ID"]
open_hw_target [get_hw_targets "*/xilinx_tcf/Xilinx/$FPGA_ID"]

# Create flash configuration file
write_cfgmem -force -format mcs -size 256 -interface SPIx4 \
    -loaddata "up $OFFSET0 $FILE0" \
    -checksum \
    -file $MCS

# Prepare system bitstream
set_property PROGRAM.FILE $BIT0 [get_hw_devices xcvu37p_0]
set_property PROBES.FILE $LTX0 [get_hw_devices xcvu37p_0]
set_property FULL_PROBES.FILE $LTX0 [get_hw_devices xcvu37p_0]

current_hw_device [get_hw_devices xcvu37p_0]
refresh_hw_device [lindex [get_hw_devices xcvu37p_0] 0]

proc print_vios {} {
    puts "--------------------"
    set vios [get_hw_vios -of_objects [get_hw_devices xcvu37p_0]]
    puts "Done programming device, found [llength $vios] VIOS: "
    foreach vio $vios {
        puts "- $vio : [get_hw_probes * -of_objects $vio]"
    }
    puts "--------------------"
}

proc write_rst {regexp_vio regexp_probe val} {
    puts "\[write_rst $regexp_vio $regexp_probe\]"
    set vio_sys [get_hw_vios -of_objects [get_hw_devices xcvu37p_0] -regexp $regexp_vio]
    set_property OUTPUT_VALUE $val [get_hw_probes -of_objects $vio_sys -regexp $regexp_probe]
    commit_hw_vio [get_hw_probes -of_objects $vio_sys -regexp $regexp_probe]
}

print_vios

write_rst "hw_vio_1" ".*rst.*" 1

set BOOTROM0 "/scratch/cykoenig/development/snitch/hw/system/occamy/fpga/bootrom/bootrom-spl.tcl"

# Write bootrom
if {$BOOTROM0 ne ""} {
  # Wake up peripherals to write bootrom
  write_rst "hw_vio_1" ".*glbl_rst.*" 0
  source $BOOTROM0
} else {
  puts "Not writing bootrom. File does not exist."
}

write_rst "hw_vio_1" ".*rst.*" 0

#if {$rdi::mode eq "batch"} { after 10; }

create_hw_axi_txn -force -verbose -type WRITE -len 1 -address 0x0 -data 0x00000001 txn $axi; run_hw_axi [get_hw_axi_txns txn]; [get_property DATA [get_hw_axi_txns txn]]
create_hw_axi_txn -force -verbose -type READ  -len 1 -address 0x0 rxn $axi; run_hw_axi [get_hw_axi_txns rxn]; [get_property DATA [get_hw_axi_txns rxn]]