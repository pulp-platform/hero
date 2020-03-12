#SETUP
sh date
sh echo "Current git version is `git rev-parse --short HEAD`"
sh rm -rf alib

source scripts/rm_setup/design_setup.tcl

#SYNTHESIS SCRIPT
source scripts/utils/colors.tcl
source scripts/utils/print_logo.tcl
source scripts/utils/area_report.tcl

# ENVIRONMET SETUP
#Create Folders
#source scripts/utils/create_folder.tcl

suppress_message { VER-130 }
set_host_option -max_core $NUM_CORES

#When set to true, this variable enables advanced analysis through transparent latches during timing updates and reporting. When set to false (the default), this variable disables advanced analysis and reporting through transparent latches.
set timing_enable_through_paths true

# This valiable replaces -timing_high_effort_script option in compile ultra which is ignored.
set compile_timing_high_effort true

set reAnalyzeRTL "TRUE"

set DESIGN_NAME  "pulp"

# Set VERILOG defines
set DEFINE "SYNTHESIS=1"
set DEFINE "INVECAS=1"

sh mkdir -p unmapped

# Operating conditions
set TEMP 125C
set VBN 0P00
set VBP 0P00


# ANALIZE THE RTL CODE or Read the GTECH
if { $reAnalyzeRTL == "TRUE" } {
    file delete -force -- ./work
    source -echo -verbose ./scripts/analyze_auto/ips_add_files.tcl
    source -echo -verbose ./scripts/analyze_auto/rtl_add_files.tcl
    elaborate pulp

    write -format verilog -hier -o ./unmapped/pulp_unmapped.v
    write -format ddc -hier -o ./unmapped/pulp_unmapped.ddc pulp
} else {
     read_file  -format ddc  ./unmapped/pulp_unmapped.ddc
}

current_design pulp
link
