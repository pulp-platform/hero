# 
# go_link.tcl
#
# Copyright (C) 2017 ETH Zurich
# All rights reserved.
# 

#SETUP
sh date
sh echo "Current git version is `git rev-parse --short HEAD`"
source scripts/rm_setup/design_setup.tcl

#SYNTHESIS SCRIPT
source scripts/utils/colors.tcl
source scripts/utils/print_logo.tcl
source scripts/utils/area_report.tcl

suppress_message { VER-130 }
set_host_option -max_core $NUM_CORES

set reAnalyzeRTL "TRUE"

set DESIGN_NAME  "pulp_cluster"

# Set VERILOG defines
set DEFINES "TARGET_SYNTHESIS=1"
set DEFINE "INVECAS=1"

file delete -force -- ./work
source -echo -verbose ./scripts/analyze_auto/ips_add_files.tcl
# set up .v files to use obsolete Verilog 2001 standard (necessary for some idiotic memory cuts)
set hdlin_vrlg_std 2001
source -echo -verbose ./scripts/analyze_auto/rtl_add_files.tcl

elaborate pulp_cluster

current_design pulp_cluster

if { [link] == 0 } {
  exit 1
}
exit 0

