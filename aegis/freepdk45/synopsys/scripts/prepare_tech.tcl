# useful shortcuts
alias h   "history"
alias cud "current_design"
alias rad "remove_design -all"

# increase significant digits in report files
set report_default_significant_digits  6

# disable default DE output redirect
set de_log_redirect_enable false

# set target library to FreePDK45
set FREEPDK_DIR "/usr/scratch/sulperg/tbenz/FreePDK45/FreePDK45/osu_soc/lib/files/"
set search_path [concat  $search_path $FREEPDK_DIR]
set alib_library_analysis_path $FREEPDK_DIR
set link_library [set target_library [concat  [list gscl45nm.db] [list dw_foundation.sldb]]]
set synthetic_library [concat  $synthetic_library dw_foundation.sldb]
set target_library "gscl45nm.db"

# define work folder
sh mkdir -p WORK
define_design_lib WORK -path ./WORK

# report latches
set hdlin_check_no_latch true
set hdlin_latch_always_async_set_reset true

# keep names when writing power information (saif)
# set power_preserve_rtl_hier_names true

# verilog / vhdl export config
set vhdlout_dont_write_types true
set vhdlout_write_components false
set verilogout_no_tri true

# name nets consistently
set hdlin_presto_net_name_prefix n

# nicely name test signals
set test_scan_in_port_naming_style "SynopsysScanIn%s%s_ti"
set test_scan_out_port_naming_style "SynopsysScanOut%s%s_to"
set test_scan_enable_port_naming_style "SynopsysScanEn%s_ti"

# create a simple naming scheme for macro cells
set template_naming_style %s_%p
set template_parameter_style %d
set template_separator_style _

# report linking issues
set auto_link_disable true
