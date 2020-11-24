# useful shortcuts
alias h   "history"
alias cud "current_design"
alias rad "remove_design -all"

# increase significant digits in report files
set report_default_significant_digits  6

# disable default DE output redirect
set de_log_redirect_enable false

# set target library to GF22
set GF22_DIR "/usr/pack/gf-22-kgf/invecas/std/2020.01/"
set DB_LOC "model/timing/db/"

set CORNER "SSG_0P72V_0P00V_0P00V_0P00V_M40C"

set DB_LIBS ""
set ALIB_PATHS ""

lappend DB_LIBS "${GF22_DIR}GF22FDX_SC8T_104CPP_BASE_CSC20L_FDK_RELV06R40/${DB_LOC}GF22FDX_SC8T_104CPP_BASE_CSC20L_${CORNER}.db"
lappend DB_LIBS "${GF22_DIR}GF22FDX_SC8T_104CPP_BASE_CSC20SL_FDK_RELV06R40/${DB_LOC}GF22FDX_SC8T_104CPP_BASE_CSC20SL_${CORNER}.db"
lappend DB_LIBS "${GF22_DIR}GF22FDX_SC8T_104CPP_BASE_CSC24L_FDK_RELV06R40/${DB_LOC}GF22FDX_SC8T_104CPP_BASE_CSC24L_${CORNER}.db"
lappend DB_LIBS "${GF22_DIR}GF22FDX_SC8T_104CPP_BASE_CSC24SL_FDK_RELV06R40/${DB_LOC}GF22FDX_SC8T_104CPP_BASE_CSC24SL_${CORNER}.db"
lappend DB_LIBS "${GF22_DIR}GF22FDX_SC8T_104CPP_BASE_CSC28L_FDK_RELV06R40/${DB_LOC}GF22FDX_SC8T_104CPP_BASE_CSC28L_${CORNER}.db"
lappend DB_LIBS "${GF22_DIR}GF22FDX_SC8T_104CPP_BASE_CSC28SL_FDK_RELV06R40/${DB_LOC}GF22FDX_SC8T_104CPP_BASE_CSC28SL_${CORNER}.db"
lappend DB_LIBS "${GF22_DIR}GF22FDX_SC8T_104CPP_ECO_CSL_FDK_RELV04R30/${DB_LOC}GF22FDX_SC8T_104CPP_ECO_CSL_${CORNER}.db"
lappend DB_LIBS "${GF22_DIR}GF22FDX_SC8T_104CPP_ECO_CSSL_FDK_RELV04R30/${DB_LOC}GF22FDX_SC8T_104CPP_ECO_CSSL_${CORNER}.db"
lappend DB_LIBS "${GF22_DIR}GF22FDX_SC8T_104CPP_HPK_CSL_FDK_RELV03R40/${DB_LOC}GF22FDX_SC8T_104CPP_HPK_CSL_${CORNER}.db"
lappend DB_LIBS "${GF22_DIR}GF22FDX_SC8T_104CPP_HPK_CSSL_FDK_RELV03R40/${DB_LOC}GF22FDX_SC8T_104CPP_HPK_CSSL_${CORNER}.db"
lappend DB_LIBS "${GF22_DIR}GF22FDX_SC8T_104CPP_HPKCUSTOM_CSL_FDK_RELV00R50/${DB_LOC}GF22FDX_SC8T_104CPP_HPKCUSTOM_CSL_${CORNER}.db"
lappend DB_LIBS "${GF22_DIR}GF22FDX_SC8T_104CPP_LPK_CSL_FDK_RELV03R30/${DB_LOC}GF22FDX_SC8T_104CPP_LPK_CSL_${CORNER}.db"
lappend DB_LIBS "${GF22_DIR}GF22FDX_SC8T_104CPP_LPK_CSSL_FDK_RELV03R30/${DB_LOC}GF22FDX_SC8T_104CPP_LPK_CSSL_${CORNER}.db"
#lappend DB_LIBS "${GF22_DIR}GF22FDX_SC8T_104CPP_SHIFT_CSL_FDK_RELV03R40/${DB_LOC}GF22FDX_SC8T_104CPP_SHIFT_CSL_${CORNER}.db"
#lappend DB_LIBS "${GF22_DIR}GF22FDX_SC8T_104CPP_SHIFT_CSSL_FDK_RELV03R40/${DB_LOC}GF22FDX_SC8T_104CPP_SHIFT_CSSL_${CORNER}.db"
#lappend DB_LIBS "${GF22_DIR}GF22FDX_SC8T_104CPP_SHIFTHL_CSL_FDK_RELV01R40/${DB_LOC}GF22FDX_SC8T_104CPP_SHIFTHL_CSL_${CORNER}.db"
#lappend DB_LIBS "${GF22_DIR}GF22FDX_SC8T_104CPP_SHIFTHL_CSSL_FDK_RELV01R40/${DB_LOC}GF22FDX_SC8T_104CPP_SHIFTHL_CSSL_${CORNER}.db"

set link_library [set target_library [concat ${DB_LIBS}  [list dw_foundation.sldb]]]
set alib_library_analysis_path ./alib/
set synthetic_library [concat  $synthetic_library dw_foundation.sldb]
set target_library ${DB_LIBS}

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
