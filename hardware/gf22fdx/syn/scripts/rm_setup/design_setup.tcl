set NUM_CORES 8

set IPS_PATH        "../../deps"
set RTL_PATH        "../../src"
set DESIGN_PATH     "../../../"

set reAnalyzeRTL   "TRUE"
set doDFT          "FALSE"
set OUT_FILENAME   "pulp_soc"

set std_cell_path  "/usr/pack/gf-22-kgf/invecas/std/V05R00"
set pwr_cell_path  "/usr/pack/gf-22-kgf/invecas/std/V02R00"
set mem_path1      "/usr/pack/gf-22-kgf/dz/mem/synopsys.dz/2016.03"
set mem_path2      "/usr/pack/gf-22-kgf/dz/mem/synopsys.dz/2016.12"
set io_path        "/usr/pack/gf-22-kgf/invecas/io/V04R40/IN22FDX_GPIO18_10M3S30P_FDK_RELV04R40"

set search_path [ join "$std_cell_path/GF22FDX_SC8T_104CPP_BASE_CSC20L/model/timing/db
                        $std_cell_path/GF22FDX_SC8T_104CPP_BASE_CSC24L/model/timing/db
                        $std_cell_path/GF22FDX_SC8T_104CPP_BASE_CSC28L/model/timing/db
                        $std_cell_path/GF22FDX_SC8T_104CPP_BASE_CSC20SL/model/timing/db
                        $std_cell_path/GF22FDX_SC8T_104CPP_BASE_CSC24SL/model/timing/db
                        $std_cell_path/GF22FDX_SC8T_104CPP_BASE_CSC28SL/model/timing/db
                        $pwr_cell_path/GF22FDX_SC8T_104CPP_HPK_CSL/model/timing/db
                        $io_path/model/timing/db
		        $mem_path1
                        $mem_path2
                        $search_path"]

set CLK_GATE_CELL    "GF22FDX_SC8T_104CPP_BASE_CSC24L_SSG_0P72V_0P00V_0P00V_0P00V_125C/SC8T_CKGPRELATNX4_CSC24L"
set FLL              "$IPS_PATH/gf22_FLL/deliverable"

set ADDITIONAL_TARGET_LIB_FILES "GF22FDX_SC8T_104CPP_BASE_CSC20L_SSG_0P72V_0P00V_0P00V_0P00V_125C.db \
                                 GF22FDX_SC8T_104CPP_BASE_CSC24L_SSG_0P72V_0P00V_0P00V_0P00V_125C.db \
                                 GF22FDX_SC8T_104CPP_BASE_CSC28L_SSG_0P72V_0P00V_0P00V_0P00V_125C.db"

set target_library [concat $target_library $ADDITIONAL_TARGET_LIB_FILES]

set ADDITIONAL_LINK_LIB_FILES     "IN22FDX_R1PH_NFHN_W01024B032M04C256_104cpp_SSG_0P720V_0P000V_0P000V_125C.db \
                                   GF22FDX_SC8T_104CPP_HPK_CSL_SSG_0P72V_0P00V_0P00V_0P00V_125C.db"

set link_library   [concat $target_library $link_library $ADDITIONAL_LINK_LIB_FILES]

set search_path [ join "$IPS_PATH/axi/per2axi
                        $IPS_PATH/axi/axi2per
                        $IPS_PATH/axi/axi2mem
                        $IPS_PATH/axi/axi_node
                        $IPS_PATH/axi/axi/src
                        $IPS_PATH/axi/axi/src
                        $IPS_PATH/apb_periph/apb_i2c
                        $IPS_PATH/mchan/rtl/include
                        $IPS_PATH/cluster_peripherals/include
                        $IPS_PATH/cluster_peripherals/event_unit/include
                        $IPS_PATH/common_cells/include
                        $IPS_PATH/fpu_interco/
                        $IPS_PATH/riscv/rtl/include
                        $IPS_PATH/hwpe-ctrl/rtl
                        $IPS_PATH/hwpe-stream/rtl
                        $IPS_PATH/xne/rtl
                        $FLL/DB
                        $RTL_PATH/include
                        $RTL_PATH/apb/include
                        $search_path"]

define_design_lib work -path ./work

echo $target_library
echo " design_setup has been sourced \n"
