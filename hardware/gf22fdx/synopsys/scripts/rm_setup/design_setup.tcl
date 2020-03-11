set NUM_CORES 1

set IPS_PATH        "../../deps"
set RTL_PATH        "../../src"
set DESIGN_PATH     "../../../"

set reAnalyzeRTL   "TRUE"
set doDFT          "FALSE"
set OUT_FILENAME   "pulp"

set SYNDIR_MW "."
set OUTNAME_MW "mem"
exec mkdir -p $SYNDIR_MW/out

set std_cell_path  "/usr/pack/gf-22-kgf/invecas/std/V05R00"
set pwr_cell_path  "/usr/pack/gf-22-kgf/invecas/std/V02R00"
set mem_path1      "/usr/pack/gf-22-kgf/dz/mem/synopsys.dz/2016.03"
set mem_path2      "/usr/pack/gf-22-kgf/dz/mem/synopsys.dz/2016.12"
set mem_path3      "/usr/pack/gf-22-kgf/dz/mem/R1PH/V03R01/synopsys.dz"
set io_path        "/usr/pack/gf-22-kgf/invecas/io/V04R40/IN22FDX_GPIO18_10M3S30P_FDK_RELV04R40"
set tlu_path       "/usr/pack/gf-22-kgf/gf/pdk-22FDX-V1.3_2.2/PlaceRoute/ICC2/TLUPlus"
set tech_mw_path   "/usr/pack/gf-22-kgf/gf/pdk-22FDX-V1.3_2.2/PlaceRoute/ICC2/Techfiles"
set mw_path        "/usr/scratch/fenga4/garofalo/prj/hero_newcache_fixigor/hardware/gf22fdx/synopsys/milkyway/"

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
                        $mem_path3
                        $search_path"]

set CLK_GATE_CELL    "GF22FDX_SC8T_104CPP_BASE_CSC24L_SSG_0P72V_0P00V_0P00V_0P00V_125C/SC8T_CKGPRELATNX4_CSC24L"
set FLL              "$IPS_PATH/gf22_FLL/deliverable"

set ADDITIONAL_TARGET_LIB_FILES "GF22FDX_SC8T_104CPP_BASE_CSC20L_SSG_0P72V_0P00V_0P00V_0P00V_125C.db \
                                 GF22FDX_SC8T_104CPP_BASE_CSC24L_SSG_0P72V_0P00V_0P00V_0P00V_125C.db \
                                 GF22FDX_SC8T_104CPP_BASE_CSC28L_SSG_0P72V_0P00V_0P00V_0P00V_125C.db"

set target_library [concat $target_library $ADDITIONAL_TARGET_LIB_FILES]

set ADDITIONAL_LINK_LIB_FILES     "IN22FDX_R1PH_NFHN_W01024B032M04C256_104cpp_SSG_0P720V_0P000V_0P000V_125C.db \
                                   IN22FDX_R1PH_NFHN_W00032B128M02C256_104cpp_FFG_0P880V_0P450V_M0P450V_125C.db \
                                   IN22FDX_R1PH_NFHN_W00064B128M02C256_104cpp_FFG_0P880V_0P450V_M0P450V_125C.db \
                                   GF22FDX_SC8T_104CPP_HPK_CSL_SSG_0P72V_0P00V_0P00V_0P00V_125C.db"

set link_library   [concat $target_library $link_library $ADDITIONAL_LINK_LIB_FILES]

lappend search_path [file normalize $SYNDIR_MW]
if {[shell_is_in_topographical_mode]} {
      echo " topographical mode \n"
    create_mw_lib $SYNDIR_MW/out/${OUTNAME_MW}_mwlib -technology $tech_mw_path/10M_2Mx_6Cx_2Ix_LB/22FDSOI_10M_2Mx_6Cx_2Ix_LB_104cpp_8t_mw.tf   \
        -mw_reference_library [list $std_cell_path/GF22FDX_SC8T_104CPP_BASE_CSC20L/milkyway/10M_2Mx_6Cx_2Ix_LB/GF22FDX_SC8T_104CPP_BASE_CSC20L    \
                                    $std_cell_path/GF22FDX_SC8T_104CPP_BASE_CSC20SL/milkyway/10M_2Mx_6Cx_2Ix_LB/GF22FDX_SC8T_104CPP_BASE_CSC20SL   \
                                    $std_cell_path/GF22FDX_SC8T_104CPP_BASE_CSC24L/milkyway/10M_2Mx_6Cx_2Ix_LB/GF22FDX_SC8T_104CPP_BASE_CSC24L    \
                                    $std_cell_path/GF22FDX_SC8T_104CPP_BASE_CSC24SL/milkyway/10M_2Mx_6Cx_2Ix_LB/GF22FDX_SC8T_104CPP_BASE_CSC24SL   \
                                    $std_cell_path/GF22FDX_SC8T_104CPP_BASE_CSC28L/milkyway/10M_2Mx_6Cx_2Ix_LB/GF22FDX_SC8T_104CPP_BASE_CSC28L    \
                                    $std_cell_path/GF22FDX_SC8T_104CPP_BASE_CSC28SL/milkyway/10M_2Mx_6Cx_2Ix_LB/GF22FDX_SC8T_104CPP_BASE_CSC28SL   \
                                    $mw_path/IN22FDX_R1PH_NFHN_W01024B032M04C256.lef]

    open_mw_lib $SYNDIR_MW/out/${OUTNAME_MW}_mwlib
}

set search_path [ join "$IPS_PATH/axi/per2axi
                        $IPS_PATH/axi/axi2per
                        $IPS_PATH/axi/axi2mem
                        $IPS_PATH/axi/axi_node
                        $IPS_PATH/axi/axi/src
                        $IPS_PATH/axi/include
                        $IPS_PATH/apb_periph/apb_i2c
                        $IPS_PATH/mchan/rtl/include
                        $IPS_PATH/cluster_peripherals/include
                        $IPS_PATH/cluster_peripherals/event_unit/include
                        $IPS_PATH/riscv/rtl/include
                        $IPS_PATH/common_cells/include
                        $IPS_PATH/fpu_interco/
                        $IPS_PATH/pulp_cluster/packages
                        $IPS_PATH/hwpe-ctrl/rtl
                        $IPS_PATH/hwpe-stream/rtl
                        $IPS_PATH/xne/rtl
                        $IPS_PATH/pulp_cluster/packages
                        $FLL/DB
                        $RTL_PATH/include
                        $RTL_PATH/apb/include
 			$RTL_PATH
                        $search_path"]




define_design_lib work -path ./work

echo $target_library
echo " design_setup has been sourced \n"
