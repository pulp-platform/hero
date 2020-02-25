#################################################################
## INITIALIZATION
#################################################################

## Three delay calculation corners are defined here typical, best, worst
## the long command parses the

create_library_set -name lib_ffg_M40C \
                   -timing [ list \
    ../technology/lib/GF22FDX_SC8T_104CPP_BASE_CSC20L_FFG_0P88V_0P00V_0P00V_0P00V_M40C.lib.gz \
    ../technology/lib/GF22FDX_SC8T_104CPP_BASE_CSC24L_FFG_0P88V_0P00V_0P00V_0P00V_M40C.lib.gz \
    ../technology/lib/GF22FDX_SC8T_104CPP_BASE_CSC28L_FFG_0P88V_0P00V_0P00V_0P00V_M40C.lib.gz \
    ../technology/lib/GF22FDX_SC8T_104CPP_HPK_CSL_FFG_0P88V_0P00V_0P00V_0P00V_M40C.lib \
    ../technology/lib/IN22FDX_S1D_NFRG_W04096B032M04C128_104cpp_FFG_0P880V_0P880V_0P000V_0P000V_M40C.lib \
    ../technology/lib/IN22FDX_S1D_NFRG_W02048B032M04C128_104cpp_FFG_0P880V_0P880V_0P000V_0P000V_M40C.lib \
    ../technology/lib/IN22FDX_R1PH_NFHN_W01024B032M04C256_104cpp_FFG_0P880V_0P000V_0P000V_M40C.lib \
			    ] -aocv [ list \
    ../technology/aocv/GF22FDX_SC8T_104CPP_BASE_CSC20L_FFG_0P88V_0P00V_0P00V_0P00V_M40C.aocv \
    ../technology/aocv/GF22FDX_SC8T_104CPP_BASE_CSC24L_FFG_0P88V_0P00V_0P00V_0P00V_M40C.aocv \
    ../technology/aocv/GF22FDX_SC8T_104CPP_BASE_CSC28L_FFG_0P88V_0P00V_0P00V_0P00V_M40C.aocv \
    /usr/pack/gf-22-kgf/dz/mem/model/timing/aocv/IN22FDX_S1D_NFRG_W04096B032M04C128_104cpp_FFG_0P880V_0P880V_0P000V_0P000V_M40C.aocv \
    /usr/pack/gf-22-kgf/dz/mem/model/timing/aocv/IN22FDX_S1D_NFRG_W02048B032M04C128_104cpp_FFG_0P880V_0P880V_0P000V_0P000V_M40C.aocv \
    /usr/pack/gf-22-kgf/dz/mem/model/timing/aocv/IN22FDX_R1PH_NFHN_W01024B032M04C256_104cpp_FFG_0P880V_0P000V_0P000V_M40C.aocv \
				     ]

create_library_set -name lib_ffg_125C \
                   -timing [ list \
    ../technology/lib/GF22FDX_SC8T_104CPP_BASE_CSC20L_FFG_0P88V_0P00V_0P00V_0P00V_125C.lib.gz \
    ../technology/lib/GF22FDX_SC8T_104CPP_BASE_CSC24L_FFG_0P88V_0P00V_0P00V_0P00V_125C.lib.gz \
    ../technology/lib/GF22FDX_SC8T_104CPP_BASE_CSC28L_FFG_0P88V_0P00V_0P00V_0P00V_125C.lib.gz \
    ../technology/lib/GF22FDX_SC8T_104CPP_HPK_CSL_FFG_0P88V_0P00V_0P00V_0P00V_125C.lib \
    ../technology/lib/IN22FDX_S1D_NFRG_W04096B032M04C128_104cpp_FFG_0P880V_0P880V_0P000V_0P000V_125C.lib \
    ../technology/lib/IN22FDX_S1D_NFRG_W02048B032M04C128_104cpp_FFG_0P880V_0P880V_0P000V_0P000V_125C.lib \
    ../technology/lib/IN22FDX_R1PH_NFHN_W01024B032M04C256_104cpp_FFG_0P880V_0P000V_0P000V_125C.lib \
			    ] -aocv [ list \
    ../technology/aocv/GF22FDX_SC8T_104CPP_BASE_CSC20L_FFG_0P88V_0P00V_0P00V_0P00V_125C.aocv \
    ../technology/aocv/GF22FDX_SC8T_104CPP_BASE_CSC24L_FFG_0P88V_0P00V_0P00V_0P00V_125C.aocv \
    ../technology/aocv/GF22FDX_SC8T_104CPP_BASE_CSC28L_FFG_0P88V_0P00V_0P00V_0P00V_125C.aocv \
    /usr/pack/gf-22-kgf/dz/mem/model/timing/aocv/IN22FDX_S1D_NFRG_W04096B032M04C128_104cpp_FFG_0P880V_0P880V_0P000V_0P000V_125C.aocv \
    /usr/pack/gf-22-kgf/dz/mem/model/timing/aocv/IN22FDX_S1D_NFRG_W02048B032M04C128_104cpp_FFG_0P880V_0P880V_0P000V_0P000V_125C.aocv \
    /usr/pack/gf-22-kgf/dz/mem/model/timing/aocv/IN22FDX_R1PH_NFHN_W01024B032M04C256_104cpp_FFG_0P880V_0P000V_0P000V_125C.aocv \   
                        ]

create_library_set -name lib_ssg_M40C \
                   -timing [ list \
    ../technology/lib/GF22FDX_SC8T_104CPP_BASE_CSC20L_SSG_0P72V_0P00V_0P00V_0P00V_M40C.lib.gz \
    ../technology/lib/GF22FDX_SC8T_104CPP_BASE_CSC24L_SSG_0P72V_0P00V_0P00V_0P00V_M40C.lib.gz \
    ../technology/lib/GF22FDX_SC8T_104CPP_BASE_CSC28L_SSG_0P72V_0P00V_0P00V_0P00V_M40C.lib.gz \
    ../technology/lib/GF22FDX_SC8T_104CPP_HPK_CSL_SSG_0P72V_0P00V_0P00V_0P00V_M40C.lib \
    ../technology/lib/IN22FDX_S1D_NFRG_W04096B032M04C128_104cpp_SSG_0P720V_0P720V_0P000V_0P000V_M40C.lib \
    ../technology/lib/IN22FDX_S1D_NFRG_W02048B032M04C128_104cpp_SSG_0P720V_0P720V_0P000V_0P000V_M40C.lib \
    ../technology/lib/IN22FDX_R1PH_NFHN_W01024B032M04C256_104cpp_SSG_0P720V_0P000V_0P000V_M40C.lib \	 
                         ] -aocv [ list \
    ../technology/aocv/GF22FDX_SC8T_104CPP_BASE_CSC20L_SSG_0P72V_0P00V_0P00V_0P00V_M40C.aocv \
    ../technology/aocv/GF22FDX_SC8T_104CPP_BASE_CSC24L_SSG_0P72V_0P00V_0P00V_0P00V_M40C.aocv \
    ../technology/aocv/GF22FDX_SC8T_104CPP_BASE_CSC28L_SSG_0P72V_0P00V_0P00V_0P00V_M40C.aocv \
    /usr/pack/gf-22-kgf/dz/mem/model/timing/aocv/IN22FDX_S1D_NFRG_W04096B032M04C128_104cpp_SSG_0P720V_0P720V_0P000V_0P000V_M40C.aocv \
    /usr/pack/gf-22-kgf/dz/mem/model/timing/aocv/IN22FDX_S1D_NFRG_W02048B032M04C128_104cpp_SSG_0P720V_0P720V_0P000V_0P000V_M40C.aocv \
    /usr/pack/gf-22-kgf/dz/mem/model/timing/aocv/IN22FDX_R1PH_NFHN_W01024B032M04C256_104cpp_SSG_0P720V_0P000V_0P000V_M40C.aocv \   
                        ]

create_library_set -name lib_ssg_125C \
                   -timing [ list \
    ../technology/lib/GF22FDX_SC8T_104CPP_BASE_CSC20L_SSG_0P72V_0P00V_0P00V_0P00V_125C.lib.gz \
    ../technology/lib/GF22FDX_SC8T_104CPP_BASE_CSC24L_SSG_0P72V_0P00V_0P00V_0P00V_125C.lib.gz \
    ../technology/lib/GF22FDX_SC8T_104CPP_BASE_CSC28L_SSG_0P72V_0P00V_0P00V_0P00V_125C.lib.gz \
    ../technology/lib/GF22FDX_SC8T_104CPP_HPK_CSL_SSG_0P72V_0P00V_0P00V_0P00V_125C.lib \
    ../technology/lib/IN22FDX_S1D_NFRG_W04096B032M04C128_104cpp_SSG_0P720V_0P720V_0P000V_0P000V_125C.lib \
    ../technology/lib/IN22FDX_S1D_NFRG_W02048B032M04C128_104cpp_SSG_0P720V_0P720V_0P000V_0P000V_125C.lib \
    ../technology/lib/IN22FDX_R1PH_NFHN_W01024B032M04C256_104cpp_SSG_0P720V_0P000V_0P000V_125C.lib \
		  ] -aocv [ list \
    ../technology/aocv/GF22FDX_SC8T_104CPP_BASE_CSC20L_SSG_0P72V_0P00V_0P00V_0P00V_125C.aocv \
    ../technology/aocv/GF22FDX_SC8T_104CPP_BASE_CSC24L_SSG_0P72V_0P00V_0P00V_0P00V_125C.aocv \
    ../technology/aocv/GF22FDX_SC8T_104CPP_BASE_CSC28L_SSG_0P72V_0P00V_0P00V_0P00V_125C.aocv \
    /usr/pack/gf-22-kgf/dz/mem/model/timing/aocv/IN22FDX_S1D_NFRG_W04096B032M04C128_104cpp_SSG_0P720V_0P720V_0P000V_0P000V_125C.aocv \
    /usr/pack/gf-22-kgf/dz/mem/model/timing/aocv/IN22FDX_S1D_NFRG_W02048B032M04C128_104cpp_SSG_0P720V_0P720V_0P000V_0P000V_125C.aocv \
    /usr/pack/gf-22-kgf/dz/mem/model/timing/aocv/IN22FDX_R1PH_NFHN_W01024B032M04C256_104cpp_SSG_0P720V_0P000V_0P000V_125C.aocv \   
                        ]


create_library_set -name lib_tt_025C \
                   -timing [ list \
    ../technology/lib/GF22FDX_SC8T_104CPP_BASE_CSC20L_TT_0P80V_0P00V_0P00V_0P00V_25C.lib.gz \
    ../technology/lib/GF22FDX_SC8T_104CPP_BASE_CSC24L_TT_0P80V_0P00V_0P00V_0P00V_25C.lib.gz \
    ../technology/lib/GF22FDX_SC8T_104CPP_BASE_CSC28L_TT_0P80V_0P00V_0P00V_0P00V_25C.lib.gz \
    ../technology/lib/GF22FDX_SC8T_104CPP_HPK_CSL_TT_0P80V_0P00V_0P00V_0P00V_25C.lib \
    ../technology/lib/IN22FDX_S1D_NFRG_W04096B032M04C128_104cpp_TT_0P800V_0P800V_0P000V_0P000V_025C.lib \
    ../technology/lib/IN22FDX_S1D_NFRG_W02048B032M04C128_104cpp_TT_0P800V_0P800V_0P000V_0P000V_025C.lib \
    ../technology/lib/IN22FDX_R1PH_NFHN_W01024B032M04C256_104cpp_TT_0P800V_0P000V_0P000V_025C.lib \	 
                         ] -aocv [ list \
    ../technology/aocv/GF22FDX_SC8T_104CPP_BASE_CSC20L_TT_0P80V_0P00V_0P00V_0P00V_25C.aocv \
    ../technology/aocv/GF22FDX_SC8T_104CPP_BASE_CSC24L_TT_0P80V_0P00V_0P00V_0P00V_25C.aocv \
    ../technology/aocv/GF22FDX_SC8T_104CPP_BASE_CSC28L_TT_0P80V_0P00V_0P00V_0P00V_25C.aocv \
    /usr/pack/gf-22-kgf/dz/mem/model/timing/aocv/IN22FDX_S1D_NFRG_W04096B032M04C128_104cpp_TT_0P800V_0P800V_0P000V_0P000V_025C.aocv \
    /usr/pack/gf-22-kgf/dz/mem/model/timing/aocv/IN22FDX_S1D_NFRG_W02048B032M04C128_104cpp_TT_0P800V_0P800V_0P000V_0P000V_025C.aocv \
    /usr/pack/gf-22-kgf/dz/mem/model/timing/aocv/IN22FDX_R1PH_NFHN_W01024B032M04C256_104cpp_TT_0P800V_0P000V_0P000V_025C.aocv \   
                        ]

# RC corners
create_rc_corner -name rccCmaxDP_125C  -T 125 -qx_tech_file ../technology/qrc/qrcTechFile_FuncCmaxDP
create_rc_corner -name rccCminDP_125C  -T 125 -qx_tech_file ../technology/qrc/qrcTechFile_FuncCminDP
create_rc_corner -name rccRCmaxDP_125C -T 125 -qx_tech_file ../technology/qrc/qrcTechFile_FuncRCmaxDP
create_rc_corner -name rccRCminDP_125C -T 125 -qx_tech_file ../technology/qrc/qrcTechFile_FuncRCminDP

create_rc_corner -name rccCmaxDP_M40C  -T -40 -qx_tech_file ../technology/qrc/qrcTechFile_FuncCmaxDP
create_rc_corner -name rccCminDP_M40C  -T -40 -qx_tech_file ../technology/qrc/qrcTechFile_FuncCminDP
create_rc_corner -name rccRCmaxDP_M40C -T -40 -qx_tech_file ../technology/qrc/qrcTechFile_FuncRCmaxDP
create_rc_corner -name rccRCminDP_M40C -T -40 -qx_tech_file ../technology/qrc/qrcTechFile_FuncRCminDP

create_rc_corner -name rccnominal_025C -T  25 -qx_tech_file ../technology/qrc/qrcTechFile_nominal

## 16 delay corners are defined here

create_delay_corner -name delay_ffg_M40C_Cmax   -library_set lib_ffg_M40C -rc_corner rccCmaxDP_M40C
create_delay_corner -name delay_ffg_M40C_Cmin   -library_set lib_ffg_M40C -rc_corner rccCminDP_M40C
create_delay_corner -name delay_ffg_M40C_RCmax  -library_set lib_ffg_M40C -rc_corner rccRCmaxDP_M40C
create_delay_corner -name delay_ffg_M40C_RCmin  -library_set lib_ffg_M40C -rc_corner rccRCminDP_M40C

create_delay_corner -name delay_ffg_125C_Cmax   -library_set lib_ffg_125C -rc_corner rccCmaxDP_125C
create_delay_corner -name delay_ffg_125C_Cmin   -library_set lib_ffg_125C -rc_corner rccCminDP_125C
create_delay_corner -name delay_ffg_125C_RCmax  -library_set lib_ffg_125C -rc_corner rccRCmaxDP_125C
create_delay_corner -name delay_ffg_125C_RCmin  -library_set lib_ffg_125C -rc_corner rccRCminDP_125C

create_delay_corner -name delay_ssg_M40C_Cmax   -library_set lib_ssg_M40C -rc_corner rccCmaxDP_M40C
create_delay_corner -name delay_ssg_M40C_Cmin   -library_set lib_ssg_M40C -rc_corner rccCminDP_M40C
create_delay_corner -name delay_ssg_M40C_RCmax  -library_set lib_ssg_M40C -rc_corner rccRCmaxDP_M40C
create_delay_corner -name delay_ssg_M40C_RCmin  -library_set lib_ssg_M40C -rc_corner rccRCminDP_M40C

create_delay_corner -name delay_ssg_125C_Cmax   -library_set lib_ssg_125C -rc_corner rccCmaxDP_125C
create_delay_corner -name delay_ssg_125C_Cmin   -library_set lib_ssg_125C -rc_corner rccCminDP_125C
create_delay_corner -name delay_ssg_125C_RCmax  -library_set lib_ssg_125C -rc_corner rccRCmaxDP_125C
create_delay_corner -name delay_ssg_125C_RCmin  -library_set lib_ssg_125C -rc_corner rccRCminDP_125C

create_delay_corner -name delay_tt_025C_Nom    -library_set lib_tt_025C -rc_corner rccnominal_025C

#Explicit Power Domain

update_delay_corner -name delay_ffg_M40C_Cmax   -library_set lib_ffg_M40C -rc_corner rccCmaxDP_M40C   -power_domain PD_core
update_delay_corner -name delay_ffg_M40C_Cmin   -library_set lib_ffg_M40C -rc_corner rccCminDP_M40C   -power_domain PD_core
update_delay_corner -name delay_ffg_M40C_RCmax  -library_set lib_ffg_M40C -rc_corner rccRCmaxDP_M40C  -power_domain PD_core
update_delay_corner -name delay_ffg_M40C_RCmin  -library_set lib_ffg_M40C -rc_corner rccRCminDP_M40C  -power_domain PD_core

update_delay_corner -name delay_ffg_125C_Cmax   -library_set lib_ffg_125C -rc_corner rccCmaxDP_125C   -power_domain PD_core
update_delay_corner -name delay_ffg_125C_Cmin   -library_set lib_ffg_125C -rc_corner rccCminDP_125C   -power_domain PD_core
update_delay_corner -name delay_ffg_125C_RCmax  -library_set lib_ffg_125C -rc_corner rccRCmaxDP_125C  -power_domain PD_core
update_delay_corner -name delay_ffg_125C_RCmin  -library_set lib_ffg_125C -rc_corner rccRCminDP_125C  -power_domain PD_core

update_delay_corner -name delay_ssg_M40C_Cmax   -library_set lib_ssg_M40C -rc_corner rccCmaxDP_M40C   -power_domain PD_core
update_delay_corner -name delay_ssg_M40C_Cmin   -library_set lib_ssg_M40C -rc_corner rccCminDP_M40C   -power_domain PD_core
update_delay_corner -name delay_ssg_M40C_RCmax  -library_set lib_ssg_M40C -rc_corner rccRCmaxDP_M40C  -power_domain PD_core
update_delay_corner -name delay_ssg_M40C_RCmin  -library_set lib_ssg_M40C -rc_corner rccRCminDP_M40C  -power_domain PD_core

update_delay_corner -name delay_ssg_125C_Cmax   -library_set lib_ssg_125C -rc_corner rccCmaxDP_125C   -power_domain PD_core
update_delay_corner -name delay_ssg_125C_Cmin   -library_set lib_ssg_125C -rc_corner rccCminDP_125C   -power_domain PD_core
update_delay_corner -name delay_ssg_125C_RCmax  -library_set lib_ssg_125C -rc_corner rccRCmaxDP_125C  -power_domain PD_core
update_delay_corner -name delay_ssg_125C_RCmin  -library_set lib_ssg_125C -rc_corner rccRCminDP_125C  -power_domain PD_core

update_delay_corner -name delay_tt_025C_Nom     -library_set lib_tt_025C  -rc_corner rccnominal_025C  -power_domain PD_core

update_delay_corner -name delay_ffg_M40C_Cmax   -library_set lib_ffg_M40C -rc_corner rccCmaxDP_M40C   -power_domain PD_memarray
update_delay_corner -name delay_ffg_M40C_Cmin   -library_set lib_ffg_M40C -rc_corner rccCminDP_M40C   -power_domain PD_memarray
update_delay_corner -name delay_ffg_M40C_RCmax  -library_set lib_ffg_M40C -rc_corner rccRCmaxDP_M40C  -power_domain PD_memarray
update_delay_corner -name delay_ffg_M40C_RCmin  -library_set lib_ffg_M40C -rc_corner rccRCminDP_M40C  -power_domain PD_memarray

update_delay_corner -name delay_ffg_125C_Cmax   -library_set lib_ffg_125C -rc_corner rccCmaxDP_125C   -power_domain PD_memarray
update_delay_corner -name delay_ffg_125C_Cmin   -library_set lib_ffg_125C -rc_corner rccCminDP_125C   -power_domain PD_memarray
update_delay_corner -name delay_ffg_125C_RCmax  -library_set lib_ffg_125C -rc_corner rccRCmaxDP_125C  -power_domain PD_memarray
update_delay_corner -name delay_ffg_125C_RCmin  -library_set lib_ffg_125C -rc_corner rccRCminDP_125C  -power_domain PD_memarray

update_delay_corner -name delay_ssg_M40C_Cmax   -library_set lib_ssg_M40C -rc_corner rccCmaxDP_M40C   -power_domain PD_memarray
update_delay_corner -name delay_ssg_M40C_Cmin   -library_set lib_ssg_M40C -rc_corner rccCminDP_M40C   -power_domain PD_memarray
update_delay_corner -name delay_ssg_M40C_RCmax  -library_set lib_ssg_M40C -rc_corner rccRCmaxDP_M40C  -power_domain PD_memarray
update_delay_corner -name delay_ssg_M40C_RCmin  -library_set lib_ssg_M40C -rc_corner rccRCminDP_M40C  -power_domain PD_memarray

update_delay_corner -name delay_ssg_125C_Cmax   -library_set lib_ssg_125C -rc_corner rccCmaxDP_125C   -power_domain PD_memarray
update_delay_corner -name delay_ssg_125C_Cmin   -library_set lib_ssg_125C -rc_corner rccCminDP_125C   -power_domain PD_memarray
update_delay_corner -name delay_ssg_125C_RCmax  -library_set lib_ssg_125C -rc_corner rccRCmaxDP_125C  -power_domain PD_memarray
update_delay_corner -name delay_ssg_125C_RCmin  -library_set lib_ssg_125C -rc_corner rccRCminDP_125C  -power_domain PD_memarray

update_delay_corner -name delay_tt_025C_Nom     -library_set lib_tt_025C  -rc_corner rccnominal_025C  -power_domain PD_memarray

update_delay_corner -name delay_ffg_M40C_Cmax   -library_set lib_ffg_M40C -rc_corner rccCmaxDP_M40C   -power_domain PD_periphery
update_delay_corner -name delay_ffg_M40C_Cmin   -library_set lib_ffg_M40C -rc_corner rccCminDP_M40C   -power_domain PD_periphery
update_delay_corner -name delay_ffg_M40C_RCmax  -library_set lib_ffg_M40C -rc_corner rccRCmaxDP_M40C  -power_domain PD_periphery
update_delay_corner -name delay_ffg_M40C_RCmin  -library_set lib_ffg_M40C -rc_corner rccRCminDP_M40C  -power_domain PD_periphery

update_delay_corner -name delay_ffg_125C_Cmax   -library_set lib_ffg_125C -rc_corner rccCmaxDP_125C   -power_domain PD_periphery
update_delay_corner -name delay_ffg_125C_Cmin   -library_set lib_ffg_125C -rc_corner rccCminDP_125C   -power_domain PD_periphery
update_delay_corner -name delay_ffg_125C_RCmax  -library_set lib_ffg_125C -rc_corner rccRCmaxDP_125C  -power_domain PD_periphery
update_delay_corner -name delay_ffg_125C_RCmin  -library_set lib_ffg_125C -rc_corner rccRCminDP_125C  -power_domain PD_periphery

update_delay_corner -name delay_ssg_M40C_Cmax   -library_set lib_ssg_M40C -rc_corner rccCmaxDP_M40C   -power_domain PD_periphery
update_delay_corner -name delay_ssg_M40C_Cmin   -library_set lib_ssg_M40C -rc_corner rccCminDP_M40C   -power_domain PD_periphery
update_delay_corner -name delay_ssg_M40C_RCmax  -library_set lib_ssg_M40C -rc_corner rccRCmaxDP_M40C  -power_domain PD_periphery
update_delay_corner -name delay_ssg_M40C_RCmin  -library_set lib_ssg_M40C -rc_corner rccRCminDP_M40C  -power_domain PD_periphery

update_delay_corner -name delay_ssg_125C_Cmax   -library_set lib_ssg_125C -rc_corner rccCmaxDP_125C   -power_domain PD_periphery
update_delay_corner -name delay_ssg_125C_Cmin   -library_set lib_ssg_125C -rc_corner rccCminDP_125C   -power_domain PD_periphery
update_delay_corner -name delay_ssg_125C_RCmax  -library_set lib_ssg_125C -rc_corner rccRCmaxDP_125C  -power_domain PD_periphery
update_delay_corner -name delay_ssg_125C_RCmin  -library_set lib_ssg_125C -rc_corner rccRCminDP_125C  -power_domain PD_periphery

update_delay_corner -name delay_tt_025C_Nom     -library_set lib_tt_025C  -rc_corner rccnominal_025C  -power_domain PD_periphery

#################################################################
## LOAD CONSTRAINTS
#################################################################

create_constraint_mode -name func_mode \
            -sdc_files [list src/constraints/dummy.sdc]

## now we create a view that combined the MODE with the CORNER
## hence the name Multi MODE multi CORNER.

create_analysis_view -name view_ffg_M40C_Cmax   -delay_corner delay_ffg_M40C_Cmax  -constraint_mode func_mode
create_analysis_view -name view_ffg_M40C_Cmin   -delay_corner delay_ffg_M40C_Cmin  -constraint_mode func_mode
create_analysis_view -name view_ffg_M40C_RCmax  -delay_corner delay_ffg_M40C_RCmax -constraint_mode func_mode
create_analysis_view -name view_ffg_M40C_RCmin  -delay_corner delay_ffg_M40C_RCmin -constraint_mode func_mode

create_analysis_view -name view_ffg_125C_Cmax   -delay_corner delay_ffg_125C_Cmax  -constraint_mode func_mode
create_analysis_view -name view_ffg_125C_Cmin   -delay_corner delay_ffg_125C_Cmin  -constraint_mode func_mode
create_analysis_view -name view_ffg_125C_RCmax  -delay_corner delay_ffg_125C_RCmax -constraint_mode func_mode
create_analysis_view -name view_ffg_125C_RCmin  -delay_corner delay_ffg_125C_RCmin -constraint_mode func_mode

create_analysis_view -name view_ssg_M40C_Cmax   -delay_corner delay_ssg_M40C_Cmax  -constraint_mode func_mode
create_analysis_view -name view_ssg_M40C_Cmin   -delay_corner delay_ssg_M40C_Cmin  -constraint_mode func_mode
create_analysis_view -name view_ssg_M40C_RCmax  -delay_corner delay_ssg_M40C_RCmax -constraint_mode func_mode
create_analysis_view -name view_ssg_M40C_RCmin  -delay_corner delay_ssg_M40C_RCmin -constraint_mode func_mode

create_analysis_view -name view_ssg_125C_Cmax   -delay_corner delay_ssg_125C_Cmax  -constraint_mode func_mode
create_analysis_view -name view_ssg_125C_Cmin   -delay_corner delay_ssg_125C_Cmin  -constraint_mode func_mode
create_analysis_view -name view_ssg_125C_RCmax  -delay_corner delay_ssg_125C_RCmax -constraint_mode func_mode
create_analysis_view -name view_ssg_125C_RCmin  -delay_corner delay_ssg_125C_RCmin -constraint_mode func_mode

create_analysis_view -name view_tt_025C_Nom     -delay_corner delay_tt_025C_Nom    -constraint_mode func_mode

#################################################################
## SET ANALYSIS VIEWS
#################################################################

## This command determines which VIEWS will be used for analysis. In this
## example we use both 'functional' and 'test_mode' when doing setup analysis
## and we use only the 'hold' view when doing hold analysis.

#Setup with CMax e RCMax SSG -40 125
#Hold  with CMin e RCMin FFG -40 125

set_analysis_view -setup { view_ssg_M40C_Cmax view_ssg_M40C_RCmax view_ssg_125C_Cmax view_ssg_125C_RCmax } \
                  -hold  { view_ffg_M40C_Cmin view_ffg_M40C_RCmin view_ffg_125C_Cmin view_ffg_125C_RCmin }

#At SignOff time, use all the 16 corners for both HOLD and SETUP


## *IMPORTANT* It is actually possible that due to the differences in modelling,
##             for some circuits it could actually be possible that hold violations
##             can occur for 'typical' or 'worst' timing. We would advise to create
##             hold views with three different delay corners, just to make sure that this
##             is not the case.


## The MMMC will affect the way some of the commands are going to work:
## use:
##   timeDesign -expandedViews
## to get separate reports for each view

