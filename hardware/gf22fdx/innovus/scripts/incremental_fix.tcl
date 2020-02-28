#With the new ROM LEF from fix v1

verify_drc
verifyProcessAntenna
setNanoRouteMode -routeInsertAntennaDiode true
globalDetailRoute
saveDesign save/pulp_chip_fixDRC_v2.enc
verify_drc
verifyProcessAntenna

##Diode in ROM, from fix v2

#deleteFiller -prefix FILL
#
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[0]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[1]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[2]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[3]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[4]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[5]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[6]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[7]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[8]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[9]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[10]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[11]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[12]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[13]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[14]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[15]} -prefix ANTECO
#
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[16]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[17]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[18]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[19]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[20]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[21]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[22]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[23]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[24]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[25]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[26]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[27]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[28]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[29]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[30]} -prefix ANTECO
#attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[31]} -prefix ANTECO
#
#refinePlace
#
#verify_drc
#setNanoRouteMode -routeWithECO true
#setNanoRouteMode -drouteFixAntenna true
#globalDetailRoute
#
#setFillerMode -doDRC true
#setFillerMode -ecoMode true
#addFiller
#
#verify_drc
#verifyProcessAntenna
#
#ecoRoute -fix_drc
#
#verify_drc
#verifyProcessAntenna
#
#saveDesign save/pulp_chip_fixDRC_v3.enc
#Did not work

##Diode in ROM v2, restore from v2

deleteFiller -prefix FILL

attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[0]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[1]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[2]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[3]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[4]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[5]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[6]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[7]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[8]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[9]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[10]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[11]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[12]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[13]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[14]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[15]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[16]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[17]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[18]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[19]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[20]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[21]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[22]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[23]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[24]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[25]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[26]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[27]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[28]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[29]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[30]} -prefix ANTECO
attachDiode -diodeCell SC8T_ANTENNAX11_CSC24L -pin {soc_domain_i/ulpsoc_i/boot_rom_i/rom_mem_i Q[31]} -prefix ANTECO

setPlaceMode -place_detail_preserve_routing true
refinePlace

clearDrc

setNanoRouteMode -quiet -routeWithTimingDriven false
setNanoRouteMode -quiet -routeInsertAntennaDiode false
setNanoRouteMode -quiet -routeWithSiDriven false
setNanoRouteMode -routeWithECO true
setNanoRouteMode -drouteFixAntenna false

globalDetailRoute

setFillerMode -doDRC true
setFillerMode -ecoMode true
addFiller


verify_drc
verifyProcessAntenna

saveDesign save/pulp_chip_fixDRC_v4.enc

if { [ info exists DESIGNNAME ] } {
   set NAME "$DESIGNNAME"

} else {
    set NAME "final"

}

foreach cell [dbGet -p head.libCells.name *] {
  if [string match "SC8T_FILL*"          [dbGet ${cell}.name]]  { lappend excludeCellInstList [dbGet ${cell}.name]}
  if [string match "*30P_FILL*"          [dbGet ${cell}.name]]  { lappend excludeCellInstList [dbGet ${cell}.name]}
  if [string match "SC8T*COLCAPPX1_CSC*" [dbGet ${cell}.name]]  { lappend excludeCellInstList [dbGet ${cell}.name]}
  if [string match "SC8T_COLCAPNX1_CSC*" [dbGet ${cell}.name]]  { lappend excludeCellInstList [dbGet ${cell}.name]}
  if [string match "*_CONCAVEPRX9_CSC*"  [dbGet ${cell}.name]]  { lappend excludeCellInstList [dbGet ${cell}.name]}
  if [string match "*_CONCAVEPLX9_CSC*"  [dbGet ${cell}.name]]  { lappend excludeCellInstList [dbGet ${cell}.name]}
  if [string match "*_CONCAVENRX9_CSC*"  [dbGet ${cell}.name]]  { lappend excludeCellInstList [dbGet ${cell}.name]}
  if [string match "*_CONCAVENLX9_CSC*"  [dbGet ${cell}.name]]  { lappend excludeCellInstList [dbGet ${cell}.name]}
}

saveNetlist out/${NAME}.v -excludeLeafCell
saveNetlist out/${NAME}_pwr.v -excludeLeafCell -excludeCellInst $excludeCellInstList -includePowerGround

# This netlist contains all filler cells and everything.
# This have to be used for LVS
saveNetlist out/${NAME}_lvs.v -excludeLeafCell -excludeCellInst $excludeCellInstList -includePhysicalInst -phys


# layout
setStreamOutMode -SEvianames ON -specifyViaName %t_VIA -virtualConnection false

# you can set an alternative top name with -structureName
# streamOut out/${NAME}.gds.gz -structureName sem01w0
# for design with a macro merged by cockpit
streamOut out/${NAME}.gds.gz  -mapFile ../technology/22FDSOI_edi2gds_colored.layermap -outputMacros -merge {  \
  /usr/pack/gf-22-kgf/invecas/std/V05R00/GF22FDX_SC8T_104CPP_BASE_CSC20SL/gds/GF22FDX_SC8T_104CPP_BASE_CSC20SL.gds \
  /usr/pack/gf-22-kgf/invecas/std/V05R00/GF22FDX_SC8T_104CPP_BASE_CSC20L/gds/GF22FDX_SC8T_104CPP_BASE_CSC20L.gds \
  /usr/pack/gf-22-kgf/invecas/std/V05R00/GF22FDX_SC8T_104CPP_BASE_CSC24SL/gds/GF22FDX_SC8T_104CPP_BASE_CSC24SL.gds \
  /usr/pack/gf-22-kgf/invecas/std/V05R00/GF22FDX_SC8T_104CPP_BASE_CSC24L/gds/GF22FDX_SC8T_104CPP_BASE_CSC24L.gds \
  /usr/pack/gf-22-kgf/invecas/std/V05R00/GF22FDX_SC8T_104CPP_BASE_CSC28SL/gds/GF22FDX_SC8T_104CPP_BASE_CSC28SL.gds \
  /usr/pack/gf-22-kgf/invecas/std/V05R00/GF22FDX_SC8T_104CPP_BASE_CSC28L/gds/GF22FDX_SC8T_104CPP_BASE_CSC28L.gds \
  /usr/pack/gf-22-kgf/invecas/std/V02R00/GF22FDX_SC8T_104CPP_LPK_CSL/gds/GF22FDX_SC8T_104CPP_LPK_CSL.gds \
  /usr/pack/gf-22-kgf/invecas/io/V04R30/IN22FDX_GPIO18_10M3S30P_V0430/gds/IN22FDX_GPIO18_10M3S30P_V0430.gds \
  /usr/pack/gf-22-kgf/dz/mem/gds/IN22FDX_S1D_NFRG_W04096B032M04C128.gds \
  /usr/pack/gf-22-kgf/dz/mem/gds/IN22FDX_S1D_NFRG_W02048B032M04C128.gds \
  /usr/pack/gf-22-kgf/dz/mem/gds/IN22FDX_ROMI_FRG_W02048B032M32C064_boot_code.gds \
  ../../fe/ips/gf22_FLL/deliverable/GDS/gf22_FLL.gds \
  }

timedesign -postRoute -expandedViews       -outDir reports/timing -prefix pulpissimo_final_pathGroupECOv4
timedesign -postRoute -expandedViews -hold -outDir reports/timing -prefix pulpissimo_final_pathGroupECOv4

set_global timing_recompute_sdf_in_setuphold_mode true
# Write out SDF, take the first analysis_views from the hold and the setup list
write_sdf -precision 4 -min_period_edges posedge -recompute_parallel_arcs -nonegchecks \
          -min_view view_ffg_125C_RCmin \
          -typ_view view_tt_025C_Nom    \
          -max_view view_ssg_M40C_RCmax \
          out/${NAME}.sdf.gz
