##########################################################################
#  place RAM macros
##########################################################################

set ramHM0row0 l2_ram_i/CUTS_0__bank_gen_bank_i_cut_0
set ramHM1row0 l2_ram_i/CUTS_1__bank_gen_bank_i_cut_0
set ramHM2row0 l2_ram_i/CUTS_2__bank_gen_bank_i_cut_0
set ramHM3row0 l2_ram_i/CUTS_3__bank_gen_bank_i_cut_0

set ramHM0row1 l2_ram_i/CUTS_0__bank_gen_bank_i_cut_1
set ramHM1row1 l2_ram_i/CUTS_1__bank_gen_bank_i_cut_1
set ramHM2row1 l2_ram_i/CUTS_2__bank_gen_bank_i_cut_1
set ramHM3row1 l2_ram_i/CUTS_3__bank_gen_bank_i_cut_1

set ramHM0row2 l2_ram_i/CUTS_0__bank_gen_bank_i_cut_2
set ramHM1row2 l2_ram_i/CUTS_1__bank_gen_bank_i_cut_2
set ramHM2row2 l2_ram_i/CUTS_2__bank_gen_bank_i_cut_2
set ramHM3row2 l2_ram_i/CUTS_3__bank_gen_bank_i_cut_2

set ramHM0row3 l2_ram_i/CUTS_0__bank_gen_bank_i_cut_3
set ramHM1row3 l2_ram_i/CUTS_1__bank_gen_bank_i_cut_3
set ramHM2row3 l2_ram_i/CUTS_2__bank_gen_bank_i_cut_3
set ramHM3row3 l2_ram_i/CUTS_3__bank_gen_bank_i_cut_3

set ramHM0row4 l2_ram_i/CUTS_0__bank_gen_bank_i_cut_4
set ramHM1row4 l2_ram_i/CUTS_1__bank_gen_bank_i_cut_4
set ramHM2row4 l2_ram_i/CUTS_2__bank_gen_bank_i_cut_4
set ramHM3row4 l2_ram_i/CUTS_3__bank_gen_bank_i_cut_4

set ramHM0row5 l2_ram_i/CUTS_0__bank_gen_bank_i_cut_5
set ramHM1row5 l2_ram_i/CUTS_1__bank_gen_bank_i_cut_5
set ramHM2row5 l2_ram_i/CUTS_2__bank_gen_bank_i_cut_5
set ramHM3row5 l2_ram_i/CUTS_3__bank_gen_bank_i_cut_5

set ramHM0row6 l2_ram_i/CUTS_0__bank_gen_bank_i_cut_6
set ramHM1row6 l2_ram_i/CUTS_1__bank_gen_bank_i_cut_6
set ramHM2row6 l2_ram_i/CUTS_2__bank_gen_bank_i_cut_6
set ramHM3row6 l2_ram_i/CUTS_3__bank_gen_bank_i_cut_6

set ramHM0row7 l2_ram_i/CUTS_0__bank_gen_bank_i_cut_7
set ramHM1row7 l2_ram_i/CUTS_1__bank_gen_bank_i_cut_7
set ramHM2row7 l2_ram_i/CUTS_2__bank_gen_bank_i_cut_7
set ramHM3row7 l2_ram_i/CUTS_3__bank_gen_bank_i_cut_7

set ramPri0row0    l2_ram_i/bank_sram_pri0_i_cut_0
set ramPri1row0    l2_ram_i/bank_sram_pri0_i_cut_1

set ramPri0row1    l2_ram_i/bank_sram_pri1_i_cut_0
set ramPri1row1    l2_ram_i/bank_sram_pri1_i_cut_1

set haloBlock     2.50
set routingBlock [expr $haloBlock + 0.155]

#same for all the Inteleaved cuts
set RamSize      [dbCellDim [dbInstCellName [dbGetInstByName $ramHM0row0  ]]]
set smallRamSize [dbCellDim [dbInstCellName [dbGetInstByName $ramPri1row0 ]]]

set socFLL     i_clk_rst_gen/i_fll_soc
set perFLL     i_clk_rst_gen/i_fll_per
set clusterFLL i_clk_rst_gen/i_fll_cluster

set RamSize_W [expr [lindex $RamSize 0] /1000 ]
set RamSize_H [expr [lindex $RamSize 1] /1000 ]

set smallRamSize_W [expr [lindex $smallRamSize 0] /1000 ]
set smallRamSize_H [expr [lindex $smallRamSize 1] /1000 ]


set sram_initX             2.22
set sram_initY             2.22
set sram_delta_y           1.65
set sram_delta_x           1.65




#Column Left
set X $sram_initX
set Y $sram_initY

set haloSRAM        1.70
set haloSRAM_right  1.70
set haloSRAM_left   1.70
set haloSRAM_bottom 0.92
set haloSRAM_top    0.00

set routingSRAM  [expr $haloSRAM_right  + 0.155]

placeInstance -fixed  $ramHM0row0 $X $Y R0
addHaloToBlock -fromInstBox $haloSRAM_left $haloSRAM       $haloSRAM_right $haloSRAM_top $ramHM0row0

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM0row1 $X $Y R0
addHaloToBlock -fromInstBox $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM0row1

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM0row2 $X $Y R0
addHaloToBlock -fromInstBox $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM0row2

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM0row3 $X $Y R0
addHaloToBlock -fromInstBox $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM0row3

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM0row4 $X $Y R0
addHaloToBlock -fromInstBox $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM0row4

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM0row5 $X $Y R0
addHaloToBlock -fromInstBox $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM0row5

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM0row6 $X $Y R0
addHaloToBlock -fromInstBox $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM0row6

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM0row7 $X $Y R0
addHaloToBlock -fromInstBox $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM0row7

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM1row0 $X $Y R0
addHaloToBlock -fromInstBox $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM1row0

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM1row1 $X $Y R0
addHaloToBlock -fromInstBox $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM1row1

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM1row2 $X $Y R0
addHaloToBlock -fromInstBox $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM1row2

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM1row3 $X $Y R0
addHaloToBlock -fromInstBox $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM1row3

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM1row4 $X $Y R0
addHaloToBlock -fromInstBox $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM1row4

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM1row5 $X $Y R0
addHaloToBlock -fromInstBox $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM     $ramHM1row5

#Avoid stripes in C1 next to the memories as there will be the rings
createRouteBlk -box $sram_initX 0 [expr $sram_initX + $RamSize_W + $routingSRAM] [expr $Y + $RamSize_H ] -layer C1


#Column Right

set Xleft [expr $floorW - $floorMargin - $haloSRAM - $RamSize_W - 0.206 ]

set X $Xleft
set Y $sram_initY

set haloSRAM        1.70
set haloSRAM_right  1.70
set haloSRAM_left   1.70
set haloSRAM_bottom 0.92
set haloSRAM_top    0.00

set routingSRAM  [expr $haloSRAM_left  + 0.155]

placeInstance -fixed  $ramHM2row0 $X $Y R180
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM        $haloSRAM_right $haloSRAM_top $ramHM2row0

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM2row1 $X $Y R180
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM2row1

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM2row2 $X $Y R180
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM2row2

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM2row3 $X $Y R180
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM2row3

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM2row4 $X $Y R180
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM2row4

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM2row5 $X $Y R180
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM2row5

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM2row6 $X $Y R180
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM2row6

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM3row0 $X $Y R180
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM3row0

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM3row1 $X $Y R180
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM3row1

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM3row2 $X $Y R180
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM3row2

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM3row3 $X $Y R180
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM  $ramHM3row3

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM1row7 $X $Y R180
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM  $ramHM1row7

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM2row7 $X $Y R180
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM  $ramHM2row7

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM3row7 $X $Y R180
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM  $ramHM3row7


#Avoid stripes in C1 next to the memories as there will be the rings
createRouteBlk -box [expr $Xleft - $routingSRAM - 0.15] 0 [expr $Xleft + $RamSize_W + $routingSRAM]  [expr $Y + $RamSize_H ] -layer C1


#Column Center Left

set X [expr $floorW/2 - $RamSize_W -0.15]
set Y $sram_initY

set haloSRAM        1.70
set haloSRAM_right  0.046
set haloSRAM_left   1.70
set haloSRAM_bottom 0.90
set haloSRAM_top    0.00

set routingSRAM  [expr $haloSRAM_left  + 0.155]

#left bottom right top: top 0 because it is delta_y from the bottom of the next

placeInstance -fixed  $ramHM3row4 $X $Y R180
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramHM3row4

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM1row6 $X $Y R180
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM $haloSRAM_right $haloSRAM_top $ramHM1row6

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramPri0row1 $X $Y R180
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM_top $ramPri0row1

#for the HALO add 0.8
set Y [expr $Y+$RamSize_H+$haloSRAM+0.8]
placeInstance -fixed  $ramPri0row0 $X $Y R180
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM $haloSRAM_right $haloSRAM $ramPri0row0
#Avoid stripes in C1 next to the memories as there will be the rings
createRouteBlk -box [expr $X - $routingSRAM + 0.15] 0 [expr $X + $RamSize_W + $routingSRAM] [expr $Y + $RamSize_H + $haloSRAM  ] -layer C1

#Column Center Right
#set X $Xcenter_r
set Y $sram_initY
set X [expr $floorW/2 + 0.15]

set haloSRAM        1.70
set haloSRAM_right  1.70
set haloSRAM_left   0.00
set haloSRAM_bottom 0.90
set haloSRAM_top    0.00

set routingSRAM  [expr $haloSRAM_right  + 0.155]

placeInstance -fixed  $ramHM3row5 $X $Y R0
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM     $ramHM3row5

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramHM3row6 $X $Y R0
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM $haloSRAM_right $haloSRAM_top $ramHM3row6

set Y [expr $Y+$RamSize_H+$sram_delta_y]
placeInstance -fixed  $ramPri1row1 $X $Y R0
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM $ramPri1row1

#Avoid stripes in C1 next to the memories as there will be the rings
createRouteBlk -box [expr $X - 0.15] 0  [expr $X + $RamSize_W] [expr $Y + $RamSize_H + $routingSRAM ] -layer C1

#small memory cut
set Y [expr $Y+$RamSize_H+$haloSRAM+0.8]
placeInstance -fixed  $ramPri1row0 $X $Y R0
set haloSRAM_bottom 0.00
addHaloToBlock -fromInstBox  $haloSRAM_left $haloSRAM_bottom $haloSRAM_right $haloSRAM $ramPri1row0
#Avoid stripes in C1 next to the memories as there will be the rings, extra care for the small memory
createRouteBlk -box [expr $X - 0.15] [expr $Y - $sram_delta_y] [expr $X + $smallRamSize_W + $routingSRAM + 0.75] [expr $Y + $smallRamSize_H + $routingSRAM ] -layer C1


#FLL
set fllSize [dbCellDim [dbInstCellName [dbGetInstByName $perFLL]]]
set fllSize_W [expr [lindex $fllSize 0] / 1000]
set fllSize_H [expr [lindex $fllSize 1] / 1000]

#use later for placement
set init_Xfll [expr $floorW/2 - $fllSize_W/2 - 3 -  $fllSize_W/3]
set init_Yfll [expr $floorH - 2.5 - $fllSize_H]

set Xfll $init_Xfll
set Yfll $init_Yfll

set haloFLL 1.50
set routingFLL $haloFLL

placeInstance -fixed $perFLL $Xfll $Yfll R0
addHaloToBlock -fromInstBox $haloFLL $haloFLL 0.8 $haloFLL $perFLL

set Xfll [expr $Xfll + $fllSize_W + 1]

placeInstance -fixed $socFLL $Xfll $Yfll R0
addHaloToBlock -fromInstBox 0 $haloFLL $haloFLL $haloFLL $socFLL

set Xfll [expr $Xfll + $fllSize_W + 1]

placeInstance -fixed $clusterFLL $Xfll $Yfll R0
addHaloToBlock -fromInstBox 0 $haloFLL $haloFLL $haloFLL $clusterFLL

createRouteBlk -box [expr $init_Xfll  - $routingFLL + 5.35 ] [expr $init_Yfll - $routingFLL ] \
[expr $init_Xfll + $fllSize_W*3 + 2 + $routingFLL - 5.22] [expr $init_Yfll + $fllSize_H + $routingFLL + 0.5 ] -layer C1

#otherwise ENDCAP goes out from the coreboundary
createPlaceBlockage -box 0 0.48 $floorW 0.53

redraw

