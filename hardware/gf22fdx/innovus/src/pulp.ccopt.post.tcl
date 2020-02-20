#Added manually
set_ccopt_property buffer_cells       [ list SC8T_CKBUFX2_CSC20L      \
                                             SC8T_CKBUFX4_CSC20L      \
                                             SC8T_CKBUFX6_CSC20L      \
                                             SC8T_CKBUFX8_CSC20L      \
                                             SC8T_CKBUFX10_CSC20L     \
                                             SC8T_CKBUFX12_CSC20L     \
                                      ]

set_ccopt_property inverter_cells     [ list SC8T_CKINVX2_CSC20L      \
                                             SC8T_CKINVX4_CSC20L      \
                                             SC8T_CKINVX6_CSC20L      \
                                             SC8T_CKINVX8_CSC20L      \
                                             SC8T_CKINVX10_CSC20L     \
                                             SC8T_CKINVX12_CSC20L     \
                                      ]

set_ccopt_property clock_gating_cells [ list SC8T_CKGPRELATNX1_CSC20L \
                                             SC8T_CKGPRELATNX2_CSC20L \
                                             SC8T_CKGPRELATNX4_CSC20L \
                                      ]

check_ccopt_clock_tree_convergence
# Restore the ILM status if possible
if { [get_ccopt_property auto_design_state_for_ilms] == 0 } {
  if {$::ccopt::ilm::ccoptSpecRestoreData != {} } {
    eval $::ccopt::ilm::ccoptSpecRestoreData
  }
}
