#VSS
  #M9->M8
editSelectVia -net VSS -cut_layer YX
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 1 -via_rows 2
deselectAll
  #M8->M7
editSelectVia -net VSS -cut_layer A5
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 2 -via_rows 6
deselectAll
  #M7->M6
editSelectVia -net VSS -cut_layer A4
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 2 -via_rows 6
deselectAll
  #M6->M5
editSelectVia -net VSS -cut_layer A3
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 2 -via_rows 6
deselectAll
  #M5->M4
editSelectVia -net VSS -cut_layer A2
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 2 -via_rows 6
deselectAll
  #M4->M3
editSelectVia -net VSS -cut_layer A1
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 2 -via_rows 6
deselectAll
