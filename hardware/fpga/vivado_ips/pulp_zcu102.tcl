create_project pulp_zcu102 ./pulp_zcu102 -part xczu9eg-ffvb1156-2-e
set_property board_part xilinx.com:zcu102:part0:3.3 [current_project]

source ./define_srcs.tcl
add_files -fileset [current_fileset] ./pulp_zcu102.v
add_files -fileset constrs_1 -norecurse {./pulp_zcu102_synth.xdc ./pulp_zcu102_impl.xdc}
set_property used_in_implementation false [get_files ./pulp_zcu102_synth.xdc]
set_property used_in_synthesis false [get_files ./pulp_zcu102_impl.xdc]
set_property top pulp_zcu102 [current_fileset]

synth_design -rtl -name rtl_1

ipx::package_project -root_dir . -vendor ethz.ch -library user -taxonomy /UserIP -import_files \
  -set_current false
ipx::unload_core ./component.xml
ipx::edit_ip_in_project -upgrade true -name tmp_edit_project -directory . ./component.xml
set_property core_revision 2 [ipx::current_core]
ipx::update_source_project_archive -component [ipx::current_core]
ipx::create_xgui_files [ipx::current_core]
ipx::update_checksums [ipx::current_core]
ipx::save_core [ipx::current_core]
ipx::move_temp_component_back -component [ipx::current_core]
close_project -delete

set_property ip_repo_paths . [current_project]
update_ip_catalog
close_project
