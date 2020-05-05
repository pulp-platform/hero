read_file -type sourcelist files.list
set_option define TARGET_SYNTHESIS
set_option enableSV yes
set_option enableSV09 yes
set_option top pulp
current_goal Design_Read -top pulp
link_design -force
exit -force 0
