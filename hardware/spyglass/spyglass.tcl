read_file -type sourcelist files.list
set_option define {TARGET_SYNTHESIS TARGET_GF22}
set_option enableSV yes
set_option enableSV09 yes
set_option ignoredu {IN22FDX_R1PH_NFHN_W00064B128M02C256 IN22FDX_R1PH_NFHN_W01024B032M04C256}
set_option top pulp
current_goal Design_Read -top pulp
link_design -force
exit -force 0
