namespace eval ::ccopt {}
namespace eval ::ccopt::ilm {}
set ::ccopt::ilm::ccoptSpecRestoreData {}
# Start by checking for unflattened ILMs.
# Will flatten if so and then check the db sync.
if { [catch {ccopt_check_and_flatten_ilms_no_restore}] } {
  return -code error
}
# cache the value of the restore command output by the ILM flattening code
set ::ccopt::ilm::ccoptSpecRestoreData $::ccopt::ilm::ccoptRestoreILMState

#This has been added manually
if { [dbGet head.routeTypes.name default_route_type_leaf] != "default_route_type_leaf" } {
create_route_type -name default_route_type_leaf -bottom_preferred_layer 3 -top_preferred_layer 4
}
if { [dbGet head.routeTypes.name default_route_type_nonleaf] != "default_route_type_nonleaf" } {
create_route_type -name default_route_type_nonleaf -bottom_preferred_layer 4 -top_preferred_layer 6
}
