# CREATE CLOCKS
source -echo -verbose ./src/constraints/PrePlace/create_clocks_mode0.sdc

# BOUNDARY
source -echo -verbose ./src/constraints/PrePlace/boundary_conditions.sdc

# EXCEPTIONS
source -echo -verbose ./src/constraints/PrePlace/exceptions.sdc

# INPUT OUTPUT DELAY
source -echo -verbose ./src/constraints/PrePlace/input_output_delay.sdc
