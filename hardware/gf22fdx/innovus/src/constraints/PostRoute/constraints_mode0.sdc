# CREATE CLOCKS
source -echo -verbose ./src/constraints/PostRoute/create_clocks_mode0.sdc

# BOUNDARY
source -echo -verbose ./src/constraints/PostRoute/boundary_conditions.sdc

# EXCEPTIONS
source -echo -verbose ./src/constraints/PostRoute/exceptions.sdc

# INPUT OUTPUT DELAY
source -echo -verbose ./src/constraints/PostRoute/input_output_delay.sdc
