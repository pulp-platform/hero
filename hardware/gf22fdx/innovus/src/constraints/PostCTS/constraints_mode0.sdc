# CREATE CLOCKS
source -echo -verbose ./src/constraints/PostCTS/create_clocks_mode0.sdc

# BOUNDARY
source -echo -verbose ./src/constraints/PostCTS/boundary_conditions.sdc

# EXCEPTIONS
source -echo -verbose ./src/constraints/PostCTS/exceptions.sdc

# INPUT OUTPUT DELAY
source -echo -verbose ./src/constraints/PostCTS/input_output_delay.sdc
