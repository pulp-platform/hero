# CREATE CLOCKS
source -echo -verbose ./scripts/constraints/create_clocks_mode0.sdc

# BOUNDARY
source -echo -verbose ./scripts/constraints/boundary_conditions.sdc

# EXCEPTIONS
source -echo -verbose ./scripts/constraints/exceptions.sdc

# INPUT OUTPUT DELAY
source -echo -verbose ./scripts/constraints/input_output_delay.sdc
