# CLOCK

set CLK_PERIOD        2000
set REF_CLK_PERIOD    100000

create_clock -period $CLK_PERIOD -name PULP_CLK [ get_ports clk_i     ]
set_clock_uncertainty   300                     [ get_clocks PULP_CLK ]
set_clock_transition    200                     [ get_clocks PULP_CLK ]

set_clock_groups -asynchronous -group PULP_CLK
