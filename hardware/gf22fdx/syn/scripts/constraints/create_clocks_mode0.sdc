# BOUNDARY CONDITIONS

set_driving_cell -lib_cell SC8T_BUFX6_CSC20L  -pin Z -from_pin A [ all_inputs  ]
set_load                                                     0.1 [ all_outputs ]

# CLOCK

set CLK_PERIOD        2000
set REF_CLK_PERIOD    100000

create_clock -period $CLK_PERIOD -name CLUSTER_CLK [ get_ports clk_i        ]
set_clock_uncertainty   500                        [ get_clocks CLUSTER_CLK ]
set_clock_transition    200                        [ get_clocks CLUSTER_CLK ]

create_clock -period $REF_CLK_PERIOD  -name REF_CLK  [ get_ports  ref_clk_i ]
set_clock_uncertainty   500                          [ get_clocks REF_CLK   ]
set_clock_transition    200                          [ get_clocks REF_CLK   ]

set_clock_groups -asynchronous -group REF_CLK
set_clock_groups -asynchronous -group CLUSTER_CLK

# IDEAL AND DONT TOUCH NETWORKS

set_ideal_network       [get_ports  rst_ni]
set_ideal_network       [get_ports  clk_i ]
set_ideal_network       [get_ports  ref_clk_i]
set_ideal_network       [get_ports  test_mode_i]

set_ideal_network       [get_pins rstgen_i/i_rstgen_bypass/rst_no]

set_dont_touch_network  [get_ports  rst_ni]
set_dont_touch_network  [get_ports  clk_i ]
set_dont_touch_network  [get_ports  ref_clk_i]
set_dont_touch_network  [get_ports  test_mode_i]

set_dont_touch_network  [get_pins rstgen_i/i_rstgen_bypass/rst_no]
