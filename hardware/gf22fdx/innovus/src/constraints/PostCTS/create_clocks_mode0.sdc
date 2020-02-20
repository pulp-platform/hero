# REF CLOCK: 10 MHz, actually 32 KHz
set REF_C_Period               100000
set REF_C_Latency_Max            1000
set REF_C_Latency_Min             500
set REF_C_Uncertainty             500

# FLL1 CLOCK: 500 MHz
set SOC_C_Period                 3500
set SOC_C_Latency_Max            1000
set SOC_C_Latency_Min             900
set SOC_C_Uncertainty             500

# FLL2 CLOCK: 500 MHz
set PER_C_Period                 3500
set PER_C_Latency_Max            1000
set PER_C_Latency_Min             900
set PER_C_Uncertainty             500

# FLL3 CLOCK: 1 GHz
set CLUSTER_C_Period             1000
set CLUSTER_C_Latency_Max        1000
set CLUSTER_C_Latency_Min         900
set CLUSTER_C_Uncertainty         500

#DUAL CLOCK FIFO
set INPUT_LATENCY_FROM_MUX       500
set MAX_TURNAROUND_LATENCY       200
set MAX_DELAY_READ_POINTER_O     200

#########################
### CLOCKS DEFINITION ###
#########################

# REF CLOCK
create_clock -name REF_CLK   -period      $REF_C_Period      [get_ports ref_clk_i]
set_clock_uncertainty                     $REF_C_Uncertainty [get_clocks REF_CLK]
set_clock_transition                      200                [get_clocks REF_CLK]

# FLL1 CLK
create_clock -name FLL1_CLK -period $SOC_C_Period [ get_pins i_clk_rst_gen/i_fll_soc/FLLCLK ]
set_clock_uncertainty                     $SOC_C_Uncertainty [get_clocks FLL1_CLK]
set_clock_transition                      200                [get_clocks FLL1_CLK]

# FLL2 CLK
create_clock -name FLL2_CLK -period $PER_C_Period [ get_pins i_clk_rst_gen/i_fll_per/FLLCLK ]
set_clock_uncertainty                     $PER_C_Uncertainty [get_clocks FLL2_CLK]
set_clock_transition                      200                [get_clocks FLL2_CLK]

# FLL3 CLK
create_clock -name FLL3_CLK -period $CLUSTER_C_Period [ get_pins i_clk_rst_gen/i_fll_cluster/FLLCLK ]
set_clock_uncertainty                     $CLUSTER_C_Uncertainty [get_clocks FLL3_CLK]
set_clock_transition                      200                    [get_clocks FLL3_CLK]

# SOC CLK
set_dont_touch         [ get_cells i_clk_rst_gen/clk_mux_fll_soc_i/clk_mux_i        ]
set_case_analysis 0    [ get_pins  i_clk_rst_gen/clk_mux_fll_soc_i/clk_mux_i/CLKSEL ]
create_generated_clock [ get_pins i_clk_rst_gen/clk_mux_fll_soc_i/clk_mux_i/Z ] \
                        -name SOC_CLK -source [ get_pins i_clk_rst_gen/i_fll_soc/FLLCLK ] -divide_by 1
# PER CLK
set_dont_touch         [ get_cells i_clk_rst_gen/clk_mux_fll_per_i/clk_mux_i        ]
set_case_analysis 0    [ get_pins  i_clk_rst_gen/clk_mux_fll_per_i/clk_mux_i/CLKSEL ]
create_generated_clock [ get_pins i_clk_rst_gen/clk_mux_fll_per_i/clk_mux_i/Z ] \
                        -name PER_CLK -source [ get_pins i_clk_rst_gen/i_fll_per/FLLCLK ] -divide_by 1

# CLUSTER CLK
set_dont_touch         [ get_cells i_clk_rst_gen/clk_mux_fll_cluster_i/clk_mux_i        ]
set_case_analysis 0    [ get_pins  i_clk_rst_gen/clk_mux_fll_cluster_i/clk_mux_i/CLKSEL ]
create_generated_clock [ get_pins i_clk_rst_gen/clk_mux_fll_cluster_i/clk_mux_i/Z ] \
                        -name CLUSTER_CLK -source [ get_pins i_clk_rst_gen/i_fll_cluster/FLLCLK ] -divide_by 1

##################
### FALSE PATH ###
##################

# FALSE PATH ON CLOCK DOMAINS CROSSING
set_clock_groups -asynchronous -group REF_CLK
set_clock_groups -asynchronous -group FLL1_CLK
set_clock_groups -asynchronous -group FLL2_CLK
set_clock_groups -asynchronous -group FLL3_CLK
set_clock_groups -asynchronous -group SOC_CLK
set_clock_groups -asynchronous -group PER_CLK
set_clock_groups -asynchronous -group CLUSTER_CLK
