module simple_twoclk (
    input logic clk_i,
    input logic rst_i,

    input logic clk_ext_i,

    input  logic [31:0] a,          // clk_i driven
    input  logic        a_valid_i,
    output logic        a_ready_o,
    input  logic [31:0] b,          // clk_i driven
    output logic [31:0] z,          // clk_ext_i driven
    output logic        z_valid_o,
    input  logic        z_ready_i,
    output logic [31:0] z_bb        // clk_i driven
);

    // random 2-clock FIFO
    cdc_fifo_gray #(
        .T         ( logic [31:0] ),
        .LOG_DEPTH ( 3            )
    ) i_cdc_fifo_gray (
        .src_rst_ni  ( rst_ni    ),
        .src_clk_i   ( clk_i     ),
        .src_data_i  ( a         ),
        .src_valid_i ( a_valid_i ),
        .src_ready_o ( a_ready_o ),
        .dst_rst_ni  ( rst_ni    ),
        .dst_clk_i   ( clk_ext_i ),
        .dst_data_o  ( z         ),
        .dst_valid_o ( z_valid_o ),
        .dst_ready_i ( z_ready_i )
    );

    // Intentional blackbox
    ext_bb i_bb (
        .clk_i  ( clk_i     ),
        .rst_ni ( rst_ni    ),
        .in1    ( a         ),
        .in2    ( b         ),
        .out    ( z_bb      )
    );

endmodule : simple_twoclk
