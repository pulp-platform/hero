module foobar (
    input  logic         clk_i,
    input  logic         rst_ni,
    input  logic         req_i,
    input  logic         we_i,
    input  logic [ 31:0] a_i,
    input  logic [ 31:0] b_i,
    output logic [ 63:0] z_o
);

    logic [63:0] z_d;
    logic [15:0] z_s;
    logic [31:0] z_t;

    assign z_d = a_i + b_i;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            z_o <= 0;
        end else begin
            z_o <= z_d + z_s + z_t;
        end
    end

    tc_sram  #(
        .NumWords  (  16 ),
        .DataWidth (  16 ),
        .ByteWidth (   8 ),
        .NumPorts  (   1 )
    ) i_tc_sram (
        .clk_i   ( clk_i     ),
        .rst_ni  ( rst_ni    ),
        .req_i   ( req_i     ),
        .we_i    ( we_i      ),
        .addr_i  ( a_i [3:0] ),
        .wdata_i ( z_d [15:0] ),
        .be_i    ( z_o [1:0]  ),
        .rdata_o ( z_s       )
    );

    tc_sram  #(
        .NumWords  (  32 ),
        .DataWidth (  32 ),
        .ByteWidth (   8 ),
        .NumPorts  (   1 )
    ) i_tc_sram_2 (
        .clk_i   ( clk_i     ),
        .rst_ni  ( rst_ni    ),
        .req_i   ( req_i     ),
        .we_i    ( we_i      ),
        .addr_i  ( a_i [4:0] ),
        .wdata_i ( z_d [31:0] ),
        .be_i    ( z_o [3:0]  ),
        .rdata_o ( z_t       )
    );

endmodule : foobar
