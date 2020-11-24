module simple (
    input  logic a,
    input  logic b,
    output logic z,
    input  logic clk_i,
    input  logic rst_ni
);
    assign z = a ^ b;

endmodule : simple
