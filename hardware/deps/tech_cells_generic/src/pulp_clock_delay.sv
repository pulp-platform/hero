`timescale 1ns/1ps 
module pulp_clock_delay
(
   input  logic in_i,
   output logic out_o
);


assign #(0.300) out_o = in_i;

endmodule // pulp_clock_delay
