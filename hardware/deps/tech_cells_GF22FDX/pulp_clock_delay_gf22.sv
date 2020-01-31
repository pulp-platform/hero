//andy hack: support different standard cell libraries by setting `GF_TRACK,
//`GF_VT and `GF_LEN
// SC8T_CKGPRELATNX1_CSC24L
// SC8T_BUFX3_CSC20L



module pulp_clock_delay
(
   input  logic in_i,
   output logic out_o
);

    logic taps_0;
    logic taps_1;


    SC8T_DLY100X1_CSC20L u_delay_rds_0
    (
        .A ( in_i         ),
        .Z ( taps_0       )
    );

    SC8T_BUFX1_CSC24L clk_inv_i_0
    (
       .A(taps_0),
       .Z(taps_1)
    );

    SC8T_BUFX3_CSC24L clk_inv_i_1
    (
       .A(taps_1),
       .Z(out_o)
    );


endmodule // pulp_clock_delay
