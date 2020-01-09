// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Igor Loi <igor.loi@unibo.it>
// Davide Rossi <davide.rossi@unibo.it>

`include "mchan_defines.sv"

module mchan_arbiter
#(
    parameter DATA_WIDTH = 32,
    parameter N_MASTER   = 2,
    parameter LOG_MASTER = (N_MASTER == 1) ? 1 : $clog2(N_MASTER)
)
(
    input  logic                                clk,
    input  logic                                rst_n,
    
    // ---------------- REQ_SIDE --------------------------
    input  logic [N_MASTER-1:0]                 req_i,
    output logic [N_MASTER-1:0]                 gnt_o,
    input  logic [N_MASTER-1:0][DATA_WIDTH-1:0] data_i,
    
    // Outputs
    output  logic                               req_o,
    input   logic                               gnt_i,
    output  logic [DATA_WIDTH-1:0]              data_o,
    output  logic [LOG_MASTER-1:0]              id_o
);
   
   localparam N_WIRE =  N_MASTER - 2;
   
   logic [LOG_MASTER-1:0]                       RR_FLAG;
   
   typedef logic [LOG_MASTER-1:0]               temp_ID_type;
   
   
   genvar                       j,k;
   
   generate
      
      if(N_MASTER == 1)
        begin
           assign req_o    = req_i[0];
           assign gnt_o[0] = gnt_i;
           assign data_o   = data_i[0];
           assign id_o     = '0;
        end
      else
        begin
           if(N_MASTER == 2)
             begin : INCR // START of  MASTER  == 2
                // ---------------- FAN IN PRIMITIVE  -------------------------
                mchan_arb_primitive #( .DATA_WIDTH(DATA_WIDTH) , .ID_WIDTH(LOG_MASTER) ) MCHAN_ARB_FAN_IN_REQ
                  (
                   .RR_FLAG  ( RR_FLAG   ),
                   .req0_i   ( req_i[0]  ),
                   .req1_i   ( req_i[1]  ),
                   .gnt0_o   ( gnt_o[0]  ),
                   .gnt1_o   ( gnt_o[1]  ),
                   .data0_i  ( data_i[0] ),
                   .data1_i  ( data_i[1] ),
                   .id0_i    ( 1'b0      ),
                   .id1_i    ( 1'b1      ),
                   .req_o    ( req_o     ),
                   .gnt_i    ( gnt_i     ),
                   .data_o   ( data_o    ),
                   .id_o     ( id_o      )
                   );
             end // block: INCR
           else // More than two master
             begin : BINARY_TREE
                logic [DATA_WIDTH-1:0]          data_LEVEL[N_WIRE-1:0];
                logic [LOG_MASTER-1:0]          id_LEVEL[N_WIRE-1:0];
                logic                           req_LEVEL[N_WIRE-1:0];
                logic                           gnt_LEVEL[N_WIRE-1:0];
                
                for(j=0; j < LOG_MASTER; j++) // Iteration for the number of the stages minus one
                  begin : STAGE
                     for(k=0; k<2**j; k=k+1) // Iteration needed to create the binary tree
                       begin : INCR_VERT
                          
                          if (j == 0 )  // LAST NODE, drives the module outputs
                            begin : LAST_NODE
                               mchan_arb_primitive #( .DATA_WIDTH(DATA_WIDTH), .ID_WIDTH(LOG_MASTER) ) MCHAN_ARB_FAN_IN_REQ
                                 (
                                  .RR_FLAG ( RR_FLAG[LOG_MASTER-j-1]),
                                  // LEFT SIDE
                                  .req0_i  ( req_LEVEL[2*k]         ),
                                  .req1_i  ( req_LEVEL[2*k+1]       ),
                                  .gnt0_o  ( gnt_LEVEL[2*k]         ),
                                  .gnt1_o  ( gnt_LEVEL[2*k+1]       ),
                                  .data0_i ( data_LEVEL[2*k]        ),
                                  .data1_i ( data_LEVEL[2*k+1]      ),
                                  .id0_i   ( id_LEVEL[2*k]          ),
                                  .id1_i   ( id_LEVEL[2*k+1]        ),
                                  // RIGTH SIDE
                                  .req_o   ( req_o                  ),
                                  .gnt_i   ( gnt_i                  ),
                                  .data_o  ( data_o                 ),
                                  .id_o    ( id_o                   )
                                  );
                            end 
                          else if ( j < LOG_MASTER - 1) // Middle Nodes
                            begin : MIDDLE_NODES // START of MIDDLE LEVELS Nodes
                               mchan_arb_primitive #( .DATA_WIDTH(DATA_WIDTH) , .ID_WIDTH(LOG_MASTER) ) MCHAN_ARB_FAN_IN_REQ
                                 (
                                  .RR_FLAG(RR_FLAG[LOG_MASTER-j-1]),
                                  // LEFT SIDE
                                  .data0_i  (  data_LEVEL[((2**j)*2-2) + 2*k]     ),
                                  .data1_i  (  data_LEVEL[((2**j)*2-2) + 2*k +1]  ),
                                  .req0_i   (  req_LEVEL[((2**j)*2-2) + 2*k]      ),
                                  .req1_i   (  req_LEVEL[((2**j)*2-2) + 2*k+1]    ),
                                  .gnt0_o   (  gnt_LEVEL[((2**j)*2-2) + 2*k]      ),
                                  .gnt1_o   (  gnt_LEVEL[((2**j)*2-2) + 2*k+1]    ),
                                  .id0_i    (  id_LEVEL[((2**j)*2-2) + 2*k]       ),
                                  .id1_i    (  id_LEVEL[((2**j)*2-2) + 2*k+1]     ),
                                  // RIGTH SIDE
                                  .data_o  (   data_LEVEL[((2**(j-1))*2-2) + k]   ),
                                  .req_o   (   req_LEVEL[((2**(j-1))*2-2) + k]    ),
                                  .gnt_i   (   gnt_LEVEL[((2**(j-1))*2-2) + k]    ),
                                  .id_o    (   id_LEVEL[((2**(j-1))*2-2) + k]     )
                                  );
                            end  // END of MIDDLE LEVELS Nodes
                          else // First stage (connected with the Main inputs ) --> ( j == N_MASTER - 1 )
                            begin : LEAF_NODES  // START of FIRST LEVEL Nodes (LEAF)
                               
                               mchan_arb_primitive #( .DATA_WIDTH(DATA_WIDTH), .ID_WIDTH(LOG_MASTER) ) MCHAN_ARB_FAN_IN_REQ
                                 (
                                  .RR_FLAG ( RR_FLAG[LOG_MASTER-j-1]           ),
                                  // LEFT SIDE
                                  .req0_i  ( req_i[2*k]                        ),
                                  .req1_i  ( req_i[2*k+1]                      ),
                                  .gnt0_o  ( gnt_o[2*k]                        ),
                                  .gnt1_o  ( gnt_o[2*k+1]                      ),
                                  .data0_i ( data_i[2*k]                       ),
                                  .data1_i ( data_i[2*k+1]                     ),
                                  .id0_i   ( temp_ID_type'(2*k)                ), //CORE ID
                                  .id1_i   ( temp_ID_type'(2*k+1)              ), //CORE ID
                                  // RIGTH SIDE
                                  .data_o  ( data_LEVEL[((2**(j-1))*2-2) + k]  ),
                                  .req_o   ( req_LEVEL[((2**(j-1))*2-2) + k]   ),
                                  .gnt_i   ( gnt_LEVEL[((2**(j-1))*2-2) + k]   ),
                                  .id_o    (  id_LEVEL[((2**(j-1))*2-2) + k]   )
                                  );
                            end // End of FIRST LEVEL Nodes (LEAF)
                       end
                  end
             end // block: BINARY_TREE
        end
   endgenerate
   
   //COUNTER USED TO SWITCH PERIODICALLY THE PRIORITY FLAG"
   mchan_rr_flag_req #( .WIDTH(LOG_MASTER) )  RR_REQ
     (
      .clk(clk),
      .rst_n(rst_n),
      .RR_FLAG_req_o(RR_FLAG),
      .req_i(req_o),
      .gnt_i(gnt_i)
      );
   
endmodule
