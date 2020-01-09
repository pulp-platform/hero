// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module generic_memory_with_grant
#(
    parameter ADDR_WIDTH = 12,
    parameter DATA_WIDTH = 64,
    parameter BE_WIDTH   = DATA_WIDTH/8
)
(
    input  logic          CLK,
    input  logic          INITN,
    
    input  logic                       CEN,
    input  logic [ADDR_WIDTH-1:0]      A,
    output logic                       GNT,
    input  logic                       WEN,
    input  logic [BE_WIDTH-1:0][7:0]   D,
    input  logic [BE_WIDTH-1:0]        BE,
    
    output logic [DATA_WIDTH-1:0]      Q,
    output logic                       RVAL
 );
   
   localparam   NUM_WORDS = 2**ADDR_WIDTH;
   
   // always_ff @(posedge CLK or negedge INITN)
   // begin
   //   if(~INITN)
   //   begin
   //      GNT <= 1'b0;
   //   end
   //   else
   //   begin
   //      GNT <= $random()%2;
   //   end
   // end

   assign GNT = 1;

   logic [BE_WIDTH-1:0][7:0]           MEM [NUM_WORDS-1:0];
   logic [31:0] temp_32_bit;

    int unsigned  i;


    assign req_int = (CEN == 1'b0 ) & (GNT == 1'b1);


    always @(posedge CLK)
    begin
        if ( req_int )
        begin
              RVAL <= 1'b1;
              if ( WEN == 1'b0 )
              begin
                 Q <= 'X;

                 for (i=0; i < BE_WIDTH; i++) 
                 begin
                    if ( BE[i] == 1'b1 )
                    begin
                      MEM[A][i] <= D[i];
                    end
                 end
              end
              else
              begin
                     Q <= MEM[A];
              end
        end
        else  // req_int == 0
        begin
           RVAL <= 1'b0;
           Q <= 'X;
        end
    end

    initial
    begin
        for(i=0;i<2**ADDR_WIDTH-1;i++)
        begin
            temp_32_bit = i*8;
            MEM[i] = {temp_32_bit+4,temp_32_bit};
        end

    end

   
endmodule
