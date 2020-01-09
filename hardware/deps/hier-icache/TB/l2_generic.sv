// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


//********************************************************
//************* L2 RAM MEMORY WRAPPER ********************
//********************************************************

module l2_generic
#(
  parameter            ADDR_WIDTH = 12
)
(
  input logic                    CLK,
  input logic                    RSTN,

  input logic                    CEN,
  input logic                    WEN,
  input logic [ADDR_WIDTH-1:0]   A,
  input logic [63:0]             D,
  input logic [7:0]              BE,
  output logic [63:0]            Q
);
   
    logic           s_cen;
    logic           s_wen;
            
    // GENERATION OF CEN
    always_comb
    begin
      s_cen = 1'b1;
      if (CEN == 1'b0)
        s_cen = 1'b0;         
    end
   
    // GENERATION OF WEN
    always_comb
    begin
      s_wen = 1'b1;
      if (WEN == 1'b0)
        s_wen = 1'b0;       
    end



   generic_memory_with_grant
   #(
      .ADDR_WIDTH (ADDR_WIDTH),
      .DATA_WIDTH (64)
   )
   cut
   (
      .CLK   (CLK),  
      .INITN (RSTN),

      .CEN   (s_cen),  
      .A     (A[ADDR_WIDTH-1:0]),    
      .GNT   (),  
      .WEN   (s_wen),  
      .D     (D),    
      .BE    (BE),   
      .Q     (Q),    
      .RVAL  ()
   );
      
endmodule