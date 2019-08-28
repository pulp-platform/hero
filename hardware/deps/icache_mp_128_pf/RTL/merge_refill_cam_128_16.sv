////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Copyright 2018 ETH Zurich and University of Bologna.                       //
// Copyright and related rights are licensed under the Solderpad Hardware     //
// License, Version 0.51 (the "License"); you may not use this file except in //
// compliance with the License.  You may obtain a copy of the License at      //
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law  //
// or agreed to in writing, software, hardware and materials distributed under//
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR     //
// CONDITIONS OF ANY KIND, either express or implied. See the License for the //
// specific language governing permissions and limitations under the License. //
//                                                                            //
// Company:        Micrel Lab @ DEIS - University of Bologna                  //
//                    Viale Risorgimento 2 40136                              //
//                    Bologna - fax 0512093785 -                              //
//                                                                            //
// Engineer:       Igor Loi - igor.loi@unibo.it                               //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
//                                                                            //
// Create Date:    22/01/2018                                                 //
// Design Name:    ICACHE_MP_128_PF                                           //
// Module Name:    merge_refill_cam_128_16                                    //
// Project Name:   MrWolf                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    This block implemets a CAM with 16 slots, used to track    //
//                 outstanding refills. Anytime a refill is required, the     //
//                 main CC first checks that there is not yet a pending refill//
//                 on that cache line. If yes, it simply updated that Entry   //
//                 of the cam. In case there is no valid entry, it pushed     //
//                 refill info in the CAM , and it assertd a refill.          //
//                 When Refill is Back from AXI port, the related entry is    //
//                 popped, and all the related processor are notified.        //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - 22/01/2018 : File Created                                  //
// Additional Comments:                                                       //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


module merge_refill_cam_128_16
#(
    parameter  NB_WAYS        = 4,
    parameter  ID_WIDTH       = 4, 
    parameter  LOG2_ID_WIDTH  = $clog2(ID_WIDTH),
    parameter  ADDR_WIDTH     = 32,
    parameter  DEPTH          = 16,
    parameter  LOG2_DEPTH     = $clog2(DEPTH),
    parameter  ADDR_CHECK_LSB = 4,
    parameter  ADDR_CHECK_MSB = ADDR_WIDTH-1
)
(
    input  logic                      clk,
    input  logic                      rst_n,

    output logic                      empty_o,

    input  logic                      fetch_req_i,
    input  logic [LOG2_ID_WIDTH-1:0]  fetch_ID_BIN_i,
    input  logic [ID_WIDTH-1:0]       fetch_ID_OH_i,
    input  logic [ADDR_WIDTH-1:0]     fetch_addr_i,
    input  logic [NB_WAYS-1:0]        fetch_way_i,
    output logic                      fetch_gnt_o,
    output logic [ID_WIDTH-1:0]       retry_fetch_o,

    input  logic                      AXI_rvalid_i,
    input  logic [LOG2_DEPTH-1:0]     AXI_rID_i,

    output logic                      AXI_req_o,
    output logic [ADDR_WIDTH-1:0]     AXI_addr_o,
    output logic [LOG2_DEPTH-1:0]     AXI_ID_o,
    input  logic                      AXI_gnt_i,


    // for refill PURPOSE ONLY
    output logic [ADDR_WIDTH-1:0]     refill_addr_o,
    output logic [ID_WIDTH-1:0]       refill_ID_o,
    output logic [NB_WAYS-1:0]        refill_way_o
);


   logic [DEPTH-1:0]                                  LOOKUP_TABLE;
   logic [ID_WIDTH-1:0]                               ID_TABLE   [DEPTH-1:0];
   logic [NB_WAYS+ADDR_WIDTH-1:0]                     ADDR_TABLE [DEPTH-1:0];

   logic [DEPTH-1:0]                                  check_push_Match_addr;
   logic [$clog2(DEPTH)-1:0]                          push_MATCH_index;

   logic [ADDR_WIDTH-1:0]                             last_refill_addr;
   logic                                              last_refill_valid;
   logic                                              FIFO_full;



    assign FIFO_full     = (&LOOKUP_TABLE) ? 1'b1 : 1'b0;
    assign empty_o       = (|LOOKUP_TABLE) ? 1'b0 : 1'b1;


   assign refill_addr_o  = {ADDR_TABLE[AXI_rID_i][ADDR_WIDTH-1:0]};
   assign refill_way_o   =  ADDR_TABLE[AXI_rID_i][NB_WAYS+ADDR_WIDTH-1:ADDR_WIDTH];
   assign refill_ID_o    =  ID_TABLE[AXI_rID_i];


   int unsigned i,j,k;


    always_ff @(posedge clk or negedge rst_n) 
    begin
        if(~rst_n) 
        begin
            for(i=0; i<DEPTH; i++)
            begin
                  LOOKUP_TABLE[i] <= 1'b0;
                  ID_TABLE[i]     <= '0;
                  ADDR_TABLE[i]   <= '0;
            end
            last_refill_addr  <= '0;
            last_refill_valid <= 1'b0;
            retry_fetch_o     <= '0;

        end 
        else 
        begin

            // Handle Response
            if(AXI_rvalid_i)
            begin
                  LOOKUP_TABLE  [AXI_rID_i] <= 1'b0;
                  ID_TABLE      [AXI_rID_i] <= '0;
                  ADDR_TABLE    [AXI_rID_i] <= '0;
                  last_refill_addr <= ADDR_TABLE[AXI_rID_i][ADDR_WIDTH-1:0];
            end

            last_refill_valid <= AXI_rvalid_i;

            //check if the last refill and current address match
            if( ((fetch_req_i == 1'b1) && (last_refill_valid == 1'b1) && ( last_refill_addr[ADDR_CHECK_MSB:ADDR_CHECK_LSB] == fetch_addr_i[ADDR_CHECK_MSB:ADDR_CHECK_LSB] )) || ((AXI_rID_i==push_MATCH_index) && (|check_push_Match_addr == 1'b1) && ( AXI_rvalid_i)) )  
            begin
                retry_fetch_o <= fetch_ID_OH_i;
            end
            else
            begin

                retry_fetch_o <= '0;
               // CODE HERE
                if(|check_push_Match_addr)
                begin
                       if(fetch_req_i)
                       begin
                           LOOKUP_TABLE[push_MATCH_index]             <= 1'b1;
                           ID_TABLE[push_MATCH_index][fetch_ID_BIN_i] <= 1'b1;
                       end
                end
                else // There is no matching addresses in the FIFO, push in the first available slot
                begin  
                       if(FIFO_full == 1'b0)
                       begin
                             casex(LOOKUP_TABLE)

                             16'bxxxxxxxx_xxxxxxx0 :
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       LOOKUP_TABLE[0]              <= 1'b1;
                                       ID_TABLE[0][fetch_ID_BIN_i]  <= 1'b1;
                                       ADDR_TABLE[0]                <= {fetch_way_i,fetch_addr_i};
                                     end
                             end

                             16'bxxxxxxxx_xxxxxx01 : 
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       LOOKUP_TABLE[1]              <= 1'b1;
                                       ID_TABLE[1][fetch_ID_BIN_i]  <= 1'b1;
                                       ADDR_TABLE[1]                <= {fetch_way_i,fetch_addr_i};
                                     end
                             end

                             16'bxxxxxxxx_xxxxx011 :
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       LOOKUP_TABLE[2]              <= 1'b1;
                                       ID_TABLE[2][fetch_ID_BIN_i]  <= 1'b1;
                                       ADDR_TABLE[2]                <= {fetch_way_i,fetch_addr_i};
                                     end
                             end

                             16'bxxxxxxxx_xxxx0111 : 
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       LOOKUP_TABLE[3]              <= 1'b1;
                                       ID_TABLE[3][fetch_ID_BIN_i]  <= 1'b1;
                                       ADDR_TABLE[3]                <= {fetch_way_i,fetch_addr_i};
                                     end
                             end

                             16'bxxxxxxxx_xxx01111 : 
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       LOOKUP_TABLE[4]              <= 1'b1;
                                       ID_TABLE[4][fetch_ID_BIN_i]  <= 1'b1;
                                       ADDR_TABLE[4]                <= {fetch_way_i,fetch_addr_i};
                                     end
                             end

                             16'bxxxxxxxx_xx011111 : 
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       LOOKUP_TABLE[5]              <= 1'b1;
                                       ID_TABLE[5][fetch_ID_BIN_i]  <= 1'b1;
                                       ADDR_TABLE[5]                <= {fetch_way_i,fetch_addr_i};
                                     end
                             end

                             16'bxxxxxxxx_x0111111 : 
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       LOOKUP_TABLE[6]              <= 1'b1;
                                       ID_TABLE[6][fetch_ID_BIN_i]  <= 1'b1;
                                       ADDR_TABLE[6]                <= {fetch_way_i,fetch_addr_i};
                                     end
                             end

                             16'bxxxxxxxx_01111111 : 
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       LOOKUP_TABLE[7]              <= 1'b1;
                                       ID_TABLE[7][fetch_ID_BIN_i]  <= 1'b1;
                                       ADDR_TABLE[7]                <= {fetch_way_i,fetch_addr_i};
                                     end
                             end

                             16'bxxxxxxx0_11111111 :
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       LOOKUP_TABLE[8]              <= 1'b1;
                                       ID_TABLE[8][fetch_ID_BIN_i]  <= 1'b1;
                                       ADDR_TABLE[8]                <= {fetch_way_i,fetch_addr_i};
                                     end
                             end

                             16'bxxxxxx01_11111111 : 
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       LOOKUP_TABLE[9]              <= 1'b1;
                                       ID_TABLE[9][fetch_ID_BIN_i]  <= 1'b1;
                                       ADDR_TABLE[9]                <= {fetch_way_i,fetch_addr_i};
                                     end
                             end

                             16'bxxxxx011_11111111 :
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       LOOKUP_TABLE[10]              <= 1'b1;
                                       ID_TABLE[10][fetch_ID_BIN_i]  <= 1'b1;
                                       ADDR_TABLE[10]                <= {fetch_way_i,fetch_addr_i};
                                     end
                             end

                             16'bxxxx0111_11111111 : 
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       LOOKUP_TABLE[11]              <= 1'b1;
                                       ID_TABLE[11][fetch_ID_BIN_i]  <= 1'b1;
                                       ADDR_TABLE[11]                <= {fetch_way_i,fetch_addr_i};
                                     end
                             end

                             16'bxxx01111_11111111 : 
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       LOOKUP_TABLE[12]              <= 1'b1;
                                       ID_TABLE[12][fetch_ID_BIN_i]  <= 1'b1;
                                       ADDR_TABLE[12]                <= {fetch_way_i,fetch_addr_i};
                                     end
                             end

                             16'bxx011111_11111111 : 
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       LOOKUP_TABLE[13]              <= 1'b1;
                                       ID_TABLE[13][fetch_ID_BIN_i]  <= 1'b1;
                                       ADDR_TABLE[13]                <= {fetch_way_i,fetch_addr_i};
                                     end
                             end

                             16'bx0111111_11111111 : 
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       LOOKUP_TABLE[14]              <= 1'b1;
                                       ID_TABLE[14][fetch_ID_BIN_i]  <= 1'b1;
                                       ADDR_TABLE[14]                <= {fetch_way_i,fetch_addr_i};
                                     end
                             end

                             16'b01111111_11111111 : 
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       LOOKUP_TABLE[15]              <= 1'b1;
                                       ID_TABLE[15][fetch_ID_BIN_i]  <= 1'b1;
                                       ADDR_TABLE[15]                <= {fetch_way_i,fetch_addr_i};
                                     end
                             end

                             16'b11111111_11111111 : 
                             begin
                                         //LOOKUP_TABLE[11][4] <= 1'b1;
                             end
                             endcase
                       end
                end
                //CODE END
            end
        end
    end




    always_comb
    begin

            AXI_addr_o  = fetch_addr_i & 32'hFFFF_FFF0;
            AXI_ID_o    = '0;
            AXI_req_o   = 1'b0;

            if( (last_refill_valid == 1'b1) && ( last_refill_addr[ADDR_CHECK_MSB:ADDR_CHECK_LSB] == fetch_addr_i[ADDR_CHECK_MSB:ADDR_CHECK_LSB] ) ) 
            begin
                AXI_req_o = 1'b0;
                fetch_gnt_o = 1'b1;
                AXI_ID_o    = '0;
            end
            else
            begin

                if(|check_push_Match_addr)
                begin
                       fetch_gnt_o  = 1'b1;

                       if(fetch_req_i)
                       begin
                            AXI_req_o = 1'b0;
                            AXI_ID_o  = '0;
                       end
                end
                else
                begin

                       AXI_req_o     = ~FIFO_full & fetch_req_i;
                       fetch_gnt_o   = ~FIFO_full & AXI_gnt_i;

                       if(FIFO_full == 1'b0)
                       begin
                             casex(LOOKUP_TABLE)

                             16'bxxxxxxxx_xxxxxxx0 :
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       AXI_ID_o                      = 0;
                                     end
                             end

                             16'bxxxxxxxx_xxxxxx01 : 
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       AXI_ID_o                      = 1;
                                     end
                             end

                             16'bxxxxxxxx_xxxxx011 :
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       AXI_ID_o                      = 2;
                                     end
                             end

                             16'bxxxxxxxx_xxxx_0111 : 
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       AXI_ID_o                      = 3;
                                     end
                             end

                             16'bxxxxxxxx_xxx0_1111 :
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       AXI_ID_o                      = 4;
                                     end
                             end

                             16'bxxxxxxxx_xx01_1111 : 
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       AXI_ID_o                      = 5;
                                     end
                             end

                             16'bxxxxxxxx_x011_1111 :
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       AXI_ID_o                      = 6;
                                     end
                             end

                             16'bxxxx_xxxx_0111_1111 : 
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       AXI_ID_o                      = 7;
                                     end
                             end


                             16'bxxxx_xxx0_1111_1111 :
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       AXI_ID_o                      = 8;
                                     end
                             end

                             16'bxxxx_xx01_1111_1111 : 
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       AXI_ID_o                      = 9;
                                     end
                             end

                             16'bxxxx_x011_1111_1111 :
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       AXI_ID_o                      = 10;
                                     end
                             end

                             16'bxxxx_0111_1111_1111 : 
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       AXI_ID_o                      = 11;
                                     end
                             end

                             16'bxxx0_1111_1111_1111 :
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       AXI_ID_o                      = 12;
                                     end
                             end

                             16'bxx01_1111_1111_1111 : 
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       AXI_ID_o                      = 13;
                                     end
                             end

                             16'bx011_1111_1111_1111 :
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       AXI_ID_o                      = 14;
                                     end
                             end

                             16'b0111_1111_1111_1111 : 
                             begin
                                     if(fetch_req_i & AXI_gnt_i)
                                     begin
                                       AXI_ID_o                      = 15;
                                     end
                             end


                             default : 
                             begin
                                         AXI_ID_o = 0;
                             end
                             endcase
                       end
                       else
                       begin
                            AXI_ID_o = '0;
                       end

                end
            end

    end



    onehot_to_bin #( .ONEHOT_WIDTH(DEPTH) ) OH_2_BIN_PUSH  ( .onehot(check_push_Match_addr), .bin(push_MATCH_index) );

   always_comb
   begin
      for(k=0; k<DEPTH; k++)
      begin
         if({LOOKUP_TABLE[k],ADDR_TABLE[k][ADDR_CHECK_MSB:ADDR_CHECK_LSB]} == {1'b1,fetch_addr_i[ADDR_CHECK_MSB:ADDR_CHECK_LSB]})
         begin
            check_push_Match_addr[k] = 1'b1;
         end
         else
         begin
            check_push_Match_addr[k] = 1'b0;
         end
      end
   end

endmodule
