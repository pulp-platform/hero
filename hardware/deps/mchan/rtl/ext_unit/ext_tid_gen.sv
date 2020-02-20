// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Davide Rossi <davide.rossi@unibo.it>

module ext_tid_gen
  #(
    parameter EXT_TID_WIDTH = 6
    )
   (
    input   logic                       clk_i,
    input   logic	                rst_ni,
    
    output  logic	                valid_tid_o,
    output  logic [EXT_TID_WIDTH-1:0]	tid_o,
    
    input   logic	               	incr_i,
    
    input   logic [EXT_TID_WIDTH-1:0]	tid_i,
    input   logic                       release_tid_i
    );
   
   localparam NB_OUTSND_TRANS = 2**EXT_TID_WIDTH;
   
   integer 				i;
   
   logic [63:0] 			tid_table, s_tid;
   
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
	if(rst_ni == 1'b0)
	  begin
	     for(i=0; i<NB_OUTSND_TRANS; i++)
	       begin
		  tid_table[i] <= 1'b0;
	       end
	     for(i=NB_OUTSND_TRANS; i< 64; i++)
	       begin
		  tid_table[i] <= 1'b1;
	       end
	  end
	else
	  begin
	     
	     if(release_tid_i)
	       tid_table[tid_i] <= 1'b0;
	     else;
	     
	     casex(tid_table)
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxx0 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[0] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xx01 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[1]<= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_x011 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[2]<= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_0111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[3] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxx0_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[4] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xx01_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[5] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_x011_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[6] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_0111_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[7] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxx0_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[8] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xx01_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[9] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_x011_1111_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[10] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_0111_1111_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[11] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxx0_1111_1111_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[12] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xx01_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[13] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_x011_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[14] <= 1'b1;
		      end
		 end	  
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_0111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[15] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxx0_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[16] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xx01_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[17] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_x011_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[18] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_0111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[19] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxx0_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[20] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xx01_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[21] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_x011_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[22] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_0111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[23] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxx0_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[24] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xx01_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[25] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_x011_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[26] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_0111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[27] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxx0_1111_1111_1111_1111_1111_1111_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[28] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xx01_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[29] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_x011_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[30] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_0111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[31] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxx0_1111_1111_1111_1111_1111_1111_1111_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[32] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xx01_1111_1111_1111_1111_1111_1111_1111_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[33]<= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_x011_1111_1111_1111_1111_1111_1111_1111_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[34]<= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_0111_1111_1111_1111_1111_1111_1111_1111_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[35] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxx0_1111_1111_1111_1111_1111_1111_1111_1111_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[36] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xx01_1111_1111_1111_1111_1111_1111_1111_1111_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[37] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_x011_1111_1111_1111_1111_1111_1111_1111_1111_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[38] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_0111_1111_1111_1111_1111_1111_1111_1111_1111_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[39] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxx0_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[40] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_xx01_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[41] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_x011_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[42] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxxx_0111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[43] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xxx0_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[44] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_xx01_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[45] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxxx_x011_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[46] <= 1'b1;
		      end
		 end	  
	       
	       64'bxxxx_xxxx_xxxx_xxxx_0111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[47] <= 1'b1;
		      end
		 end
	       
	       64'bxxxx_xxxx_xxxx_xxx0_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[48] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xxxx_xx01_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[49] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xxxx_x011_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[50] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xxxx_0111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[51] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xxx0_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[52] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_xx01_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[53] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_x011_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[54] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxxx_0111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[55] <= 1'b1;
		      end
		 end

	       64'bxxxx_xxx0_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[56] <= 1'b1;
		      end
		 end

	       64'bxxxx_xx01_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[57] <= 1'b1;
		      end
		 end

	       64'bxxxx_x011_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[58] <= 1'b1;
		      end
		 end

	       64'bxxxx_0111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[59] <= 1'b1;
		      end
		 end

	       64'bxxx0_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[60] <= 1'b1;
		      end
		 end

	       64'bxx01_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[61] <= 1'b1;
		      end
		 end

	       64'bx011_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[62] <= 1'b1;
		      end
		 end

	       64'b0111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[63] <= 1'b1;
		      end
		 end

	       default:
		 begin
		 end
	       
	     endcase
	     
	  end
     end
   
   always_comb
     begin
	casex(tid_table)
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxx0 : 
	    begin
	       s_tid            = 0;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xx01 : 
	    begin
	       s_tid            = 1;
	       valid_tid_o      = 1'b1;
	    end	  
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_x011 : 
	    begin
	       s_tid            = 2;
	       valid_tid_o      = 1'b1;
	    end	  
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_0111 : 
	    begin
	       s_tid            = 3;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxx0_1111 : 
	    begin
	       s_tid            = 4;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xx01_1111 : 
	    begin
	       s_tid            = 5;
	       valid_tid_o      = 1'b1;
	    end	  
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_x011_1111 : 
	    begin
	       s_tid            = 6;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_0111_1111 : 
	    begin
	       s_tid            = 7;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxx0_1111_1111 : 
	    begin
	       s_tid            = 8;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xx01_1111_1111 : 
	    begin
	       s_tid            = 9;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_x011_1111_1111 :
	    begin
	       s_tid            = 10;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_0111_1111_1111 :
	    begin
	       s_tid            = 11;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxx0_1111_1111_1111 :
	    begin
	       s_tid            = 12;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xx01_1111_1111_1111 :
	    begin
	       s_tid            = 13;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_x011_1111_1111_1111 :
	    begin
	       s_tid            = 14;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_0111_1111_1111_1111 :
	    begin
	       s_tid            = 15;
	       valid_tid_o      = 1'b1;
	    end

	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxx0_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 16;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xx01_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 17;
	       valid_tid_o      = 1'b1;
	    end	  
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_x011_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 18;
	       valid_tid_o      = 1'b1;
	    end	  
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_0111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 19;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxx0_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 20;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xx01_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 21;
	       valid_tid_o      = 1'b1;
	    end	  
	  
	  64'bxxxxx_xxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_x011_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 22;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_0111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 23;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxx0_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 24;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xx01_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 25;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_x011_1111_1111_1111_1111_1111_1111 :
	    begin
	       s_tid            = 26;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_0111_1111_1111_1111_1111_1111_1111 :
	    begin
	       s_tid            = 27;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxx0_1111_1111_1111_1111_1111_1111_1111 :
	    begin
	       s_tid            = 28;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xx01_1111_1111_1111_1111_1111_1111_1111 :
	    begin
	       s_tid            = 29;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_x011_1111_1111_1111_1111_1111_1111_1111 :
	    begin
	       s_tid            = 30;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_0111_1111_1111_1111_1111_1111_1111_1111 :
	    begin
	       s_tid            = 31;
	       valid_tid_o      = 1'b1;
	    end

	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxx0_1111_1111_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 32;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xx01_1111_1111_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 33;
	       valid_tid_o      = 1'b1;
	    end	  
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_x011_1111_1111_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 34;
	       valid_tid_o      = 1'b1;
	    end	  
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_0111_1111_1111_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 35;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxx0_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 36;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xx01_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 37;
	       valid_tid_o      = 1'b1;
	    end	  
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_x011_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 38;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxxx_0111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 39;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xxx0_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 40;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_xx01_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 41;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_x011_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 :
	    begin
	       s_tid            = 42;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxxx_0111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 :
	    begin
	       s_tid            = 43;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xxx0_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 :
	    begin
	       s_tid            = 44;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_xx01_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 :
	    begin
	       s_tid            = 45;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_x011_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 :
	    begin
	       s_tid            = 46;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xxxx_0111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 :
	    begin
	       s_tid            = 47;
	       valid_tid_o      = 1'b1;
	    end

	  64'bxxxx_xxxx_xxxx_xxx0_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 48;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxxx_xx01_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 49;
	       valid_tid_o      = 1'b1;
	    end	  
	  
	  64'bxxxx_xxxx_xxxx_x011_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 50;
	       valid_tid_o      = 1'b1;
	    end	  
	  
	  64'bxxxx_xxxx_xxxx_0111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 51;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xxx0_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 52;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_xx01_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 53;
	       valid_tid_o      = 1'b1;
	    end	  
	  
	  64'bxxxx_xxxx_x011_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 54;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxxx_0111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 55;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xxx0_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 56;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_xx01_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 : 
	    begin
	       s_tid            = 57;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_x011_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 :
	    begin
	       s_tid            = 58;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxxx_0111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 :
	    begin
	       s_tid            = 59;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxxx0_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 :
	    begin
	       s_tid            = 60;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bxx01_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 :
	    begin
	       s_tid            = 61;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'bx011_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 :
	    begin
	       s_tid            = 62;
	       valid_tid_o      = 1'b1;
	    end
	  
	  64'b0111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 :
	    begin
	       s_tid            = 63;
	       valid_tid_o      = 1'b1;
	    end

	  default :
	    begin
	       s_tid            = 6'b000000;
	       valid_tid_o      = 1'b0;
	    end
	  
	endcase
	
     end
   
   assign tid_o = s_tid[EXT_TID_WIDTH-1:0];
   
endmodule
