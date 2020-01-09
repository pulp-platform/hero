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
    parameter EXT_TID_WIDTH = 4
    )
   (
    input   logic                       clk_i,
    input   logic	                rst_ni,
    
    output  logic	                valid_tid_o,
    output  logic [EXT_TID_WIDTH-1:0]	tid_o,
    
    input   logic	                incr_i,
    
    input   logic [EXT_TID_WIDTH-1:0]	tid_i,
    input   logic                       release_tid_i
    );
   
   localparam NB_OUTSND_TRANS = 2**EXT_TID_WIDTH;
   
   integer 				i;
   
   logic [15:0] 			tid_table, s_tid;
   
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
	if(rst_ni == 1'b0)
	  begin
	     for(i=0; i<NB_OUTSND_TRANS; i++)
	       begin
		  tid_table[i] <= 1'b0;
	       end
	     for(i=NB_OUTSND_TRANS; i< 16; i++)
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
	       
	       16'bxxxx_xxxx_xxxx_xxx0 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[0] <= 1'b1;
		      end
		 end
	       
	       16'bxxxx_xxxx_xxxx_xx01 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[1]<= 1'b1;
		      end
		 end
	       
	       16'bxxxx_xxxx_xxxx_x011 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[2]<= 1'b1;
		      end
		 end
	       
	       16'bxxxx_xxxx_xxxx_0111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[3] <= 1'b1;
		      end
		 end
	       
	       16'bxxxx_xxxx_xxx0_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[4] <= 1'b1;
		      end
		 end
	       
	       16'bxxxx_xxxx_xx01_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[5] <= 1'b1;
		      end
		 end
	       
	       16'bxxxx_xxxx_x011_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[6] <= 1'b1;
		      end
		 end
	       
	       16'bxxxx_xxxx_0111_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[7] <= 1'b1;
		      end
		 end
	       
	       16'bxxxx_xxx0_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[8] <= 1'b1;
		      end
		 end
	       
	       16'bxxxx_xx01_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[9] <= 1'b1;
		      end
		 end
	       
	       16'bxxxx_x011_1111_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[10] <= 1'b1;
		      end
		 end
	       
	       16'bxxxx_0111_1111_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[11] <= 1'b1;
		      end
		 end
	       
	       16'bxxx0_1111_1111_1111 :
		 begin
		    if(incr_i)
		      begin
			 tid_table[12] <= 1'b1;
		      end
		 end
	       
	       16'bxx01_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[13] <= 1'b1;
		      end
		 end
	       
	       16'bx011_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[14] <= 1'b1;
		      end
		 end	  
	       
	       16'b0111_1111_1111_1111 : 
		 begin
		    if(incr_i)
		      begin
			 tid_table[15] <= 1'b1;
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
	  
	  16'bxxxx_xxxx_xxxx_xxx0 : 
	    begin
	       s_tid            = 0;
	       valid_tid_o      = 1'b1;
	    end
	  
	  16'bxxxx_xxxx_xxxx_xx01 : 
	    begin
	       s_tid            = 1;
	       valid_tid_o      = 1'b1;
	    end	  
	  
	  16'bxxxx_xxxx_xxxx_x011 : 
	    begin
	       s_tid            = 2;
	       valid_tid_o      = 1'b1;
	    end	  
	  
	  16'bxxxx_xxxx_xxxx_0111 : 
	    begin
	       s_tid            = 3;
	       valid_tid_o      = 1'b1;
	    end
	  
	  16'bxxxx_xxxx_xxx0_1111 : 
	    begin
	       s_tid            = 4;
	       valid_tid_o      = 1'b1;
	    end
	  
	  16'bxxxx_xxxx_xx01_1111 : 
	    begin
	       s_tid            = 5;
	       valid_tid_o      = 1'b1;
	    end	  
	  
	  16'bxxxx_xxxx_x011_1111 : 
	    begin
	       s_tid            = 6;
	       valid_tid_o      = 1'b1;
	    end
	  
	  16'bxxxx_xxxx_0111_1111 : 
	    begin
	       s_tid            = 7;
	       valid_tid_o      = 1'b1;
	    end
	  
	  16'bxxxx_xxx0_1111_1111 : 
	    begin
	       s_tid            = 8;
	       valid_tid_o      = 1'b1;
	    end
	  
	  16'bxxxx_xx01_1111_1111 : 
	    begin
	       s_tid            = 9;
	       valid_tid_o      = 1'b1;
	    end
	  
	  16'bxxxx_x011_1111_1111 :
	    begin
	       s_tid            = 10;
	       valid_tid_o      = 1'b1;
	    end
	  
	  16'bxxxx_0111_1111_1111 :
	    begin
	       s_tid            = 11;
	       valid_tid_o      = 1'b1;
	    end
	  
	  16'bxxx0_1111_1111_1111 :
	    begin
	       s_tid            = 12;
	       valid_tid_o      = 1'b1;
	    end
	  
	  16'bxx01_1111_1111_1111 :
	    begin
	       s_tid            = 13;
	       valid_tid_o      = 1'b1;
	    end
	  
	  16'bx011_1111_1111_1111 :
	    begin
	       s_tid            = 14;
	       valid_tid_o      = 1'b1;
	    end
	  
	  16'b0111_1111_1111_1111 :
	    begin
	       s_tid            = 15;
	       valid_tid_o      = 1'b1;
	    end
	  
	  default :
	    begin
	       s_tid            = 4'b0000;
	       valid_tid_o      = 1'b0;
	    end
	  
	endcase
	
     end
   
   assign tid_o = s_tid[EXT_TID_WIDTH-1:0];
   
endmodule
