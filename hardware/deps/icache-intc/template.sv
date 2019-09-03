// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
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
// Design Name:    icache_intc                                                //
// Module Name:    template.sv                                                //
// Project Name:   MrWolf                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Template used to instantiate the read-only interconnect    //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - 16/02/2018 : File Created                                  //
// Additional Comments:                                                       //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

   icache_intc 
   #(
      .ADDRESS_WIDTH  (   ),
      .N_CORES        (   ),
      .N_AUX_CHANNEL  (   ),
      .UID_WIDTH      (   ),
      .DATA_WIDTH     (   ),
      .N_CACHE_BANKS  (   )
   )
   icache_intc_i
   (
      .clk_i          (   ),
      .rst_ni         (   ),

      .request_i      (   ),
      .address_i      (   ),
      .grant_o        (   ),
      .response_o     (   ),
      .read_data_o    (   ),

      .request_o      (   ),
      .address_o      (   ),
      .UID_o          (   ),
      .grant_i        (   ),

      .read_data_i    (   ),
      .response_i     (   ),
      .response_UID_i (   )
   );

