// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module event_unit_interface_mux
#(
  parameter NB_CORES       = 4,
  parameter NB_BARR        = NB_CORES/2,
  parameter PER_ID_WIDTH   = NB_CORES+1
)
(
  // clock and reset
  input  logic              clk_i,
  input  logic              rst_ni,

  // slave port from periph interconnect, decode requests
  XBAR_PERIPH_BUS.Slave     speriph_slave,
  XBAR_PERIPH_BUS.Master    periph_int_bus_master[NB_CORES+NB_BARR+2:0],

  // demuxed slave ports from each core, redistribute to eu_core and barrier units
  XBAR_PERIPH_BUS.Slave     demux_slave[NB_CORES-1:0],
  XBAR_PERIPH_BUS.Master    demux_int_bus_core_master[NB_CORES-1:0],
  XBAR_PERIPH_BUS.Master    demux_int_bus_barrier_master[NB_BARR-1:0]
);


  genvar I,J;

  localparam LOG_NB_CORES = $clog2(NB_CORES);
  localparam LOG_NB_BARR  = $clog2(NB_BARR);

  //*************************************************************//
  //                                                             //
  //       ██████╗ ███████╗███╗   ███╗██╗   ██╗██╗  ██╗          //
  //       ██╔══██╗██╔════╝████╗ ████║██║   ██║╚██╗██╔╝          //
  //       ██║  ██║█████╗  ██╔████╔██║██║   ██║ ╚███╔╝           //
  //       ██║  ██║██╔══╝  ██║╚██╔╝██║██║   ██║ ██╔██╗           //
  //       ██████╔╝███████╗██║ ╚═╝ ██║╚██████╔╝██╔╝ ██╗          //
  //       ╚═════╝ ╚══════╝╚═╝     ╚═╝ ╚═════╝ ╚═╝  ╚═╝          //
  //                                                             //
  //*************************************************************//


  // response channel for demux plug
  logic [NB_CORES-1:0]                  demux_ip_sel_SP;
  logic [NB_CORES-1:0][LOG_NB_BARR-1:0] demux_barr_sel_SP;
  logic [NB_CORES-1:0]                  demux_slave_req_del;
  logic [NB_CORES-1:0]                  demux_slave_update;
  logic [NB_CORES-1:0]                  demux_add_is_core;
  logic [NB_CORES-1:0]                  demux_slave_gnt_mux;
  logic [NB_CORES-1:0]                  demux_slave_gnt_mux_del;

  // helper arrays to work around sv dynamic bus index select limitation
  logic [NB_CORES-1:0]                  demux_slaves_core_req;
  
  logic [NB_CORES-1:0]                  demux_slave_wen;
  logic [NB_CORES-1:0][31:0]            demux_slave_add;
  logic [NB_CORES-1:0][31:0]            demux_slave_wdata;
  logic [NB_CORES-1:0]                  demux_slave_rvalid_barr;

  logic [NB_BARR-1:0][31:0]             demux_int_bus_barrier_master_r_rdata;
  logic [NB_CORES-1:0][NB_BARR-1:0]     demux_slv_bar_req_int;
  logic [NB_BARR-1:0][NB_CORES-1:0]     demux_slv_bar_req_int_transp;

  logic [NB_BARR-1:0][LOG_NB_CORES-1:0] barr_arb_sel;
  logic [NB_BARR-1:0][LOG_NB_CORES-1:0] barr_arb_ff1;
  logic [NB_BARR-1:0]                   barr_arb_no1;

  logic [NB_CORES-1:0][NB_BARR-1:0]     demux_slave_gnt_barr;
  logic [NB_CORES-1:0][LOG_NB_BARR-1:0] demux_slave_gnt_barr_bin;

  generate
    for ( I = 0; I < NB_CORES; I++ ) begin
      // slave->master: output ports to cores
      assign demux_slave[I].gnt   = demux_slave_gnt_mux[I];
      assign demux_slave[I].r_opc = 1'b0;
      assign demux_slave[I].r_id  = '0;
      // activation condition for responses on each demux plug
      assign demux_slave_update[I] = ( (demux_slave[I].req & ~demux_slave_req_del[I]) ||
                                       (~demux_slave[I].req & demux_slave_req_del[I]) ||
                                       (demux_slave[I].req & demux_slave_gnt_mux[I])  ||
                                       (demux_slave_req_del[I] & demux_slave_gnt_mux_del[I]));
      // check if Core I wants to access its private event_unit_core
      assign demux_add_is_core[I]  = ( ( demux_slave[I].add[9] == 1'b0 )                             ||   // some core reg
                                       ({demux_slave[I].add[9],demux_slave[I].add[4:2]} == 4'b1_101) ||   // barrier_trigg_self
                                       ({demux_slave[I].add[9],demux_slave[I].add[4:2]} == 4'b1_110) ||   // barrier_trigg_wait
                                       ({demux_slave[I].add[9],demux_slave[I].add[4:2]} == 4'b1_111)   ); // barrier_trigg_wait_clear
    end
  endgenerate

  generate
    for ( I = 0; I < NB_CORES; I++ ) begin
      // master->slave
      assign demux_int_bus_core_master[I].req    = demux_slaves_core_req[I];
      assign demux_int_bus_core_master[I].add    = demux_slave[I].add;
      assign demux_int_bus_core_master[I].wen    = demux_slave[I].wen;
      assign demux_int_bus_core_master[I].wdata  = demux_slave[I].wdata;

      assign demux_int_bus_core_master[I].id     = '0;
      assign demux_int_bus_core_master[I].be     = '0;
    end
  endgenerate

  generate
    for ( J = 0; J < NB_BARR; J++ ) begin
      
      // REQ generation
      for ( I = 0; I < NB_CORES; I++ ) assign demux_slv_bar_req_int_transp[J][I] = demux_slv_bar_req_int[I][J];

      ff1_loop #(
        .WIDTH(NB_CORES) )
      ff1_loop_i (
        .vector_i   ( demux_slv_bar_req_int_transp[J] ),
        .idx_bin_o  ( barr_arb_ff1[J] ),
        .no1_o      ( barr_arb_no1[J] )
      );

      assign barr_arb_sel[J] = barr_arb_no1[J] ? '0 : barr_arb_ff1[J];
      
      assign demux_int_bus_barrier_master[J].req    = ~barr_arb_no1[J];
      assign demux_int_bus_barrier_master[J].wen    = demux_slave_wen[barr_arb_sel[J]];
      assign demux_int_bus_barrier_master[J].add    = demux_slave_add[barr_arb_sel[J]];
      assign demux_int_bus_barrier_master[J].wdata  = demux_slave_wdata[barr_arb_sel[J]];
      assign demux_int_bus_barrier_master[J].id     = '0;
      assign demux_int_bus_barrier_master[J].be     = '0;

      // RESPONSE generation
      assign demux_int_bus_barrier_master_r_rdata[J] = demux_int_bus_barrier_master[J].r_rdata;

      //always_comb begin
        //for (int i=0; i<NB_CORES; i++) demux_slave_gnt_barr[i][J] = 1'b0;
        //if (~barr_arb_no1[J]) demux_slave_gnt_barr[barr_arb_ff1[J]][J] = 1'b1;
      //end

      for ( I = 0; I < NB_CORES; I++ ) assign demux_slave_gnt_barr[I][J] = (~barr_arb_no1[J]) && (barr_arb_ff1[J] == I);
      
    end
  endgenerate
  
  generate
    for ( I = 0; I < NB_CORES; I++ ) begin

      // make bus arrays slice selectable
      assign demux_slave_wen[I]   = demux_slave[I].wen;
      assign demux_slave_add[I]   = demux_slave[I].add;
      assign demux_slave_wdata[I] = demux_slave[I].wdata;

      // decoding of IP select part of address in case of request, selection of correct gnt
      always_comb begin

        demux_slv_bar_req_int[I] = '0;
  
        demux_slaves_core_req[I] = 1'b0;
        demux_slave_gnt_mux[I]   = 1'b0;

        if ( demux_slave[I].req ) begin
          // send request to private core unit, mux gnt back
          if ( demux_add_is_core[I] ) begin
            demux_slaves_core_req[I] = 1'b1;
            demux_slave_gnt_mux[I]   = demux_int_bus_core_master[I].gnt;
          end
          // send request to correct barrier unit, mux gnt back
          else begin
            demux_slv_bar_req_int[I][demux_slave[I].add[8:5]] = 1'b1;
            demux_slave_gnt_mux[I] = |demux_slave_gnt_barr[I];
          end
        end
      end

      // delayed muxing of correct response
      always_comb begin
    
        // default: silence response channel
        demux_slave[I].r_valid = 1'b0;
        demux_slave[I].r_rdata = '0;
    
        if ( demux_slave_req_del[I] ) begin
          if ( ~demux_ip_sel_SP[I] ) begin
            demux_slave[I].r_valid = demux_int_bus_core_master[I].r_valid;
            demux_slave[I].r_rdata = demux_int_bus_core_master[I].r_rdata;
          end
          else begin
            demux_slave[I].r_valid = demux_slave_rvalid_barr[I];
            demux_slave[I].r_rdata = demux_int_bus_barrier_master_r_rdata[demux_barr_sel_SP[I]];
          end
        end
      end

      onehot_to_bin #(.ONEHOT_WIDTH(NB_BARR)) demux_barr_id_i (.onehot(demux_slave_gnt_barr[I]), .bin(demux_slave_gnt_barr_bin[I]));

      // delayed signals to compute correct response
      always_ff @(posedge clk_i, negedge rst_ni)
      begin
        if (~rst_ni)
        begin
          demux_slave_req_del[I] <= 1'b0;
          demux_slave_gnt_mux_del[I] <= 1'b0;

          demux_ip_sel_SP[I]     <= 1'b0;
          demux_barr_sel_SP[I]   <= '0;

          demux_slave_rvalid_barr[I] <= 1'b0;
        end
        else
        begin
          demux_slave_req_del[I] <= demux_slave[I].req;
          demux_slave_gnt_mux_del[I] <= demux_slave_gnt_mux[I];
          if ( demux_slave_update[I] ) begin
            demux_ip_sel_SP[I]    <= ~demux_add_is_core[I];
            demux_barr_sel_SP[I]  <= demux_slave_gnt_barr_bin[I];
            demux_slave_rvalid_barr[I] <= |demux_slave_gnt_barr[I];
          end
        end
      end
    end
  endgenerate


  //*************************************************************//
  //                                                             //
  //        ██╗███╗   ██╗████████╗███████╗██████╗  ██████╗       //
  //        ██║████╗  ██║╚══██╔══╝██╔════╝██╔══██╗██╔════╝       //
  //        ██║██╔██╗ ██║   ██║   █████╗  ██████╔╝██║            //
  //        ██║██║╚██╗██║   ██║   ██╔══╝  ██╔══██╗██║            //
  //        ██║██║ ╚████║   ██║   ███████╗██║  ██║╚██████╗       //
  //        ╚═╝╚═╝  ╚═══╝   ╚═╝   ╚══════╝╚═╝  ╚═╝ ╚═════╝       //
  //                                                             //
  //*************************************************************//

  // response channel for interconnect plug
  logic [5:0] interc_ip_sel_SP, interc_ip_sel_SN;
  logic       speriph_slave_req_del;
  logic       speriph_slave_update;
  logic       speriph_slave_gnt_mux;
  logic       speriph_slave_gnt_mux_del;

  logic [NB_CORES+NB_BARR+2:0] interc_slaves_req;

  // helper arrays to work around sv dynamic bus index select limitation
  logic [NB_CORES-1:0][31:0] periph_int_bus_core_rdata;
  logic [NB_BARR-1:0][31:0]  periph_int_bus_barr_rdata;
  logic [NB_CORES-1:0]       periph_int_bus_core_rvalid;
  logic [NB_BARR-1:0]        periph_int_bus_barr_rvalid;
  logic [NB_CORES-1:0]       periph_int_bus_core_gnt;
  logic [NB_BARR-1:0]        periph_int_bus_barr_gnt;

  assign interc_ip_sel_SN = speriph_slave.add[10:5];

  // activation condition for speriph slave responses
  assign speriph_slave_update = ( (speriph_slave.req & ~speriph_slave_req_del) ||
                                  (~speriph_slave.req & speriph_slave_req_del) ||
                                  (speriph_slave.req & speriph_slave_gnt_mux)  ||
                                  (speriph_slave_req_del & speriph_slave_gnt_mux_del));

  // broadcast master->slave signals with exception of req
  generate
    for ( I = 0; I < NB_CORES+NB_BARR+3; I++ ) begin
      assign periph_int_bus_master[I].wdata = speriph_slave.wdata;
      assign periph_int_bus_master[I].add   = speriph_slave.add;
      assign periph_int_bus_master[I].wen   = speriph_slave.wen;
      assign periph_int_bus_master[I].be    = '1;
      assign periph_int_bus_master[I].id    = '0;
      assign periph_int_bus_master[I].req   = interc_slaves_req[I];
    end
  endgenerate

  // assign slave->master signals
  generate
    for ( I = 0; I < NB_CORES; I++ ) begin
      assign periph_int_bus_core_rdata[I]  = periph_int_bus_master[I].r_rdata;
      assign periph_int_bus_core_rvalid[I] = periph_int_bus_master[I].r_valid;
      assign periph_int_bus_core_gnt[I]    = periph_int_bus_master[I].gnt;
    end
    for ( I = 0; I < NB_BARR; I++ ) begin
      assign periph_int_bus_barr_rdata[I]  = periph_int_bus_master[NB_CORES+I].r_rdata;
      assign periph_int_bus_barr_rvalid[I] = periph_int_bus_master[NB_CORES+I].r_valid;
      assign periph_int_bus_barr_gnt[I]    = periph_int_bus_master[NB_CORES+I].gnt;
    end
  endgenerate

  // assign muxed slave->master gnt
  assign speriph_slave.gnt   = speriph_slave_gnt_mux;
  assign speriph_slave.r_opc = 1'b0;

  // decoding of IP select part of address in case of request, selection of correct gnt
  always_comb begin
    interc_slaves_req     = '0;
    speriph_slave_gnt_mux = 1'b0;

    if ( speriph_slave.req ) begin
      casex ( speriph_slave.add[10:7] )
        4'b0???: begin  // core units - each 0x40 (16 regs) long, [9:6] decides about which unit
          interc_slaves_req[speriph_slave.add[9:6]] = 1'b1;
          speriph_slave_gnt_mux = periph_int_bus_core_gnt[speriph_slave.add[9:6]];
        end
        4'b10??: begin  // hw barrier - each 0x20 (8 regs) long, [8:5] decides about which unit
          interc_slaves_req[NB_CORES+speriph_slave.add[8:5]] = 1'b1;
          speriph_slave_gnt_mux = periph_int_bus_barr_gnt[speriph_slave.add[8:5]];
        end
        4'b110?: begin // external sw event triggering
          interc_slaves_req[NB_CORES+NB_BARR] = 1'b1;
          speriph_slave_gnt_mux = periph_int_bus_master[NB_CORES+NB_BARR].gnt;
        end
        4'b1110: begin // soc event FIFO
          interc_slaves_req[NB_CORES+NB_BARR+1] = 1'b1;
          speriph_slave_gnt_mux = periph_int_bus_master[NB_CORES+NB_BARR+1].gnt;
        end
        4'b1111: begin // inter-cluster FIFOs
          interc_slaves_req[NB_CORES+NB_BARR+2] = 1'b1;
          speriph_slave_gnt_mux = periph_int_bus_master[NB_CORES+NB_BARR+2].gnt;
        end
      endcase
    end
  end

  // delayed muxing of correct response
  always_comb begin

    // default: silence response channel
    speriph_slave.r_valid = 1'b0;
    speriph_slave.r_rdata = '0;

    if ( speriph_slave_req_del ) begin
      casex ( interc_ip_sel_SP[5:2] )
        4'b0???: begin // core units
          speriph_slave.r_valid = periph_int_bus_core_rvalid[interc_ip_sel_SP[4:1]];
          speriph_slave.r_rdata = periph_int_bus_core_rdata[interc_ip_sel_SP[4:1]];
        end
        4'b10??: begin // barrier units
          speriph_slave.r_valid = periph_int_bus_barr_rvalid[interc_ip_sel_SP[3:0]];
          speriph_slave.r_rdata = periph_int_bus_barr_rdata[interc_ip_sel_SP[3:0]];
        end
        4'b110?: begin // external sw event trigger
          speriph_slave.r_valid = periph_int_bus_master[NB_CORES+NB_BARR].r_valid;
          speriph_slave.r_rdata = periph_int_bus_master[NB_CORES+NB_BARR].r_rdata;
        end
        4'b1110: begin // soc event FIFO
          speriph_slave.r_valid = periph_int_bus_master[NB_CORES+NB_BARR+1].r_valid;
          speriph_slave.r_rdata = periph_int_bus_master[NB_CORES+NB_BARR+1].r_rdata;
        end
        4'b1111: begin // inter-cluster FIFOs
          speriph_slave.r_valid = periph_int_bus_master[NB_CORES+NB_BARR+2].r_valid;
          speriph_slave.r_rdata = periph_int_bus_master[NB_CORES+NB_BARR+2].r_rdata;
        end
        default: begin
          speriph_slave.r_valid = 1'b0;
          speriph_slave.r_rdata = '0;
        end
      endcase
    end

  end

  // delay for interconnect signals
  always_ff @(posedge clk_i, negedge rst_ni)
  begin
    if (~rst_ni) begin
      speriph_slave.r_id    <= '0;
      interc_ip_sel_SP      <= '0;
      speriph_slave_req_del <= 1'b0;
      speriph_slave_gnt_mux_del <= 1'b0;
    end
    else
    begin
      speriph_slave_req_del <= speriph_slave.req;
      speriph_slave_gnt_mux_del <= speriph_slave_gnt_mux;
      if ( speriph_slave_update )
      begin
        speriph_slave.r_id <= speriph_slave.id;
        interc_ip_sel_SP   <= interc_ip_sel_SN;
      end
    end
  end

endmodule // event_unit_interface_mux
