/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   17.8.2018
 *
 * Description: Contains Snitch's AXI ports, does not contain user ports
 */

`include "axi/typedef.svh"

package snitch_axi_pkg;

    localparam UserWidth = 1;
    localparam AddrWidth = 64;
    localparam DataWidth = 64;
    localparam StrbWidth = DataWidth / 8;

    typedef logic [snitch_pkg::IdWidth-1:0]      id_t;
    typedef logic [snitch_pkg::IdWidthSlave-1:0] id_slv_t;
    typedef logic [AddrWidth-1:0] addr_t;
    typedef logic [DataWidth-1:0] data_t;
    typedef logic [StrbWidth-1:0] strb_t;
    typedef logic [UserWidth-1:0] user_t;

    // DMA interface
    localparam DMAUserWidth = 1;
    localparam DMAAddrWidth = snitch_pkg::DmaAddrWidth;
    localparam DMADataWidth = snitch_pkg::DmaDataWidth;
    localparam DMAStrbWidth = DMADataWidth / 8;

    typedef logic [snitch_pkg::IdWidthDma-1:0]       id_dma_t;
    typedef logic [snitch_pkg::IdWidthDmaSlave-1:0]  id_dma_slv_t;
    typedef logic [DMAAddrWidth-1:0] addr_dma_t;
    typedef logic [DMADataWidth-1:0] data_dma_t;
    typedef logic [DMAStrbWidth-1:0] strb_dma_t;
    typedef logic [DMAUserWidth-1:0] user_dma_t;

    `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
    `AXI_TYPEDEF_AW_CHAN_T(aw_chan_slv_t, addr_t, id_slv_t, user_t)
    `AXI_TYPEDEF_AW_CHAN_T(aw_chan_dma_t, addr_dma_t, id_dma_t, user_t)
    `AXI_TYPEDEF_AW_CHAN_T(aw_chan_dma_slv_t, addr_dma_t, id_dma_slv_t, user_t)

    `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
    `AXI_TYPEDEF_W_CHAN_T(w_chan_dma_t, data_dma_t, strb_dma_t, user_t)

    `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
    `AXI_TYPEDEF_B_CHAN_T(b_chan_slv_t, id_slv_t, user_t)
    `AXI_TYPEDEF_B_CHAN_T(b_chan_dma_t, id_dma_t, user_t)
    `AXI_TYPEDEF_B_CHAN_T(b_chan_dma_slv_t, id_dma_slv_t, user_t)

    `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
    `AXI_TYPEDEF_AR_CHAN_T(ar_chan_slv_t, addr_t, id_slv_t, user_t)
    `AXI_TYPEDEF_AR_CHAN_T(ar_chan_dma_t, addr_dma_t, id_dma_t, user_t)
    `AXI_TYPEDEF_AR_CHAN_T(ar_chan_dma_slv_t, addr_dma_t, id_dma_slv_t, user_t)

    `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
    `AXI_TYPEDEF_R_CHAN_T(r_chan_slv_t, data_t, id_slv_t, user_t)
    `AXI_TYPEDEF_R_CHAN_T(r_chan_dma_t, data_dma_t, id_dma_t, user_t)
    `AXI_TYPEDEF_R_CHAN_T(r_chan_dma_slv_t, data_dma_t, id_dma_slv_t, user_t)

    `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
    `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

    `AXI_TYPEDEF_REQ_T(req_slv_t, aw_chan_slv_t, w_chan_t, ar_chan_slv_t)
    `AXI_TYPEDEF_RESP_T(resp_slv_t, b_chan_slv_t, r_chan_slv_t)

    `AXI_TYPEDEF_REQ_T(req_dma_t, aw_chan_dma_t, w_chan_dma_t, ar_chan_dma_t)
    `AXI_TYPEDEF_RESP_T(resp_dma_t, b_chan_dma_t, r_chan_dma_t)

    `AXI_TYPEDEF_REQ_T(req_dma_slv_t, aw_chan_dma_slv_t, w_chan_dma_t, ar_chan_dma_slv_t)
    `AXI_TYPEDEF_RESP_T(resp_dma_slv_t, b_chan_dma_slv_t, r_chan_dma_slv_t)

endpackage
