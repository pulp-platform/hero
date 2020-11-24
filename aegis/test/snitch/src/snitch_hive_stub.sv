/// This is a stub for the snitch hive
/// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
module snitch_hive #(
  parameter int unsigned CoreCount        = 4,
  parameter int unsigned ICacheSizeByte   = 1024 * CoreCount,
  parameter logic [31:0] BootAddr         = 32'h0,
  parameter bit          RVE              = 0,
  parameter bit          RVFD             = 1,
  parameter bit          RegisterOffload  = 1,
  parameter bit          RegisterTCDMReq  = 1
) (
  input  logic                       clk_i,
  input  logic                       rst_i,
  input  logic [31:0]                hive_id_i,
  // TCDM Ports
  output logic [CoreCount-1:0][1:0][31:0] data_qaddr_o,
  output logic [CoreCount-1:0][1:0]       data_qwrite_o,
  output logic [CoreCount-1:0][1:0][3:0]  data_qamo_o,
  output logic [CoreCount-1:0][1:0][63:0] data_qdata_o,
  output logic [CoreCount-1:0][1:0][7:0]  data_qstrb_o,
  output logic [CoreCount-1:0][1:0]       data_qvalid_o,
  input  logic [CoreCount-1:0][1:0]       data_qready_i,
  input  logic [CoreCount-1:0][1:0][63:0] data_pdata_i,
  input  logic [CoreCount-1:0][1:0]       data_perror_i,
  input  logic [CoreCount-1:0][1:0]       data_pvalid_i,
  output logic [CoreCount-1:0][1:0]       data_pready_o,
  // I-Cache refill interface
  output logic [31:0]                refill_qaddr_o,
  output logic [7:0]                 refill_qlen_o,
  output logic                       refill_qvalid_o,
  input  logic                       refill_qready_i,
  input  logic [31:0]                refill_pdata_i,
  input  logic                       refill_perror_i,
  input  logic                       refill_pvalid_i,
  input  logic                       refill_plast_i,
  output logic                       refill_pready_o
);


endmodule