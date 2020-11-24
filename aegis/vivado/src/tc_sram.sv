// XPM_MEMORY instantiation template for Single Port RAM configurations
// Refer to the targeted device family architecture libraries guide for XPM_MEMORY documentation
// =======================================================================================================================

// Parameter usage table, organized as follows:
// +---------------------------------------------------------------------------------------------------------------------+
// | Parameter name       | Data type          | Restrictions, if applicable                                             |
// |---------------------------------------------------------------------------------------------------------------------|
// | Description                                                                                                         |
// +---------------------------------------------------------------------------------------------------------------------+
// +---------------------------------------------------------------------------------------------------------------------+
// | ADDR_WIDTH_A         | Integer            | Range: 1 - 20. Default value = 6.                                       |
// |---------------------------------------------------------------------------------------------------------------------|
// | Specify the width of the port A address port addra, in bits.                                                        |
// | Must be large enough to access the entire memory from port A, i.e. = $clog2(MEMORY_SIZE/[WRITE|READ]_DATA_WIDTH_A). |
// +---------------------------------------------------------------------------------------------------------------------+
// | AUTO_SLEEP_TIME      | Integer            | Range: 0 - 15. Default value = 0.                                       |
// |---------------------------------------------------------------------------------------------------------------------|
// | Specify the number of clka cycles to auto-sleep, if feature is available in architecture.                           |
// |                                                                                                                     |
// | 0 - Disable auto-sleep feature                                                                                      |
// | 3-15 - Number of auto-sleep latency cycles                                                                          |
// |                                                                                                                     |
// | Do not change from the value provided in the template instantiation.                                                |
// +---------------------------------------------------------------------------------------------------------------------+
// | BYTE_WRITE_WIDTH_A   | Integer            | Range: 1 - 4608. Default value = 32.                                    |
// |---------------------------------------------------------------------------------------------------------------------|
// | To enable byte-wide writes on port A, specify the byte width, in bits.                                              |
// |                                                                                                                     |
// | 8- 8-bit byte-wide writes, legal when WRITE_DATA_WIDTH_A is an integer multiple of 8                                |
// | 9- 9-bit byte-wide writes, legal when WRITE_DATA_WIDTH_A is an integer multiple of 9                                |
// |                                                                                                                     |
// | Or to enable word-wide writes on port A, specify the same value as for WRITE_DATA_WIDTH_A.                          |
// +---------------------------------------------------------------------------------------------------------------------+
// | CASCADE_HEIGHT       | Integer            | Range: 0 - 64. Default value = 0.                                       |
// |---------------------------------------------------------------------------------------------------------------------|
// | 0- No Cascade Height, Allow Vivado Synthesis to choose.                                                             |
// | 1 or more - Vivado Synthesis sets the specified value as Cascade Height.                                            |
// +---------------------------------------------------------------------------------------------------------------------+
// | ECC_MODE             | String             | Allowed values: no_ecc, both_encode_and_decode, decode_only, encode_only. Default value = no_ecc.|
// |---------------------------------------------------------------------------------------------------------------------|
// |                                                                                                                     |
// |   "no_ecc" - Disables ECC                                                                                           |
// |   "encode_only" - Enables ECC Encoder only                                                                          |
// |   "decode_only" - Enables ECC Decoder only                                                                          |
// |   "both_encode_and_decode" - Enables both ECC Encoder and Decoder                                                   |
// +---------------------------------------------------------------------------------------------------------------------+
// | MEMORY_INIT_FILE     | String             | Default value = none.                                                   |
// |---------------------------------------------------------------------------------------------------------------------|
// | Specify "none" (including quotes) for no memory initialization, or specify the name of a memory initialization file-|
// | Enter only the name of the file with .mem extension, including quotes but without path (e.g. "my_file.mem").        |
// | File format must be ASCII and consist of only hexadecimal values organized into the specified depth by              |
// | narrowest data width generic value of the memory. See the Memory File (MEM) section for more                        |
// | information on the syntax. Initialization of memory happens through the file name specified only when parameter     |
// | MEMORY_INIT_PARAM value is equal to "".                                                                             |
// | When using XPM_MEMORY in a project, add the specified file to the Vivado project as a design source.                |
// +---------------------------------------------------------------------------------------------------------------------+
// | MEMORY_INIT_PARAM    | String             | Default value = 0.                                                      |
// |---------------------------------------------------------------------------------------------------------------------|
// | Specify "" or "0" (including quotes) for no memory initialization through parameter, or specify the string          |
// | containing the hex characters. Enter only hex characters with each location separated by delimiter (,).             |
// | Parameter format must be ASCII and consist of only hexadecimal values organized into the specified depth by         |
// | narrowest data width generic value of the memory.For example, if the narrowest data width is 8, and the depth of    |
// | memory is 8 locations, then the parameter value should be passed as shown below.                                    |
// | parameter MEMORY_INIT_PARAM = "AB,CD,EF,1,2,34,56,78"                                                               |
// | Where "AB" is the 0th location and "78" is the 7th location.                                                        |
// +---------------------------------------------------------------------------------------------------------------------+
// | MEMORY_OPTIMIZATION  | String             | Allowed values: true, false. Default value = true.                      |
// |---------------------------------------------------------------------------------------------------------------------|
// | Specify "true" to enable the optimization of unused memory or bits in the memory structure. Specify "false" to      |
// | disable the optimization of unused memory or bits in the memory structure.                                          |
// +---------------------------------------------------------------------------------------------------------------------+
// | MEMORY_PRIMITIVE     | String             | Allowed values: auto, block, distributed, ultra. Default value = auto.  |
// |---------------------------------------------------------------------------------------------------------------------|
// | Designate the memory primitive (resource type) to use.                                                              |
// |                                                                                                                     |
// |   "auto"- Allow Vivado Synthesis to choose                                                                          |
// |   "distributed"- Distributed memory                                                                                 |
// |   "block"- Block memory                                                                                             |
// |   "ultra"- Ultra RAM memory                                                                                         |
// |                                                                                                                     |
// | NOTE: There may be a behavior mismatch if Block RAM or Ultra RAM specific features, like ECC or Asymmetry, are selected with MEMORY_PRIMITIVE set to "auto".|
// +---------------------------------------------------------------------------------------------------------------------+
// | MEMORY_SIZE          | Integer            | Range: 2 - 150994944. Default value = 2048.                             |
// |---------------------------------------------------------------------------------------------------------------------|
// | Specify the total memory array size, in bits.                                                                       |
// | For example, enter 65536 for a 2kx32 RAM.                                                                           |
// |                                                                                                                     |
// |   When ECC is enabled and set to "encode_only", then the memory size has to be multiples of READ_DATA_WIDTH_A       |
// |   When ECC is enabled and set to "decode_only", then the memory size has to be multiples of WRITE_DATA_WIDTH_A      |
// +---------------------------------------------------------------------------------------------------------------------+
// | MESSAGE_CONTROL      | Integer            | Range: 0 - 1. Default value = 0.                                        |
// |---------------------------------------------------------------------------------------------------------------------|
// | Specify 1 to enable the dynamic message reporting such as collision warnings, and 0 to disable the message reporting|
// +---------------------------------------------------------------------------------------------------------------------+
// | READ_DATA_WIDTH_A    | Integer            | Range: 1 - 4608. Default value = 32.                                    |
// |---------------------------------------------------------------------------------------------------------------------|
// | Specify the width of the port A read data output port douta, in bits.                                               |
// | The values of READ_DATA_WIDTH_A and WRITE_DATA_WIDTH_A must be equal.                                               |
// | When ECC is enabled and set to "encode_only", then READ_DATA_WIDTH_A has to be multiples of 72-bits.                |
// | When ECC is enabled and set to "decode_only" or "both_encode_and_decode", then READ_DATA_WIDTH_A has to be          |
// | multiples of 64-bits.                                                                                               |
// +---------------------------------------------------------------------------------------------------------------------+
// | READ_LATENCY_A       | Integer            | Range: 0 - 100. Default value = 2.                                      |
// |---------------------------------------------------------------------------------------------------------------------|
// | Specify the number of register stages in the port A read data pipeline. Read data output to port douta takes this   |
// | number of clka cycles.                                                                                              |
// |                                                                                                                     |
// | To target block memory, a value of 1 or larger is required- 1 causes use of memory latch only; 2 causes use of      |
// | output register.                                                                                                    |
// | To target distributed memory, a value of 0 or larger is required- 0 indicates combinatorial output.                 |
// | Values larger than 2 synthesize additional flip-flops that are not retimed into memory primitives.                  |
// +---------------------------------------------------------------------------------------------------------------------+
// | READ_RESET_VALUE_A   | String             | Default value = 0.                                                      |
// |---------------------------------------------------------------------------------------------------------------------|
// | Specify the reset value of the port A final output register stage in response to rsta input port is assertion.      |
// | Since this parameter is a string, you must specify the hex values inside double quotes. For example,                |
// | If the read data width is 8, then specify READ_RESET_VALUE_A = "EA";                                                |
// | When ECC is enabled, then reset value is not supported.                                                             |
// +---------------------------------------------------------------------------------------------------------------------+
// | RST_MODE_A           | String             | Allowed values: SYNC, ASYNC. Default value = SYNC.                      |
// |---------------------------------------------------------------------------------------------------------------------|
// | Describes the behaviour of the reset                                                                                |
// |                                                                                                                     |
// |   "SYNC" - when reset is applied, synchronously resets output port douta to the value specified by parameter READ_RESET_VALUE_A|
// |   "ASYNC" - when reset is applied, asynchronously resets output port douta to zero                                  |
// +---------------------------------------------------------------------------------------------------------------------+
// | SIM_ASSERT_CHK       | Integer            | Range: 0 - 1. Default value = 0.                                        |
// |---------------------------------------------------------------------------------------------------------------------|
// | 0- Disable simulation message reporting. Messages related to potential misuse will not be reported.                 |
// | 1- Enable simulation message reporting. Messages related to potential misuse will be reported.                      |
// +---------------------------------------------------------------------------------------------------------------------+
// | USE_MEM_INIT         | Integer            | Range: 0 - 1. Default value = 1.                                        |
// |---------------------------------------------------------------------------------------------------------------------|
// | Specify 1 to enable the generation of below message and 0 to disable generation of the following message completely.|
// | "INFO - MEMORY_INIT_FILE and MEMORY_INIT_PARAM together specifies no memory initialization.                         |
// | Initial memory contents will be all 0s."                                                                            |
// | NOTE: This message gets generated only when there is no Memory Initialization specified either through file or      |
// | Parameter.                                                                                                          |
// +---------------------------------------------------------------------------------------------------------------------+
// | WAKEUP_TIME          | String             | Allowed values: disable_sleep, use_sleep_pin. Default value = disable_sleep.|
// |---------------------------------------------------------------------------------------------------------------------|
// | Specify "disable_sleep" to disable dynamic power saving option, and specify "use_sleep_pin" to enable the           |
// | dynamic power saving option                                                                                         |
// +---------------------------------------------------------------------------------------------------------------------+
// | WRITE_DATA_WIDTH_A   | Integer            | Range: 1 - 4608. Default value = 32.                                    |
// |---------------------------------------------------------------------------------------------------------------------|
// | Specify the width of the port A write data input port dina, in bits.                                                |
// | The values of WRITE_DATA_WIDTH_A and READ_DATA_WIDTH_A must be equal.                                               |
// | When ECC is enabled and set to "encode_only" or "both_encode_and_decode", then WRITE_DATA_WIDTH_A must be           |
// | multiples of 64-bits.                                                                                               |
// | When ECC is enabled and set to "decode_only", then WRITE_DATA_WIDTH_A must be multiples of 72-bits.                 |
// +---------------------------------------------------------------------------------------------------------------------+
// | WRITE_MODE_A         | String             | Allowed values: read_first, no_change, write_first. Default value = read_first.|
// |---------------------------------------------------------------------------------------------------------------------|
// | Write mode behavior for port A output data port, douta.                                                             |
// +---------------------------------------------------------------------------------------------------------------------+

// Port usage table, organized as follows:
// +---------------------------------------------------------------------------------------------------------------------+
// | Port name      | Direction | Size, in bits                         | Domain  | Sense       | Handling if unused     |
// |---------------------------------------------------------------------------------------------------------------------|
// | Description                                                                                                         |
// +---------------------------------------------------------------------------------------------------------------------+
// +---------------------------------------------------------------------------------------------------------------------+
// | addra          | Input     | ADDR_WIDTH_A                          | clka    | NA          | Required               |
// |---------------------------------------------------------------------------------------------------------------------|
// | Address for port A write and read operations.                                                                       |
// +---------------------------------------------------------------------------------------------------------------------+
// | clka           | Input     | 1                                     | NA      | Rising edge | Required               |
// |---------------------------------------------------------------------------------------------------------------------|
// | Clock signal for port A.                                                                                            |
// +---------------------------------------------------------------------------------------------------------------------+
// | dbiterra       | Output    | 1                                     | clka    | Active-high | DoNotCare              |
// |---------------------------------------------------------------------------------------------------------------------|
// | Status signal to indicate double bit error occurrence on the data output of port A.                                 |
// +---------------------------------------------------------------------------------------------------------------------+
// | dina           | Input     | WRITE_DATA_WIDTH_A                    | clka    | NA          | Required               |
// |---------------------------------------------------------------------------------------------------------------------|
// | Data input for port A write operations.                                                                             |
// +---------------------------------------------------------------------------------------------------------------------+
// | douta          | Output    | READ_DATA_WIDTH_A                     | clka    | NA          | Required               |
// |---------------------------------------------------------------------------------------------------------------------|
// | Data output for port A read operations.                                                                             |
// +---------------------------------------------------------------------------------------------------------------------+
// | ena            | Input     | 1                                     | clka    | Active-high | Required               |
// |---------------------------------------------------------------------------------------------------------------------|
// | Memory enable signal for port A.                                                                                    |
// | Must be high on clock cycles when read or write operations are initiated. Pipelined internally.                     |
// +---------------------------------------------------------------------------------------------------------------------+
// | injectdbiterra | Input     | 1                                     | clka    | Active-high | Tie to 1'b0            |
// |---------------------------------------------------------------------------------------------------------------------|
// | Controls double bit error injection on input data when ECC enabled (Error injection capability is not available in  |
// | "decode_only" mode).                                                                                                |
// +---------------------------------------------------------------------------------------------------------------------+
// | injectsbiterra | Input     | 1                                     | clka    | Active-high | Tie to 1'b0            |
// |---------------------------------------------------------------------------------------------------------------------|
// | Controls single bit error injection on input data when ECC enabled (Error injection capability is not available in  |
// | "decode_only" mode).                                                                                                |
// +---------------------------------------------------------------------------------------------------------------------+
// | regcea         | Input     | 1                                     | clka    | Active-high | Tie to 1'b1            |
// |---------------------------------------------------------------------------------------------------------------------|
// | Clock Enable for the last register stage on the output data path.                                                   |
// +---------------------------------------------------------------------------------------------------------------------+
// | rsta           | Input     | 1                                     | clka    | Active-high | Required               |
// |---------------------------------------------------------------------------------------------------------------------|
// | Reset signal for the final port A output register stage.                                                            |
// | Synchronously resets output port douta to the value specified by parameter READ_RESET_VALUE_A.                      |
// +---------------------------------------------------------------------------------------------------------------------+
// | sbiterra       | Output    | 1                                     | clka    | Active-high | DoNotCare              |
// |---------------------------------------------------------------------------------------------------------------------|
// | Status signal to indicate single bit error occurrence on the data output of port A.                                 |
// +---------------------------------------------------------------------------------------------------------------------+
// | sleep          | Input     | 1                                     | NA      | Active-high | Tie to 1'b0            |
// |---------------------------------------------------------------------------------------------------------------------|
// | sleep signal to enable the dynamic power saving feature.                                                            |
// +---------------------------------------------------------------------------------------------------------------------+
// | wea            | Input     | WRITE_DATA_WIDTH_A                    | clka    | Active-high | Required               |
// |---------------------------------------------------------------------------------------------------------------------|
// | Write enable vector for port A input data port dina. 1 bit wide when word-wide writes are used.                     |
// | In byte-wide write configurations, each bit controls the writing one byte of dina to address addra.                 |
// | For example, to synchronously write only bits [15-8] of dina when WRITE_DATA_WIDTH_A is 32, wea would be 4'b0010.   |
// +---------------------------------------------------------------------------------------------------------------------+


// xpm_memory_spram : In order to incorporate this function into the design,
//     Verilog      : the following instance declaration needs to be placed
//     instance     : in the body of the design code.  The instance name
//   declaration    : (xpm_memory_spram_inst) and/or the port declarations within the
//       code       : parenthesis may be changed to properly reference and
//                  : connect this function to the design.  All inputs
//                  : and outputs must be connected.

//  Please reference the appropriate libraries guide for additional information on the XPM modules.

//  <-----Cut code below this line---->


// Author: Wolfgang Roenninger <wroennin@ethz.ch>
// Author: Thomas Benz <tbenz@ethz.ch>

// Description: Technology-specific wrapper for SRAM macros
//              !!! THIS FILE IS GENERATED AUTOMATICALLY !!!
//              To ensure correct operation, DO NOT change the ordering of the parameters
//
// Parameters:
// - NumWords:    Number of words in the macro. Address width can be calculated with:
//                `AddrWidth = (NumWords > 32'd1) ? $clog2(NumWords) : 32'd1`
//                The module issues a warning if there is a request on an address which is
//                not in range.
// - DataWidth:   Width of the ports `wdata_i` and `rdata_o`.
// - ByteWidth:   Width of a byte, the byte enable signal `be_i` can be calculated with the
//                ceiling division `ceil(DataWidth, ByteWidth)`.
// - NumPorts:    Number of read and write ports. Each is a full port. Ports with a higher
//                index read and write after the ones with lower indices.
// - Latency:     Read latency, the read data is available this many cycles after a request.
// - SimInit:     Macro simulation initialization. Values are:
//                "zeros":  Each bit gets initialized with 1'b0.
//                "ones":   Each bit gets initialized with 1'b1.
//                "random": Each bit gets random initialized with 1'b0 or 1'b1.
//                "none":   Each bit gets initialized with 1'bx. (default)
// - PrintSimCfg: Prints at the beginning of the simulation a `Hello` message with
//                the instantiated parameters and signal widths.
//
// Ports:
// - `clk_i`:   Clock
// - `rst_ni`:  Asynchronous reset, active low
// - `req_i`:   Request, active high
// - `we_i`:    Write request, active high
// - `addr_i`:  Request address
// - `wdata_i`: Write data, has to be valid on request
// - `be_i`:    Byte enable, active high
// - `rdata_o`: Read data, valid `Latency` cycles after a request with `we_i` low.
//
// Behaviour:
// - Address collision:  When Ports are making a write access onto the same address,
//                       the write operation will start at the port with the lowest address
//                       index, each port will overwrite the changes made by the previous ports
//                       according how the respective `be_i` signal is set.
// - Read data on write: This implementation will not produce a read data output on the signal
//                       `rdata_o` when `req_i` and `we_i` are asserted. The output data is stable
//                       on write requests.

module tc_sram #(
  parameter int unsigned NumWords     = 32'd1024, // Number of Words in data array
  parameter int unsigned DataWidth    = 32'd128,  // Data signal width
  parameter int unsigned ByteWidth    = 32'd8,    // Width of a data byte
  parameter int unsigned NumPorts     = 32'd1,    // Number of read and write ports
  parameter int unsigned Latency      = 32'd1,    // Latency when the read data is available
  parameter              SimInit      = "none",   // Simulation initialization
  parameter bit          PrintSimCfg  = 1'b0,     // Print configuration
  // DEPENDENT PARAMETERS, DO NOT OVERWRITE!
  parameter int unsigned AddrWidth = (NumWords > 32'd1) ? $clog2(NumWords) : 32'd1,
  parameter int unsigned BeWidth   = (DataWidth + ByteWidth - 32'd1) / ByteWidth, // ceil_div
  parameter type         addr_t    = logic [AddrWidth-1:0],
  parameter type         data_t    = logic [DataWidth-1:0],
  parameter type         be_t      = logic [BeWidth-1:0]
) (
  input  logic                 clk_i,      // Clock
  input  logic                 rst_ni,     // Asynchronous reset active low
  // input ports
  input  logic  [NumPorts-1:0] req_i,      // request
  input  logic  [NumPorts-1:0] we_i,       // write enable
  input  addr_t [NumPorts-1:0] addr_i,     // request address
  input  data_t [NumPorts-1:0] wdata_i,    // write data
  input  be_t   [NumPorts-1:0] be_i,       // write byte enable
  // output ports
  output data_t [NumPorts-1:0] rdata_o     // read data
);

    localparam int unsigned MemSize   = NumWords * DataWidth;

    // xpm_memory_spram: Single Port RAM
    // Xilinx Parameterized Macro, version 2019.1

    if (DataWidth%8 == 0) begin : gen_xpm

        logic [(DataWidth+7)/8-1:0]   wea;
        assign wea = we_i ? be_i : 'b0;

        xpm_memory_spram #(
            .ADDR_WIDTH_A            ( AddrWidth         ),
            .AUTO_SLEEP_TIME         ( 0                 ),
            .BYTE_WRITE_WIDTH_A      ( ByteWidth         ),
            /*.CASCADE_HEIGHT          ( 0                 ),*/
            .ECC_MODE                ( "no_ecc"          ),
            .MEMORY_INIT_FILE        ( "none"            ),
            .MEMORY_INIT_PARAM       ( "0"               ),
            /*.MEMORY_OPTIMIZATION     ( "true"            ),*/
            /*.MEMORY_PRIMITIVE        ( "ultra"           ),*/
            .MEMORY_PRIMITIVE        ( "block"           ),
            .MEMORY_SIZE             ( MemSize           ),
            .MESSAGE_CONTROL         ( 1                 ),
            .READ_DATA_WIDTH_A       ( DataWidth         ),
            .READ_LATENCY_A          ( Latency           ),
            .READ_RESET_VALUE_A      ( "0"               ),
            /*.RST_MODE_A              ( "SYNC"            ),*/
            /*.SIM_ASSERT_CHK          ( 0                 ),*/
            .USE_MEM_INIT            ( 1                 ),
            .WAKEUP_TIME             ( "disable_sleep"   ),
            .WRITE_DATA_WIDTH_A      ( DataWidth         ),
            .WRITE_MODE_A            ( "read_first"      )
        )
        xpm_memory_spram_inst (
            .dbiterra                (                   ),
            .douta                   ( rdata_o           ),
            .sbiterra                (                   ),
            .addra                   ( addr_i            ),
            .clka                    ( clk_i             ),
            .dina                    ( wdata_i           ),
            .ena                     ( 1'b1              ),
            .injectdbiterra          ( 1'b0              ),
            .injectsbiterra          ( 1'b0              ),
            .regcea                  ( 1'b0              ),
            .rsta                    ( ~rst_ni           ),
            .sleep                   ( 1'b0              ),
            .wea                     ( wea               )
        );


    end else begin : gen_padded

        localparam int unsigned PaddedDataWidth =  BeWidth * 8;
        localparam int unsigned PaddingWidth = PaddedDataWidth - DataWidth;
        logic [PaddedDataWidth-1:0]   padded_wdata, padded_rdata;

        assign padded_wdata = {{PaddingWidth{1'b0}}, wdata_i};
        assign rdata_o      = padded_rdata[DataWidth-1:0];


        tc_sram #(
            .NumWords                ( NumWords          ),
            .DataWidth               ( PaddedDataWidth   ),
            .ByteWidth               ( ByteWidth         ),
            .NumPorts                ( NumPorts          )
        ) i_sram_padded (
            .clk_i                   ( clk_i             ),
            .rst_ni                  ( rst_ni            ),
            .req_i                   ( req_i             ),
            .we_i                    ( we_i              ),
            .addr_i                  ( addr_i            ),
            .wdata_i                 ( padded_wdata      ),
            .be_i                    ( be_i              ),
            .rdata_o                 ( padded_rdata      )
        );

    end

    // End of xpm_memory_spram_inst instantiation

endmodule : tc_sram
