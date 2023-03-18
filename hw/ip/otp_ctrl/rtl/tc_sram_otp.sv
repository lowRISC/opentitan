// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Wolfgang Roenninger <wroennin@ethz.ch>, ETH Zurich
//
// Description: Xilinx implementation using the XPM constructs for `tc_sram`
//              Make sure that Vivado can detect the XPM macros by issuing
//              the `auto_detect_xpm` or `set_property XPM_LIBRARIES XPM_MEMORY [current_project]`
//              command. Currently the Xilinx macros are always initialized to all zero!
//              The behaviour, parameters and ports are described in the header of `rtl/tc_sram.sv`.

module tc_sram_otp #(
  parameter int unsigned NumWords     = 32'd1024, // Number of Words in data array
  parameter int unsigned DataWidth    = 32'd128,  // Data signal width (in bits)
  parameter int unsigned ByteWidth    = 32'd8,    // Width of a data byte (in bits)
  parameter int unsigned NumPorts     = 32'd2,    // Number of read and write ports
  parameter int unsigned Latency      = 32'd1,    // Latency when the read data is available
  parameter              SimInit      = "zeros",  // Simulation initialization, fixed to zero here!
  parameter bit          PrintSimCfg  = 1'b0,     // Print configuration
  // DEPENDENT PARAMETERS, DO NOT OVERWRITE!
  parameter int unsigned AddrWidth = (NumWords > 32'd1) ? $clog2(NumWords) : 32'd1,
  parameter int unsigned BeWidth   = (DataWidth + ByteWidth - 32'd1) / ByteWidth, // ceil_div
  parameter type         addr_t    = logic [AddrWidth-1:0],
  parameter type         data_t    = logic [DataWidth-1:0],
  parameter type         be_t      = logic [BeWidth-1:0]
) (
  input  logic                clk_i,      // Clock
  input  logic                rst_ni,     // Asynchronous reset active low
  // input ports
  input  logic  [NumPorts-1:0] req_i,      // request
  input  logic  [NumPorts-1:0] we_i,       // write enable
  input  addr_t [NumPorts-1:0] addr_i,     // request address
  input  data_t [NumPorts-1:0] wdata_i,    // write data
  input  be_t   [NumPorts-1:0] be_i,       // write byte enable
  // output ports
  output data_t [NumPorts-1:0] rdata_o     // read data
);

  localparam int unsigned DataWidthAligned = ByteWidth * BeWidth;
  localparam int unsigned Size             = NumWords * DataWidthAligned;

  typedef logic [DataWidthAligned-1:0] data_aligned_t;

  data_aligned_t [NumPorts-1:0] wdata_al;
  data_aligned_t [NumPorts-1:0] rdata_al;
  be_t           [NumPorts-1:0] we;

  // pad with 0 to next byte for inferable macro below, as the macro wants
  // READ_DATA_WIDTH_A be a multiple of BYTE_WRITE_WIDTH_A
  always_comb begin : p_align
    wdata_al = '0;
    for (int unsigned i = 0; i < NumPorts; i++) begin
      wdata_al[i][DataWidth-1:0] = wdata_i[i];
    end
  end

  for (genvar i = 0; i < NumPorts; i++) begin : gen_port_assign
    for (genvar j = 0; j < BeWidth; j++) begin : gen_we_assign
      assign we[i][j] = be_i[i][j] & we_i[i];
    end
    assign rdata_o[i] = data_t'(rdata_al[i]);
  end

  if (NumPorts == 32'd1) begin : gen_1_ports
    // xpm_memory_spram: Single Port RAM
    // XilinxParameterizedMacro, version 2018.1
    xpm_memory_spram#(
      .ADDR_WIDTH_A        ( AddrWidth        ), // DECIMAL
      .AUTO_SLEEP_TIME     ( 0                ), // DECIMAL
      .BYTE_WRITE_WIDTH_A  ( ByteWidth        ), // DECIMAL
      .ECC_MODE            ( "no_ecc"         ), // String
      .MEMORY_INIT_FILE    ( "otp-img.mem"    ), // String
      .MEMORY_INIT_PARAM   ( "0"              ), // String
      .MEMORY_OPTIMIZATION ( "true"           ), // String
      .MEMORY_PRIMITIVE    ( "auto"           ), // String
      .MEMORY_SIZE         ( Size             ), // DECIMAL in bit!
      .MESSAGE_CONTROL     ( 0                ), // DECIMAL
      .READ_DATA_WIDTH_A   ( DataWidthAligned ), // DECIMAL
      .READ_LATENCY_A      ( Latency          ), // DECIMAL
      .READ_RESET_VALUE_A  ( "0"              ), // String
      .USE_MEM_INIT        ( 1                ), // DECIMAL
      .WAKEUP_TIME         ( "disable_sleep"  ), // String
      .WRITE_DATA_WIDTH_A  ( DataWidthAligned ), // DECIMAL
      .WRITE_MODE_A        ( "no_change"      )  // String
    ) i_xpm_memory_spram (
      .dbiterra ( /*not used*/ ), // 1-bit output: Status signal to indicate double biterror
      .douta    ( rdata_al[0]  ), // READ_DATA_WIDTH_A-bitoutput: Data output for port A
      .sbiterra ( /*not used*/ ), // 1-bit output: Status signal to indicate single biterror
      .addra    ( addr_i[0]    ), // ADDR_WIDTH_A-bit input: Address for port A
      .clka     ( clk_i        ), // 1-bit input: Clock signal for port A.
      .dina     ( wdata_al[0]  ), // WRITE_DATA_WIDTH_A-bitinput: Data input for port A
      .ena      ( req_i[0]     ), // 1-bit input: Memory enable signal for port A.
      .injectdbiterra ( 1'b0   ), // 1-bit input: Controls double biterror injection
      .injectsbiterra ( 1'b0   ), // 1-bit input: Controls single biterror injection
      .regcea   ( 1'b1         ), // 1-bit input: Clock Enable for the last register
      .rsta     ( ~rst_ni      ), // 1-bit input: Reset signal for the final port A output
      .sleep    ( 1'b0         ), // 1-bit input: sleep signal to enable the dynamic power save
      .wea      ( we[0]        )
    );
  end else if (NumPorts == 32'd2) begin : gen_2_ports
    // xpm_memory_tdpram: True Dual Port RAM
    // XilinxParameterizedMacro, version 2018.1
    xpm_memory_tdpram#(
      .ADDR_WIDTH_A            ( AddrWidth        ), // DECIMAL
      .ADDR_WIDTH_B            ( AddrWidth        ), // DECIMAL
      .AUTO_SLEEP_TIME         ( 0                ), // DECIMAL
      .BYTE_WRITE_WIDTH_A      ( ByteWidth        ), // DECIMAL
      .BYTE_WRITE_WIDTH_B      ( ByteWidth        ), // DECIMAL
      .CLOCKING_MODE           ( "common_clock"   ), // String
      .ECC_MODE                ( "no_ecc"         ), // String
      .MEMORY_INIT_FILE        ( "none"           ), // String
      .MEMORY_INIT_PARAM       ( "0"              ), // String
      .MEMORY_OPTIMIZATION     ( "true"           ), // String
      .MEMORY_PRIMITIVE        ( "auto"           ), // String
      .MEMORY_SIZE             ( Size             ), // DECIMAL in bits!
      .MESSAGE_CONTROL         ( 0                ), // DECIMAL
      .READ_DATA_WIDTH_A       ( DataWidthAligned ), // DECIMAL
      .READ_DATA_WIDTH_B       ( DataWidthAligned ), // DECIMAL
      .READ_LATENCY_A          ( Latency          ), // DECIMAL
      .READ_LATENCY_B          ( Latency          ), // DECIMAL
      .READ_RESET_VALUE_A      ( "0"              ), // String
      .READ_RESET_VALUE_B      ( "0"              ), // String
      .USE_EMBEDDED_CONSTRAINT ( 0                ), // DECIMAL
      .USE_MEM_INIT            ( 1                ), // DECIMAL
      .WAKEUP_TIME             ( "disable_sleep"  ), // String
      .WRITE_DATA_WIDTH_A      ( DataWidthAligned ), // DECIMAL
      .WRITE_DATA_WIDTH_B      ( DataWidthAligned ), // DECIMAL
      .WRITE_MODE_A            ( "no_change"      ), // String
      .WRITE_MODE_B            ( "no_change"      )  // String
    ) i_xpm_memory_tdpram (
      .dbiterra ( /*not used*/ ), // 1-bit output: Doubble bit error A
      .dbiterrb ( /*not used*/ ), // 1-bit output: Doubble bit error B
      .sbiterra ( /*not used*/ ), // 1-bit output: Single bit error A
      .sbiterrb ( /*not used*/ ), // 1-bit output: Single bit error B
      .addra    ( addr_i[0]    ), // ADDR_WIDTH_A-bit input: Address for port A
      .addrb    ( addr_i[1]    ), // ADDR_WIDTH_B-bit input: Address for port B
      .clka     ( clk_i        ), // 1-bit input: Clock signal for port A
      .clkb     ( clk_i        ), // 1-bit input: Clock signal for port B
      .dina     ( wdata_al[0]  ), // WRITE_DATA_WIDTH_A-bit input: Data input for port A
      .dinb     ( wdata_al[1]  ), // WRITE_DATA_WIDTH_B-bit input: Data input for port B
      .douta    ( rdata_al[0]  ), // READ_DATA_WIDTH_A-bit output: Data output for port A
      .doutb    ( rdata_al[1]  ), // READ_DATA_WIDTH_B-bit output: Data output for port B
      .ena      ( req_i[0]     ), // 1-bit input: Memory enable signal for port A
      .enb      ( req_i[1]     ), // 1-bit input: Memory enable signal for port B
      .injectdbiterra ( 1'b0   ), // 1-bit input: Controls doublebiterror injection on input data
      .injectdbiterrb ( 1'b0   ), // 1-bit input: Controls doublebiterror injection on input data
      .injectsbiterra ( 1'b0   ), // 1-bit input: Controls singlebiterror injection on input data
      .injectsbiterrb ( 1'b0   ), // 1-bit input: Controls singlebiterror injection on input data
      .regcea   ( 1'b1         ), // 1-bit input: Clock Enable for the last register stage
      .regceb   ( 1'b1         ), // 1-bit input: Clock Enable for the last register stage
      .rsta     ( ~rst_ni      ), // 1-bit input: Reset signal for the final port A output
      .rstb     ( ~rst_ni      ), // 1-bit input: Reset signal for the final port B output
      .sleep    ( 1'b0         ), // 1-bit input: sleep signal to enable the dynamic power
      .wea      ( we[0]        ), // WRITE_DATA_WIDTH_A-bit input: Write enable vector for port A
      .web      ( we[1]        )  // WRITE_DATA_WIDTH_B-bit input: Write enable vector for port B
    );
  end else begin : gen_err_ports
    $fatal(1, "Not supported port parametrization for NumPorts: %0d", NumPorts);
  end

// Validate parameters.
// pragma translate_off
`ifndef VERILATOR
`ifndef TARGET_SYNTHESYS
  initial begin: p_assertions
    assert (SimInit == "zeros") else $fatal(1, "The Xilinx `tc_sram` has fixed SimInit: zeros");
    assert ($bits(addr_i)  == NumPorts * AddrWidth) else $fatal(1, "AddrWidth problem on `addr_i`");
    assert ($bits(wdata_i) == NumPorts * DataWidth) else $fatal(1, "DataWidth problem on `wdata_i`");
    assert ($bits(be_i)    == NumPorts * BeWidth)   else $fatal(1, "BeWidth   problem on `be_i`"   );
    assert ($bits(rdata_o) == NumPorts * DataWidth) else $fatal(1, "DataWidth problem on `rdata_o`");
    assert (NumWords  >= 32'd1) else $fatal(1, "NumWords has to be > 0");
    assert (DataWidth >= 32'd1) else $fatal(1, "DataWidth has to be > 0");
    assert (ByteWidth >= 32'd1) else $fatal(1, "ByteWidth has to be > 0");
    assert (NumPorts  >= 32'd1) else $fatal(1, "The number of ports must be at least 1!");
  end
  initial begin: p_sim_hello
    if (PrintSimCfg) begin
      $display("#################################################################################");
      $display("tc_sram functional instantiated with the configuration:"                          );
      $display("Instance: %m"                                                                     );
      $display("Number of ports   (dec): %0d", NumPorts                                           );
      $display("Number of words   (dec): %0d", NumWords                                           );
      $display("Address width     (dec): %0d", AddrWidth                                          );
      $display("Data width        (dec): %0d", DataWidth                                          );
      $display("Byte width        (dec): %0d", ByteWidth                                          );
      $display("Byte enable width (dec): %0d", BeWidth                                            );
      $display("Latency Cycles    (dec): %0d", Latency                                            );
      $display("Simulation init   (str): %0s", SimInit                                            );
      $display("#################################################################################");
    end
  end
  for (genvar i = 0; i < NumPorts; i++) begin : gen_assertions
    assert property ( @(posedge clk_i) disable iff (!rst_ni)
        (req_i[i] |-> (addr_i[i] < NumWords))) else
      $warning("Request address %0h not mapped, port %0d, expect random write or read behavior!",
          addr_i[i], i);
  end

`endif
`endif
// pragma translate_on

endmodule
