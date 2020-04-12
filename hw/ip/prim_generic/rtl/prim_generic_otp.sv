// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module prim_generic_otp #(
  parameter  int Width     = 8,
  parameter  int Depth     = 1024,
  parameter  int ErrWidth  = 8,
  localparam int AddrWidth = $clog2(Depth)
) (
  input                        clk_i,
  input                        rst_ni,
  // TODO: power sequencing signals from/to AST
  // Test interface
  input  tlul_pkg::tl_h2d_t    test_tl_i,
  output tlul_pkg::tl_d2h_t    test_tl_o,
  // Start Macro init sequence
  // init shall be asserted until acknowledged with done
  input                        init_req_i,
  output logic                 init_done_o,
  // Macro error output
  // TODO: define error codes
  output logic                 err_valid_o,
  output logic [ErrWidth-1:0]  err_code_o,
  // Ready valid handshake for read/write command
  output logic                 ready_o,
  input                        valid_i,
  input [AddrWidth-1:0]        addr_i,
  input [Width-1:0]            wdata_i,
  input                        wren_i, // 0: read command, 1: write command
  // Read data output
  output logic [Width-1:0]     rdata_o,
  output logic                 rvalid_o
);

  ///////////////////
  // Control logic //
  ///////////////////

  logic req, write_d, write_q, read_d, read_q;
  logic [Width-1:0] wdata, wdata_d, wdata_q;
  logic [AddrWidth-1:0] addr, waddr_d, waddr_q;

  // TODO: add support for these in emulation
  assign test_tl_o   = '0;
  assign err_valid_o = '0;
  assign err_type_o  = '0;
  assign init_done_o = 1'b1;

  // TODO: randomize / extend access times
  assign read_d  = ready_o & valid_i & ~wren_i;
  assign write_d = ready_o & valid_i & wren_i;
  assign wdata_d = (write_d) ? wdata_i : wdata_q;
  assign waddr_d = (write_d) ? addr_i : waddr_q;

  assign ready_o  = ~write_q;
  assign rvalid_o = read_q;

  // perform read modify write and OR bits on top
  // of existing data
  assign wdata = rdata_o | wdata_q;
  assign addr  = (write_q) ? waddr_q : addr_i;
  assign req   = read_d | write_d | write_q;

  //////////////////////////////////
  // Emulate using memory process //
  //////////////////////////////////

  logic [Width-1:0] mem [Depth];

  // using always instead of always_ff to avoid 'ICPD  - illegal combination of drivers' error
  // thrown when using $readmemh system task to backdoor load an image
  always @(posedge clk_i) begin
    if (req) begin
      if (write_q) begin
        mem[addr] <= wdata;
      end else begin
        rdata_o <= mem[addr];
      end
    end
  end

  // TODO: add verilator init mechanism
  `ifdef OTP_INIT_FILE
    localparam MEM_FILE = `PRIM_STRINGIFY(`OTP_INIT_FILE);
    initial begin
      $display("Initializing OTP from %s", MEM_FILE);
      $readmemh(MEM_FILE, mem);
    end
  `endif

  //////////
  // Regs //
  //////////

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      read_q  <= 1'b0;
      write_q <= 1'b0;
      wdata_q <= '0;
      waddr_q <= '0;
    end else begin
      read_q  <= read_d;
      write_q <= write_d;
      wdata_q <= wdata_d;
      waddr_q <= waddr_d;
    end
  end

endmodule : prim_generic_otp
