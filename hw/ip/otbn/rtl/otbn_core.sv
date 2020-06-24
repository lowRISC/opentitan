// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"
`include "prim_util.svh"

/**
 * OpenTitan Big Number Accelerator (OTBN) Core
 *
 * This module is the top-level of the OTBN processing core.
 */
module otbn_core
#(
  // Size of the instruction memory, in bytes
  parameter int ImemSizeByte = 4096,
  parameter int ImemSizeWords = ImemSizeByte/4,
  // Size of the data memory, in bytes
  parameter int DmemSizeByte = 4096,
  parameter int DmemSizeWords = 4096/32,

  localparam int ImemAddrWidth = vbits(ImemSizeByte),
  localparam int DmemAddrWidth = vbits(DmemSizeByte)
)(
  input  logic  clk_i,
  input  logic  rst_ni,

  input  logic  start_i,
  output logic  busy_o,

  // Instruction memory (IMEM)
  output logic                     imem_req_o,
  output logic                     imem_write_o,
  output logic [ImemAddrWidth-1:0] imem_addr_o,
  output logic [31:0]              imem_wdata_o,
  input  logic [31:0]              imem_rdata_i,
  input  logic                     imem_rvalid_i,
  input  logic [1:0]               imem_rerror_i,

  // Data memory (DMEM)
  output logic                     dmem_req_o,
  output logic                     dmem_write_o,
  output logic [DmemAddrWidth-1:0] dmem_addr_o,
  output logic [WLEN-1:0]          dmem_wdata_o,
  output logic [WLEN-1:0]          dmem_wmask_o,
  input  logic [WLEN-1:0]          dmem_rdata_i,
  input  logic                     dmem_rvalid_i,
  input  logic [1:0]               dmem_rerror_i
);
  import otbn_pkg::*;

  // TODO: This is probably not the final OTBN implementation.

  assign imem_req_o = 1'b0;

  assign dmem_write_o = 1'b1;
  assign dmem_addr_o = '0;
  assign dmem_wdata_o = 256'h0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF;
  assign dmem_wmask_o = {WLEN{1'b1}};

  logic [15:0] cnt;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      busy_o <= 1'b0;
      cnt <= 'b0;
      dmem_req_o <= 1'b0;
    end else begin
      if (start_i) begin
        busy_o <= 1'b1;
        cnt <= 'b0;
        dmem_req_o <= 1'b1;
      end else begin
        if (cnt == 16'hFFFF) begin
          busy_o <= 1'b0;
        end

        cnt <= cnt + 16'b1;
        dmem_req_o <= 1'b0;
      end
    end
  end
endmodule
