// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * OTBN Instruction Fetch Unit
 *
 * Fetch an instruction from the instruction memory.
 */
module otbn_instruction_fetch
  import otbn_pkg::*;
#(
  parameter int ImemSizeByte = 4096,

  localparam int ImemAddrWidth = prim_util_pkg::vbits(ImemSizeByte)
) (
  input logic clk_i,
  input logic rst_ni,

  // Instruction memory (IMEM) interface. Read-only.
  output logic                     imem_req_o,
  output logic [ImemAddrWidth-1:0] imem_addr_o,
  input  logic [31:0]              imem_rdata_i,
  input  logic                     imem_rvalid_i,
  input  logic                     imem_rerror_i,

  // Next instruction selection (to instruction fetch)
  input  logic                     insn_fetch_req_valid_i,
  input  logic [ImemAddrWidth-1:0] insn_fetch_req_addr_i,

  // Decoded instruction
  output logic                     insn_fetch_resp_valid_o,
  output logic [ImemAddrWidth-1:0] insn_fetch_resp_addr_o,
  output logic [31:0]              insn_fetch_resp_data_o,

  output logic                     insn_fetch_err_o // ECC error seen in instruction fetch
);

  assign imem_req_o = insn_fetch_req_valid_i;
  assign imem_addr_o = insn_fetch_req_addr_i;

  assign insn_fetch_resp_valid_o = imem_rvalid_i;
  assign insn_fetch_resp_data_o = imem_rdata_i;

  always_ff @(posedge clk_i) begin
    insn_fetch_resp_addr_o <= insn_fetch_req_addr_i;
  end

  assign insn_fetch_err_o = imem_rvalid_i & imem_rerror_i;

  // Nothing is reset in this module so rst_ni is unused. Leaving it in so adding resettable flops
  // (or an assertion which will use the reset) is straight forward.
  logic unused_rst_n;
  assign unused_rst_n = rst_ni;
endmodule
