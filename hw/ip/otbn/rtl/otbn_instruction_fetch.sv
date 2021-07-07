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

  logic [31:0] imem_rdata_descrambled;
  logic        imem_rvalid_descrambled;

  assign imem_req_o = insn_fetch_req_valid_i;
  assign imem_addr_o = insn_fetch_req_addr_i;

  assign insn_fetch_resp_valid_o = imem_rvalid_descrambled;
  assign insn_fetch_resp_data_o = imem_rdata_descrambled;

  always_ff @(posedge clk_i) begin
    insn_fetch_resp_addr_o <= insn_fetch_req_addr_i;
  end

  assign insn_fetch_err_o = imem_rvalid_i & imem_rerror_i;

  // Nothing is reset in this module so rst_ni is unused. Leaving it in so adding resettable flops
  // (or an assertion which will use the reset) is straight forward.
  logic unused_rst_n;
  assign unused_rst_n = rst_ni;

  // EXPERIMENT: Instruction descrambler
  logic [127:0] key;
  logic [31:0] initial_state;

`ifndef SYNTHESIS
  initial begin
    if ($value$plusargs("OTBN_CFI_KEY=%h", key)) begin
      $display("Setting OTBN_CFI_KEY from plusarg.");
    end
    if ($value$plusargs("OTBN_CFI_INITIAL_STATE=%h", initial_state)) begin
      $display("Setting OTBN_CFI_INITIAL_STATE from plusarg.");
    end
    $display("OTBN CFI: key=%x, initial_state=%x", key, initial_state);
  end
`else
  assign key = 0;
  assign initial_state = 32'he164bf2b;
`endif

  // 32b sponge state
  logic [31:0] state_d, state_q;

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      state_q <= initial_state;
    end else begin
      if (imem_rvalid_i) begin
        state_q <= state_d;
      end
    end
  end

  // 64b PRINCE primitive (12 rounds)
  prim_prince #(
    .DataWidth     (64),
    .KeyWidth      (128),
    .NumRoundsHalf (5), // 5 for full prince (12 rounds)
    .HalfwayDataReg(1'b0),
    .HalfwayKeyReg (1'b0)
  ) u_scfp_prince (
    .clk_i,
    .rst_ni,

    .data_i ({state_q, imem_rdata_i}),
    .valid_i(imem_rvalid_i),
    .dec_i  (1'b1),
    .key_i  (key),
    .valid_o(imem_rvalid_descrambled),
    .data_o ({state_d, imem_rdata_descrambled})
  );
endmodule
