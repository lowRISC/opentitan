// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * OTBN Instruction Decoder
 */
module otbn_decoder
  import otbn_pkg::*;
(
  // For assertions only.
  input  logic                 clk_i,
  input  logic                 rst_ni,

  // Instruction data to be decoded
  input  logic [31:0]          insn_fetch_resp_data_i,
  input  logic                 insn_fetch_resp_valid_i,

  // Decoded instruction
  output logic                 insn_valid_o,
  output insn_op_e             insn_op_o,

  // Decoded instruction data, matching the "Decoding" section of the specification.
  output insn_dec_base_t       insn_dec_base_o,

  // Additional control signals
  output insn_dec_ctrl_t       insn_dec_ctrl_o
);

  // Example: ADD
  assign insn_valid_o = insn_fetch_resp_valid_i;
  assign insn_op_o    = InsnOpAlu;

  assign insn_dec_base_o = '{
    d: insn_fetch_resp_data_i[11:7],
    a: insn_fetch_resp_data_i[19:15],
    b: insn_fetch_resp_data_i[24:20],
    i: '0
  };

  assign insn_dec_ctrl_o = '{
    subset:   InsnSubsetBase,
    op_a_sel: OpASelRegister,
    op_b_sel: OpBSelRegister,
    alu_op:   AluOpAdd
  };
endmodule
