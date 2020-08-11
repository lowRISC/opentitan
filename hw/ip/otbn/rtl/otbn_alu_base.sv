// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * OTBN execute block for the base instruction subset
 *
 * This ALU supports the execution of all of OTBN's base instruction subset.
 */
module otbn_alu_base
import otbn_pkg::*;
(
    // Block is combinatorial; clk/rst are for assertions only.
    input logic clk_i,
    input logic rst_ni,

    input alu_base_operation_t  operation_i,
    input alu_base_comparison_t comparison_i,

    output logic [31:0] operation_result_o,
    output logic        comparison_result_o
);

  logic [32:0] adder_op_a, adder_op_b;
  logic adder_op_b_negate;
  logic [33:0] adder_result;

  logic [31:0] and_result;
  logic [31:0] or_result;
  logic [31:0] xor_result;
  logic [31:0] not_result;

  logic is_equal;

  ///////////
  // Adder //
  ///////////

  // Adder takes in 33-bit operands. The addition of the input operands occurs on bits [32:1],
  // setting addr_op_b_negate will cause a carry-in into bit 1. Combined with an inversion of
  // operation_i.operand_b this gives a two's-complement negation (~b + 1)

  assign adder_op_b_negate = operation_i.op == AluOpSub;

  assign adder_op_a = {operation_i.operand_a, 1'b1};
  assign adder_op_b = adder_op_b_negate ? {
    ~operation_i.operand_b, 1'b1
  } : {
    operation_i.operand_b, 1'b0
  };

  assign adder_result = adder_op_a + adder_op_b;

  //////////////////////////
  // Bit-wise logical ops //
  //////////////////////////

  assign and_result = operation_i.operand_a & operation_i.operand_b;
  assign or_result = operation_i.operand_a | operation_i.operand_b;
  assign xor_result = operation_i.operand_a ^ operation_i.operand_b;
  assign not_result = ~operation_i.operand_a;

  /////////////
  // Shifter //
  /////////////

  logic [32:0] shift_in;
  logic [4:0] shift_amt;
  logic [31:0] operand_a_reverse;
  logic [32:0] shift_out;
  logic [31:0] shift_out_reverse;

  for (genvar i = 0; i < 32; i++) begin : g_shifter_reverses
    assign operand_a_reverse[i] = operation_i.operand_a[31 - i];
    assign shift_out_reverse[i] = shift_out[31 - i];
  end

  assign shift_amt = operation_i.operand_b[4:0];
  // Shifter performs right arithmetic 33-bit shifts. Force top bit to 0 to get logical shifting
  // otherwise replicate top bit of shift_in. Left shifts performed by reversing the input and
  // output.
  assign shift_in[31:0] = (operation_i.op == AluOpSll) ? operand_a_reverse : operation_i.operand_a;
  assign shift_in[32] = (operation_i.op == AluOpSra) ? operation_i.operand_a[31] : 1'b0;

  assign shift_out = signed'(shift_in) >>> shift_amt;

  ////////////////
  // Output Mux //
  ////////////////

  always_comb begin
    operation_result_o = adder_result[32:1];

    unique case (operation_i.op)
      AluOpAnd: operation_result_o = and_result;
      AluOpOr: operation_result_o = or_result;
      AluOpXor: operation_result_o = xor_result;
      AluOpNot: operation_result_o = not_result;
      AluOpSra: operation_result_o = shift_out[31:0];
      AluOpSrl: operation_result_o = shift_out[31:0];
      AluOpSll: operation_result_o = shift_out_reverse;
      default: ;
    endcase
  end

  /////////////////
  // Comparisons //
  /////////////////

  // Dedicated comparator to deal with branches. As only Equal/Not-Equal is required no need to use
  // the adder (which frees it to compute the branch target in the same cycle). No point in using
  // existing XOR logic as area added from extra mux to choose xor operands negates area saving from
  // avoiding an dedicated comparator.
  assign is_equal = comparison_i.operand_a == comparison_i.operand_b;

  assign comparison_result_o = (comparison_i.op == ComparisonOpEq) ? is_equal : ~is_equal;
endmodule
