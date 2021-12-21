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
  logic        adder_op_b_negate;
  logic [32:0] adder_result;

  logic [31:0] and_result;
  logic [31:0] or_result;
  logic [31:0] xor_result;
  logic [31:0] not_result;

  logic        is_equal;

  ///////////
  // Adder //
  ///////////

  // Adder takes in 33-bit operands. The addition of the input operands occurs on bits [32:1],
  // setting addr_op_b_negate will cause a carry-in into bit 1. Combined with an inversion of
  // operation_i.operand_b this gives a two's-complement negation (~b + 1)

  assign adder_op_b_negate = operation_i.op == AluOpBaseSub;

  assign adder_op_a = {operation_i.operand_a, 1'b1};
  assign adder_op_b = adder_op_b_negate ? {~operation_i.operand_b, 1'b1} :
                                          { operation_i.operand_b, 1'b0};

  assign adder_result = adder_op_a + adder_op_b;

  //////////////////////////
  // Bit-wise logical ops //
  //////////////////////////

  assign and_result = operation_i.operand_a & operation_i.operand_b;
  assign or_result  = operation_i.operand_a | operation_i.operand_b;
  assign xor_result = operation_i.operand_a ^ operation_i.operand_b;
  assign not_result = ~operation_i.operand_a;

  /////////////
  // Shifter //
  /////////////

  logic [32:0] shift_in;
  logic [ 4:0] shift_amt;
  logic [31:0] operand_a_reverse;
  logic [32:0] shift_out;
  logic [31:0] shift_out_reverse;

  for (genvar i = 0; i < 32; i++) begin : g_shifter_reverses
    assign operand_a_reverse[i] = operation_i.operand_a[31-i];
    assign shift_out_reverse[i] = shift_out[31-i];
  end

  assign shift_amt = operation_i.operand_b[4:0];
  // Shifter performs right arithmetic 33-bit shifts. Force top bit to 0 to get logical shifting
  // otherwise replicate top bit of shift_in. Left shifts performed by reversing the input and
  // output.
  assign shift_in[31:0] = (operation_i.op == AluOpBaseSll) ? operand_a_reverse :
                                                             operation_i.operand_a;
  assign shift_in[32] = (operation_i.op == AluOpBaseSra) ? operation_i.operand_a[31] : 1'b0;

  logic signed [32:0] shift_in_signed;
  assign shift_in_signed = signed'(shift_in);
  assign shift_out = unsigned'(shift_in_signed >>> shift_amt);

  ////////////////
  // Output Mux //
  ////////////////

  always_comb begin
    operation_result_o = adder_result[32:1];

    unique case (operation_i.op)
      AluOpBaseAnd: operation_result_o = and_result;
      AluOpBaseOr:  operation_result_o = or_result;
      AluOpBaseXor: operation_result_o = xor_result;
      AluOpBaseNot: operation_result_o = not_result;
      AluOpBaseSra: operation_result_o = shift_out[31:0];
      AluOpBaseSrl: operation_result_o = shift_out[31:0];
      AluOpBaseSll: operation_result_o = shift_out_reverse;
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

  assign comparison_result_o = (comparison_i.op == ComparisonOpBaseEq) ? is_equal : ~is_equal;

  // The bottom bit of adder_result is discarded. It simply corresponds to the carry in used to
  // produce twos complement subtraction from an addition.
  logic unused_adder_result_bit;

  // The top bit of shift_out is discarded. shift_in contains an extra bit to deal with sign
  // extension which isn't needed in the shift_out result.
  logic unused_shift_out_result_bit;
  assign unused_shift_out_result_bit = shift_out[32];

  assign unused_adder_result_bit = adder_result[0];

  // clk_i, rst_ni are only used by assertions
  logic unused_clk;
  logic unused_rst_n;

  assign unused_clk   = clk_i;
  assign unused_rst_n = rst_ni;
endmodule
