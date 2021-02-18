// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module otbn_mac_bignum
  import otbn_pkg::*;
(
  input logic clk_i,
  input logic rst_ni,

  input mac_bignum_operation_t operation_i,
  input logic                  mac_en_i,

  output logic [WLEN-1:0] operation_result_o,
  output flags_t          operation_flags_o,
  output flags_t          operation_flags_en_o,

  output logic [WLEN-1:0] ispr_acc_o,
  input  logic [WLEN-1:0] ispr_acc_wr_data_i,
  input  logic            ispr_acc_wr_en_i
);
  // The MAC operates on quarter-words, QWLEN gives the number of bits in a quarter-word.
  localparam int unsigned QWLEN = WLEN / 4;

  logic [WLEN-1:0] adder_op_a;
  logic [WLEN-1:0] adder_op_b;
  logic [WLEN-1:0] adder_result;
  logic [1:0]      adder_result_hw_is_zero;

  logic [QWLEN-1:0]  mul_op_a;
  logic [QWLEN-1:0]  mul_op_b;
  logic [WLEN/2-1:0] mul_res;
  logic [WLEN-1:0]   mul_res_shifted;

  logic [WLEN-1:0] acc;
  logic [WLEN-1:0] acc_d;
  logic [WLEN-1:0] acc_q;
  logic            acc_en;

  // Extract QWLEN multiply operands from WLEN operand inputs based on chosen quarter word from the
  // instruction (operand_[a|b]_qw_sel).
  always_comb begin
    mul_op_a = '0;
    mul_op_b = '0;

    unique case (operation_i.operand_a_qw_sel)
      2'd0: mul_op_a = operation_i.operand_a[QWLEN*0+:QWLEN];
      2'd1: mul_op_a = operation_i.operand_a[QWLEN*1+:QWLEN];
      2'd2: mul_op_a = operation_i.operand_a[QWLEN*2+:QWLEN];
      2'd3: mul_op_a = operation_i.operand_a[QWLEN*3+:QWLEN];
      default: mul_op_a = '0;
    endcase

    unique case (operation_i.operand_b_qw_sel)
      2'd0: mul_op_b = operation_i.operand_b[QWLEN*0+:QWLEN];
      2'd1: mul_op_b = operation_i.operand_b[QWLEN*1+:QWLEN];
      2'd2: mul_op_b = operation_i.operand_b[QWLEN*2+:QWLEN];
      2'd3: mul_op_b = operation_i.operand_b[QWLEN*3+:QWLEN];
      default: mul_op_b = '0;
    endcase
  end

  `ASSERT_KNOWN_IF(OperandAQWSelKnown, operation_i.operand_a_qw_sel, mac_en_i)
  `ASSERT_KNOWN_IF(OperandBQWSelKnown, operation_i.operand_b_qw_sel, mac_en_i)

  assign mul_res = mul_op_a * mul_op_b;

  // Shift the QWLEN multiply result into a WLEN word before accumulating using the shift amount
  // supplied in the instruction (pre_acc_shift_imm).
  always_comb begin
    mul_res_shifted = '0;

    unique case (operation_i.pre_acc_shift_imm)
      2'd0: mul_res_shifted = {{QWLEN*2{1'b0}}, mul_res};
      2'd1: mul_res_shifted = {{QWLEN{1'b0}}, mul_res, {QWLEN{1'b0}}};
      2'd2: mul_res_shifted = {mul_res, {QWLEN*2{1'b0}}};
      2'd3: mul_res_shifted = {mul_res[63:0], {QWLEN*3{1'b0}}};
      default: mul_res_shifted = '0;
    endcase
  end

  `ASSERT_KNOWN_IF(PreAccShiftImmKnown, operation_i.pre_acc_shift_imm, mac_en_i)

  // Accumulator logic

  // Accumulator reads as 0 if .Z set in MULQACC (zero_acc).
  assign acc = operation_i.zero_acc ? '0 : acc_q;

  // Add shifted multiplier result to current accumulator.
  assign adder_op_a = mul_res_shifted;
  assign adder_op_b = acc;

  assign adder_result = adder_op_a + adder_op_b;

  // Split zero check between the two halves of the result. This is used for flag setting (see
  // below).
  assign adder_result_hw_is_zero[0] = adder_result[WLEN/2-1:0] == 'h0;
  assign adder_result_hw_is_zero[1] = adder_result[WLEN/2+:WLEN/2] == 'h0;

  assign operation_flags_o.L    = adder_result[0];
  // L is always updated for .WO, and for .SO when writing to the lower half-word
  assign operation_flags_en_o.L = operation_i.shift_acc ? ~operation_i.wr_hw_sel_upper :
                                                          1'b1;

  // For .SO M is taken from the top-bit of shifted out half-word, otherwise it is taken from the
  // top-bit of the full result.
  assign operation_flags_o.M    = operation_i.shift_acc ? adder_result[WLEN/2-1] :
                                                          adder_result[WLEN-1];
  // M is always updated for .WO, and for .SO when writing to the upper half-word.
  assign operation_flags_en_o.M = operation_i.shift_acc ? operation_i.wr_hw_sel_upper :
                                                          1'b1;

  // For .SO Z is calculated from the shifted out half-word, otherwise it is calculated on the full
  // result.
  assign operation_flags_o.Z    = operation_i.shift_acc ? adder_result_hw_is_zero[0] :
                                                          &adder_result_hw_is_zero;

  // Z is updated for .WO. For .SO updates are based upon result and half-word:
  // - When writing to lower half-word always update Z.
  // - When writing to upper half-word clear Z if result is non-zero otherwise leave it alone.
  assign operation_flags_en_o.Z =
      operation_i.shift_acc & operation_i.wr_hw_sel_upper ? ~adder_result_hw_is_zero[0] :
                                                            1'b1;

  // MAC never sets the carry flag
  assign operation_flags_o.C    = 1'b0;
  assign operation_flags_en_o.C = 1'b0;

  // If performing an ACC ISPR write the next accumulator value is taken from the ISPR write data,
  // otherwise it is drawn from the adder result. The new accumulator can be optionally shifted
  // right by one half-word (shift_acc).
  assign acc_d = ispr_acc_wr_en_i      ? ispr_acc_wr_data_i                                :
                 operation_i.shift_acc ? {{QWLEN*2{1'b0}}, adder_result[QWLEN*2+:QWLEN*2]} :
                                         adder_result;

  // Only write to accumulator if the MAC is enabled or an ACC ISPR write is occuring.
  assign acc_en = mac_en_i | ispr_acc_wr_en_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      acc_q <= '0;
    end else if (acc_en) begin
      acc_q <= acc_d;
    end
  end

  assign ispr_acc_o = acc_q;

  // The operation result is taken directly from the adder, shift_acc only applies to the new value
  // written to the accumulator.
  assign operation_result_o = adder_result;

  `ASSERT(NoISPRAccWrAndMacEn, ~(ispr_acc_wr_en_i & mac_en_i))
endmodule
