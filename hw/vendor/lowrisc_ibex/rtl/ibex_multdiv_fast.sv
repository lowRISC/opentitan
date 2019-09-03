// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define OP_L 15:0
`define OP_H 31:16

/**
 * Fast Multiplier and Division
 *
 * 16x16 kernel multiplier and Long Division
 */
module ibex_multdiv_fast (
    input  logic             clk_i,
    input  logic             rst_ni,
    input  logic             mult_en_i,
    input  logic             div_en_i,
    input  ibex_pkg::md_op_e operator_i,
    input  logic  [1:0]      signed_mode_i,
    input  logic [31:0]      op_a_i,
    input  logic [31:0]      op_b_i,
    input  logic [33:0]      alu_adder_ext_i,
    input  logic [31:0]      alu_adder_i,
    input  logic             equal_to_zero,

    output logic [32:0]      alu_operand_a_o,
    output logic [32:0]      alu_operand_b_o,

    output logic [31:0]      multdiv_result_o,
    output logic             valid_o
);

  import ibex_pkg::*;

  logic [ 4:0] div_counter_q, div_counter_n;
  typedef enum logic [1:0] {
    ALBL, ALBH, AHBL, AHBH
  } mult_fsm_e;
  mult_fsm_e mult_state_q, mult_state_n;

  typedef enum logic [2:0] {
    MD_IDLE, MD_ABS_A, MD_ABS_B, MD_COMP, MD_LAST, MD_CHANGE_SIGN, MD_FINISH
  } md_fsm_e;
  md_fsm_e md_state_q, md_state_n;

  logic signed [34:0] mac_res_signed;
  logic        [34:0] mac_res_ext;

  logic [33:0] mac_res_q, mac_res_n, mac_res, op_remainder_n;
  logic [15:0] mult_op_a;
  logic [15:0] mult_op_b;
  logic [33:0] accum;
  logic        sign_a, sign_b;
  logic        div_sign_a, div_sign_b;
  logic        signed_mult;
  logic        is_greater_equal;
  logic        div_change_sign, rem_change_sign;
  logic [31:0] one_shift;
  logic [31:0] op_denominator_q;
  logic [31:0] op_numerator_q;
  logic [31:0] op_quotient_q;
  logic [31:0] op_denominator_n;
  logic [31:0] op_numerator_n;
  logic [31:0] op_quotient_n;
  logic [31:0] next_remainder;
  logic [32:0] next_quotient;
  logic [32:0] res_adder_h;
  logic        mult_valid;
  logic        div_valid;

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_mult_state_q
    if (!rst_ni) begin
      mult_state_q     <= ALBL;
      mac_res_q        <= '0;
      div_counter_q    <= '0;
      md_state_q       <= MD_IDLE;
      op_denominator_q <= '0;
      op_numerator_q   <= '0;
      op_quotient_q    <= '0;
    end else begin

      if (mult_en_i) begin
        mult_state_q <= mult_state_n;
      end

      if (div_en_i) begin
        div_counter_q    <= div_counter_n;
        op_denominator_q <= op_denominator_n;
        op_numerator_q   <= op_numerator_n;
        op_quotient_q    <= op_quotient_n;
        md_state_q       <= md_state_n;
      end

      unique case(1'b1)
        mult_en_i:
          mac_res_q <= mac_res_n;
        div_en_i:
          mac_res_q <= op_remainder_n;
        default:
          mac_res_q <= mac_res_q;
       endcase
    end
  end

  assign signed_mult      = (signed_mode_i != 2'b00);

  assign multdiv_result_o = div_en_i ? mac_res_q[31:0] : mac_res_n[31:0];

  // The 2 MSBs of mac_res_ext (mac_res_ext[34:33]) are always equal since:
  // 1. The 2 MSBs of the multiplicants are always equal, and
  // 2. The 16 MSBs of the addend (accum[33:18]) are always equal.
  // Thus, it is safe to ignore mac_res_ext[34].
  assign mac_res_signed =
      $signed({sign_a, mult_op_a}) * $signed({sign_b, mult_op_b}) + $signed(accum);
  assign mac_res_ext    = $unsigned(mac_res_signed);
  assign mac_res        = mac_res_ext[33:0];

  assign res_adder_h    = alu_adder_ext_i[33:1];

  assign next_remainder = is_greater_equal ? res_adder_h[31:0] : mac_res_q[31:0];
  assign next_quotient  = is_greater_equal ? {1'b0,op_quotient_q} | {1'b0,one_shift} :
                                             {1'b0,op_quotient_q};

  assign one_shift      = {31'b0, 1'b1} << div_counter_q;

  // The adder in the ALU computes alu_operand_a_o + alu_operand_b_o which means
  // Remainder - Divisor. If Remainder - Divisor >= 0, is_greater_equal is equal to 1,
  // the next Remainder is Remainder - Divisor contained in res_adder_h and the
  always_comb begin
    if ((mac_res_q[31] ^ op_denominator_q[31]) == 1'b0) begin
      is_greater_equal = (res_adder_h[31] == 1'b0);
    end else begin
      is_greater_equal = mac_res_q[31];
    end
  end

  assign div_sign_a      = op_a_i[31] & signed_mode_i[0];
  assign div_sign_b      = op_b_i[31] & signed_mode_i[1];
  assign div_change_sign = div_sign_a ^ div_sign_b;
  assign rem_change_sign = div_sign_a;


  always_comb begin : md_fsm
    div_counter_n    = div_counter_q - 5'h1;
    op_remainder_n   = mac_res_q;
    op_quotient_n    = op_quotient_q;
    md_state_n       = md_state_q;
    op_numerator_n   = op_numerator_q;
    op_denominator_n = op_denominator_q;
    alu_operand_a_o  = {32'h0  , 1'b1};
    alu_operand_b_o  = {~op_b_i, 1'b1};
    div_valid        = 1'b0;

    unique case(md_state_q)
      MD_IDLE: begin
        if (operator_i == MD_OP_DIV) begin
          // Check if the Denominator is 0
          // quotient for division by 0
          op_remainder_n = '1;
          md_state_n     = equal_to_zero ? MD_FINISH : MD_ABS_A;
        end else begin
          // Check if the Denominator is 0
          // remainder for division by 0
          op_remainder_n = {2'b0, op_a_i};
          md_state_n     = equal_to_zero ? MD_FINISH : MD_ABS_A;
        end
        // 0 - B = 0 iff B == 0
        alu_operand_a_o  = {32'h0  , 1'b1};
        alu_operand_b_o  = {~op_b_i, 1'b1};
        div_counter_n    = 5'd31;
      end

      MD_ABS_A: begin
        // quotient
        op_quotient_n   = '0;
        // A abs value
        op_numerator_n  = div_sign_a ? alu_adder_i : op_a_i;
        md_state_n      = MD_ABS_B;
        div_counter_n   = 5'd31;
        // ABS(A) = 0 - A
        alu_operand_a_o = {32'h0  , 1'b1};
        alu_operand_b_o = {~op_a_i, 1'b1};
      end

      MD_ABS_B: begin
        // remainder
        op_remainder_n   = { 33'h0, op_numerator_q[31]};
        // B abs value
        op_denominator_n = div_sign_b ? alu_adder_i : op_b_i;
        md_state_n       = MD_COMP;
        div_counter_n    = 5'd31;
        // ABS(B) = 0 - B
        alu_operand_a_o  = {32'h0  , 1'b1};
        alu_operand_b_o  = {~op_b_i, 1'b1};
      end

      MD_COMP: begin
        op_remainder_n  = {1'b0, next_remainder[31:0], op_numerator_q[div_counter_n]};
        op_quotient_n   = next_quotient[31:0];
        md_state_n      = (div_counter_q == 5'd1) ? MD_LAST : MD_COMP;
        // Division
        alu_operand_a_o = {mac_res_q[31:0], 1'b1};         // it contains the remainder
        alu_operand_b_o = {~op_denominator_q[31:0], 1'b1}; // -denominator two's compliment
      end

      MD_LAST: begin
        if (operator_i == MD_OP_DIV) begin
          // this time we save the quotient in op_remainder_n (i.e. mac_res_q) since
          // we do not need anymore the remainder
          op_remainder_n = {1'b0, next_quotient};
        end else begin
          // this time we do not save the quotient anymore since we need only the remainder
          op_remainder_n = {2'b0, next_remainder[31:0]};
        end
        // Division
        alu_operand_a_o  = {mac_res_q[31:0], 1'b1};         // it contains the remainder
        alu_operand_b_o  = {~op_denominator_q[31:0], 1'b1}; // -denominator two's compliment

        md_state_n = MD_CHANGE_SIGN;
      end

      MD_CHANGE_SIGN: begin
        md_state_n  = MD_FINISH;
        if (operator_i == MD_OP_DIV) begin
          op_remainder_n = (div_change_sign) ? {2'h0,alu_adder_i} : mac_res_q;
        end else begin
          op_remainder_n = (rem_change_sign) ? {2'h0,alu_adder_i} : mac_res_q;
        end
        // ABS(Quotient) = 0 - Quotient (or Remainder)
        alu_operand_a_o  = {32'h0  , 1'b1};
        alu_operand_b_o  = {~mac_res_q[31:0], 1'b1};
      end

      MD_FINISH: begin
        md_state_n = MD_IDLE;
        div_valid   = 1'b1;
      end

      default: begin
        md_state_n = md_fsm_e'(1'bX);
      end
    endcase // md_state_q
  end

  assign valid_o = mult_valid | div_valid;

  always_comb begin : mult_fsm
    mult_op_a    = op_a_i[`OP_L];
    mult_op_b    = op_b_i[`OP_L];
    sign_a       = 1'b0;
    sign_b       = 1'b0;
    accum        = mac_res_q;
    mac_res_n    = mac_res;
    mult_state_n = mult_state_q;
    mult_valid   = 1'b0;

    unique case (mult_state_q)

      ALBL: begin
        // al*bl
        mult_op_a = op_a_i[`OP_L];
        mult_op_b = op_b_i[`OP_L];
        sign_a    = 1'b0;
        sign_b    = 1'b0;
        accum     = '0;
        mac_res_n = mac_res;
        mult_state_n = ALBH;
      end

      ALBH: begin
        // al*bh<<16
        mult_op_a = op_a_i[`OP_L];
        mult_op_b = op_b_i[`OP_H];
        sign_a    = 1'b0;
        sign_b    = signed_mode_i[1] & op_b_i[31];
        // result of AL*BL (in mac_res_q) always unsigned with no carry, so carries_q always 00
        accum     = {18'b0,mac_res_q[31:16]};
        if (operator_i == MD_OP_MULL) begin
          mac_res_n = {2'b0,mac_res[`OP_L],mac_res_q[`OP_L]};
        end else begin
          // MD_OP_MULH
          mac_res_n = mac_res;
        end
        mult_state_n = AHBL;
      end

      AHBL: begin
        // ah*bl<<16
        mult_op_a = op_a_i[`OP_H];
        mult_op_b = op_b_i[`OP_L];
        sign_a    = signed_mode_i[0] & op_a_i[31];
        sign_b    = 1'b0;
        if (operator_i == MD_OP_MULL) begin
          accum        = {18'b0,mac_res_q[31:16]};
          mac_res_n    = {2'b0,mac_res[15:0],mac_res_q[15:0]};
          mult_valid   = 1'b1;
          mult_state_n = ALBL;
        end else begin
          accum        = mac_res_q;
          mac_res_n    = mac_res;
          mult_state_n = AHBH;
        end
      end

      AHBH: begin
        // only MD_OP_MULH here
        // ah*bh
        mult_op_a = op_a_i[`OP_H];
        mult_op_b = op_b_i[`OP_H];
        sign_a    = signed_mode_i[0] & op_a_i[31];
        sign_b    = signed_mode_i[1] & op_b_i[31];
        accum[17: 0]  = mac_res_q[33:16];
        accum[33:18]  = {16{signed_mult & mac_res_q[33]}};
        // result of AH*BL is not signed only if signed_mode_i == 2'b00
        mac_res_n    = mac_res;
        mult_state_n = ALBL;
        mult_valid   = 1'b1;
      end
      default: begin
        mult_state_n = mult_fsm_e'(1'bX);
      end
    endcase // mult_state_q
  end

endmodule // ibex_mult
