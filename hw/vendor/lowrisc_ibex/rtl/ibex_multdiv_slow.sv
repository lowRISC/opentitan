// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Slow Multiplier and Division
 *
 * Baugh-Wooley multiplier and Long Division
 */

`include "prim_assert.sv"

module ibex_multdiv_slow (
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

  logic [ 4:0] multdiv_state_q, multdiv_state_d, multdiv_state_m1;
  typedef enum logic [2:0] {
    MD_IDLE, MD_ABS_A, MD_ABS_B, MD_COMP, MD_LAST, MD_CHANGE_SIGN, MD_FINISH
  } md_fsm_e;
  md_fsm_e md_state_q, md_state_d;

  logic [32:0] accum_window_q, accum_window_d;

  logic [32:0] res_adder_l;
  logic [32:0] res_adder_h;

  logic [32:0] op_b_shift_q, op_b_shift_d;
  logic [32:0] op_a_shift_q, op_a_shift_d;
  logic [32:0] op_a_ext, op_b_ext;
  logic [32:0] one_shift;
  logic [32:0] op_a_bw_pp, op_a_bw_last_pp;
  logic [31:0] b_0;
  logic        sign_a, sign_b;
  logic [32:0] next_reminder, next_quotient;
  logic [32:0] op_remainder;
  logic [31:0] op_numerator_q, op_numerator_d;
  logic        is_greater_equal;
  logic        div_change_sign, rem_change_sign;

   // (accum_window_q + op_a_shift_q)
  assign res_adder_l       = alu_adder_ext_i[32:0];
   // (accum_window_q + op_a_shift_q)>>1
  assign res_adder_h       = alu_adder_ext_i[33:1];

  always_comb begin
    alu_operand_a_o   = accum_window_q;
    multdiv_result_o  = div_en_i ? accum_window_q[31:0] : res_adder_l;

    unique case(operator_i)

      MD_OP_MULL: begin
        alu_operand_b_o   = op_a_bw_pp;
      end

      MD_OP_MULH: begin
        alu_operand_b_o = (md_state_q == MD_LAST) ? op_a_bw_last_pp : op_a_bw_pp;
      end

      default: begin
        unique case(md_state_q)
          MD_IDLE: begin
            // 0 - B = 0 iff B == 0
            alu_operand_a_o     = {32'h0  , 1'b1};
            alu_operand_b_o     = {~op_b_i, 1'b1};
          end
          MD_ABS_A: begin
            // ABS(A) = 0 - A
            alu_operand_a_o     = {32'h0  , 1'b1};
            alu_operand_b_o     = {~op_a_i, 1'b1};
          end
          MD_ABS_B: begin
            // ABS(B) = 0 - B
            alu_operand_a_o     = {32'h0  , 1'b1};
            alu_operand_b_o     = {~op_b_i, 1'b1};
          end
          MD_CHANGE_SIGN: begin
            // ABS(Quotient) = 0 - Quotient (or Reminder)
            alu_operand_a_o     = {32'h0  , 1'b1};
            alu_operand_b_o     = {~accum_window_q[31:0], 1'b1};
          end
          default: begin
            // Division
            alu_operand_a_o     = {accum_window_q[31:0], 1'b1}; // it contains the reminder
            alu_operand_b_o     = {~op_b_shift_q[31:0], 1'b1};  // -denominator two's compliment
          end
        endcase
      end
    endcase
  end

  // The adder in the ALU computes alu_operand_a_o + alu_operand_b_o which means
  // Reminder - Divisor. If Reminder - Divisor >= 0, is_greater_equal is equal to 1,
  // the next Reminder is Reminder - Divisor contained in res_adder_h and the
  // Quotient multdiv_state_q-th bit is set to 1 using the shift register op_b_shift_q.
  assign is_greater_equal = ((accum_window_q[31] ^ op_b_shift_q[31]) == 1'b0) ?
      (res_adder_h[31] == 1'b0) : accum_window_q[31];

  assign one_shift     = {32'b0, 1'b1} << multdiv_state_q;

  assign next_reminder = is_greater_equal ? res_adder_h              : op_remainder;
  assign next_quotient = is_greater_equal ? op_a_shift_q | one_shift : op_a_shift_q;

  assign b_0             = {32{op_b_shift_q[0]}};

  // build the partial product
  assign op_a_bw_pp       = { ~(op_a_shift_q[32] & op_b_shift_q[0]),  (op_a_shift_q[31:0] & b_0) };
  assign op_a_bw_last_pp  = {  (op_a_shift_q[32] & op_b_shift_q[0]), ~(op_a_shift_q[31:0] & b_0) };

  assign sign_a   = op_a_i[31] & signed_mode_i[0];
  assign sign_b   = op_b_i[31] & signed_mode_i[1];

  assign op_a_ext = {sign_a, op_a_i};
  assign op_b_ext = {sign_b, op_b_i};

  // division
  assign op_remainder = accum_window_q[32:0];

  assign multdiv_state_m1  = multdiv_state_q - 5'h1;
  assign div_change_sign  = sign_a ^ sign_b;
  assign rem_change_sign  = sign_a;

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_multdiv_state_q
    if (!rst_ni) begin
      multdiv_state_q  <= 5'h0;
      accum_window_q   <= 33'h0;
      op_b_shift_q     <= 33'h0;
      op_a_shift_q     <= 33'h0;
      op_numerator_q   <= 32'h0;
      md_state_q       <= MD_IDLE;
    end else begin
      multdiv_state_q  <= multdiv_state_d;
      accum_window_q   <= accum_window_d;
      op_b_shift_q     <= op_b_shift_d;
      op_a_shift_q     <= op_a_shift_d;
      op_numerator_q   <= op_numerator_d;
      md_state_q       <= md_state_d;
    end
  end

  always_comb begin
    multdiv_state_d  = multdiv_state_q;
    accum_window_d   = accum_window_q;
    op_b_shift_d     = op_b_shift_q;
    op_a_shift_d     = op_a_shift_q;
    op_numerator_d   = op_numerator_q;
    md_state_d       = md_state_q;
    if (mult_en_i || div_en_i) begin
      unique case(md_state_q)
        MD_IDLE: begin
          unique case(operator_i)
            MD_OP_MULL: begin
              op_a_shift_d   = op_a_ext << 1;
              accum_window_d = {       ~(op_a_ext[32]   &     op_b_i[0]),
                                         op_a_ext[31:0] & {32{op_b_i[0]}}  };
              op_b_shift_d   = op_b_ext >> 1;
              md_state_d     = MD_COMP;
            end
            MD_OP_MULH: begin
              op_a_shift_d   = op_a_ext;
              accum_window_d = { 1'b1, ~(op_a_ext[32]   &     op_b_i[0]),
                                         op_a_ext[31:1] & {31{op_b_i[0]}}  };
              op_b_shift_d   = op_b_ext >> 1;
              md_state_d     = MD_COMP;
            end
            MD_OP_DIV: begin
              // Check if the Denominator is 0
              // quotient for division by 0
              accum_window_d = {33{1'b1}};
              md_state_d     = equal_to_zero ? MD_FINISH : MD_ABS_A;
            end
            default: begin
              // Check if the Denominator is 0
              // reminder for division by 0
              accum_window_d = op_a_ext;
              md_state_d     = equal_to_zero ? MD_FINISH : MD_ABS_A;
            end
          endcase
          multdiv_state_d   = 5'd31;
        end

        MD_ABS_A: begin
          // quotient
          op_a_shift_d   = '0;
          // A abs value
          op_numerator_d = sign_a ? alu_adder_i : op_a_i;
          md_state_d     = MD_ABS_B;
        end

        MD_ABS_B: begin
          // reminder
          accum_window_d = { 32'h0, op_numerator_q[31]};
          // B abs value
          op_b_shift_d   = sign_b ? alu_adder_i : op_b_i;
          md_state_d     = MD_COMP;
        end

        MD_COMP: begin
          multdiv_state_d   = multdiv_state_m1;
          unique case(operator_i)
            MD_OP_MULL: begin
              accum_window_d = res_adder_l;
              op_a_shift_d   = op_a_shift_q << 1;
              op_b_shift_d   = op_b_shift_q >> 1;
            end
            MD_OP_MULH: begin
              accum_window_d = res_adder_h;
              op_a_shift_d   = op_a_shift_q;
              op_b_shift_d   = op_b_shift_q >> 1;
            end
            default: begin
              accum_window_d = {next_reminder[31:0], op_numerator_q[multdiv_state_m1]};
              op_a_shift_d   = next_quotient;
            end
          endcase

          md_state_d = (multdiv_state_q == 5'd1) ? MD_LAST : MD_COMP;
        end

        MD_LAST: begin
          unique case(operator_i)
            MD_OP_MULL: begin
              accum_window_d = res_adder_l;
              md_state_d     = MD_IDLE;
            end
            MD_OP_MULH: begin
              accum_window_d = res_adder_l;
              md_state_d     = MD_IDLE;
            end
            MD_OP_DIV: begin
              // this time we save the quotient in accum_window_q since we do not need anymore the
              // reminder
              accum_window_d = next_quotient;
              md_state_d     = MD_CHANGE_SIGN;
            end
            default: begin
              // this time we do not save the quotient anymore since we need only the reminder
              accum_window_d = {1'b0, next_reminder[31:0]};
              md_state_d     = MD_CHANGE_SIGN;
            end
          endcase
        end

        MD_CHANGE_SIGN: begin
          md_state_d = MD_FINISH;
          unique case(operator_i)
            MD_OP_DIV:
              accum_window_d = (div_change_sign) ? alu_adder_i : accum_window_q;
            default:
              accum_window_d = (rem_change_sign) ? alu_adder_i : accum_window_q;
          endcase
        end

        MD_FINISH: begin
          md_state_d = MD_IDLE;
        end

        default: begin
          md_state_d = MD_IDLE;
        end
        endcase // md_state_q
      end
  end

  assign valid_o = (md_state_q == MD_FINISH) |
                   (md_state_q == MD_LAST &
                   (operator_i == MD_OP_MULL |
                    operator_i == MD_OP_MULH));

  // State must be valid.
  `ASSERT(IbexMultDivStateValid, md_state_q inside {
      MD_IDLE, MD_ABS_A, MD_ABS_B, MD_COMP, MD_LAST, MD_CHANGE_SIGN, MD_FINISH
      }, clk_i, !rst_ni)

endmodule // ibex_mult
