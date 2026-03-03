// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * OTBN bignum multiply and accumulate module
 *
 * This module supports 3 types of multiplication and accumulation instructions:
 * - bn.mulqacc: Regular 64-bit multiplication with result shifting and accumulation capabilities
 *     (see instruction description). The 64-bit multiplication operands can be selected from the
 *     input WDRs. Executes in one cycle.
 * - bn.mulv(l): Vectorized multiplication of 32-bit elements from a 256-bit vector (WDR). Operates
 *     either vector-element-wise or multiples each element of vector A with a fixed element of
 *     vector B. The later mode is referred to as lane-wise multiplication. Processes a full vector
 *     and operates on 64-bit chunks. This instruction takes 4 cycles to execute.
 * - bn.mulvm(l): Vectorized Montgomery multiplication of 32-bit elements from a 256-bit vector
 *     (WDR). Also supports the lane mode. Processes a full vector and operates on 64-bit chunks.
 *     For each chunk it takes 3 cycles to compute the Montgomery multiplication. The instruction
 *     therefore executes over 12 cycles. The final conditional subtraction step of the Montgomery
 *     algorithm is neglected to optimize area and timing. See below for more details about the
 *     Montgomery implementation.
 *
 * The multi-cycle instructions stall the OTBN pipeline by keeping the operation_valid_o flag low
 * until the computation has finished. This multi-cycle logic is controlled by an internal FSM.
 * This FSM does also set the internal data path control signals. It also forwards control signals
 * to the otbn_predecode module for SCA countermeasure control signals which require predecoding.
 *
 * The main components of this module are a vectorized 64-bit multiplier capable of computing
 * either 1 64-bit or 2 32-bit multiplications at once, a vectorized 256-bit adder as well as the
 * 256-bit wide ACC WSR. These components allow to implement the regular 64-bit multiplication with
 * accumulation in a single cycle. For the vectorized multiplications, the multiplications are
 * pipelined on the vectorized multiplier to save area. Per cycle one 64-bit chunk of the vector
 * is processed and the partial results are combined to a full 256-bit vector using the ACC WSR.
 * The Montgomery multiplication requires 3 multiplications per vector chunk. These are also
 * pipelined on the 64-bit multiplier and the final result is constructed in the ACC WSR. Both
 * vectorized instructions clear the ACC WSR at the end of the instruction using random data
 * supplied externally.
 *
 * Montgomery implementation details:
 * The Montgomery algorithm efficiently computes a multiplication and reduction by converting
 * divisions to power of two divisions and modulo operations. This module implements the unsigned
 * version of Montgomery and does not compute the conditional subtraction step to optimize for area
 * and timing.
 *
 * Algorithm inputs:
 * - a, b: Operands in [0, q[
 * - d:    Bitwidth of operands (fixed to 32 bit)
 * - q:    Modulus in ]0, 2^d]
 * - mu:   Montgomery constant, precomputed, mu = (-q)^(-1) mod 2^d
 *
 * The required constants q and mu are expected to be in the MOD WSR at following locations:
 * q  @ [31:0]
 * mu @ [63:32]
 *
 * Outputs:
 * - r = a*b * 2^(-d) mod q and r in [0,q[
 *
 * This can be computed with (where []_d are the lower d bits, []^d are the higher d bits):
 *   c = a * b
 *   r = [c + [[c]_d * mu]_d * q]^d
 *   if r >= q then                      <- not implemented in this HW
 *       return r - q
 *   return r
 *
 * Due to the neglected conditional subtraction the result is in ]0,2q[ and can be reduced into
 * ]0,q[ using the bn.addvm instruction.
 *
 * As the 3 multiplications are pipelined onto the multiplier it requires two additional registers
 * for intermediate values named "TMP" and "C". These registers hold the following intermediate
 * values when processing a vector chunk:
 *   Cycle 1:  Reg(TMP) = [a*b]_d,     Reg(C) = a*b
 *   Cycle 2:  Reg(TMP) = [TMP*mu]_d,  Reg(C) = a*b
 *   Cycle 3:  Output   = c + (TMP)*q mod q = [c + (TMP)*q]^d
 *
 * These two hidden registers are cleared with randomness after each vector chunk (i.e., every 3
 * cycles).
 */
module otbn_mac_bignum
  import otbn_pkg::*;
(
  input logic clk_i,
  input logic rst_ni,

  input mac_bignum_operation_t operation_i,
  input logic                  mac_en_i,
  input logic                  mac_commit_i,

  output logic [WLEN-1:0] operation_result_o,
  output logic            operation_valid_o,
  output flags_t          operation_flags_o,
  output flags_t          operation_flags_en_o,
  output logic            operation_intg_violation_err_o,

  input  mac_bignum_predec_t     predec_i,
  input  mac_bignum_predec_dyn_t predec_dyn_i,
  output mac_bignum_predec_dyn_t predec_dyn_next_o,
  output logic                   predec_dyn_next_valid_o,
  output logic                   predec_error_o,

  input  logic [WLEN-1:0] urnd_data_i,
  input  logic            sec_wipe_urnd_i,
  input  logic            sec_wipe_running_i,
  output logic            sec_wipe_err_o,

  output logic [ExtWLEN-1:0] ispr_acc_intg_o,
  input  logic [ExtWLEN-1:0] ispr_acc_wr_data_intg_i,
  input  logic               ispr_acc_wr_en_i,

  input  logic [ExtWLEN-1:0] ispr_mod_intg_i,

  output logic state_err_o
);
  import prim_util_pkg::vbits;

  localparam int HWLEN             = WLEN / 2;
  localparam int ExtHWLEN          = HWLEN * 39 / 32;
  localparam int BaseWordsPerHWLEN = HWLEN / 32;

  localparam int QWLEN             = WLEN / 4;
  localparam int ExtQWLEN          = QWLEN * 39 / 32;
  localparam int BaseWordsPerQWLEN = QWLEN / 32;

  //////////////////
  // ACC Register //
  //////////////////
  logic                          acc_wr_en;
  logic                          acc_clear_en;
  logic [ExtWLEN-1:0]            acc_intg_d;
  logic [ExtWLEN-1:0]            acc_intg_q;
  logic [ExtWLEN-1:0]            acc_intg_calc;
  logic [WLEN-1:0]               acc_no_intg_d;
  logic [WLEN-1:0]               acc_no_intg_q;
  logic [2*BaseWordsPerWLEN-1:0] acc_intg_err;
  for (genvar i_word = 0; i_word < BaseWordsPerWLEN; i_word++) begin : g_acc_words
    prim_secded_inv_39_32_enc i_secded_enc (
      .data_i(acc_no_intg_d[i_word * 32 +: 32]),
      .data_o(acc_intg_calc[i_word * 39 +: 39])
    );
    prim_secded_inv_39_32_dec i_secded_dec (
      .data_i    (acc_intg_q[i_word * 39 +: 39]),
      .data_o    (/* unused because we abort on any integrity error */),
      .syndrome_o(/* unused */),
      .err_o     (acc_intg_err[i_word * 2 +: 2])
    );
    assign acc_no_intg_q[i_word * 32 +: 32] = acc_intg_q[i_word * 39 +: 32];
  end

  always_ff @(posedge clk_i) begin
    if (acc_wr_en) begin
      acc_intg_q <= acc_intg_d;
    end
  end

  ////////////////
  // Register C //
  ////////////////
  logic                           c_wr_en;
  logic                           c_clear_en;
  logic [ExtHWLEN-1:0]            c_intg_d;
  logic [ExtHWLEN-1:0]            c_intg_q;
  logic [HWLEN-1:0]               c_new_value;
  logic [HWLEN-1:0]               c_clear_data;
  logic [HWLEN-1:0]               c_no_intg_d;
  logic [HWLEN-1:0]               c_no_intg_q;
  logic [2*BaseWordsPerHWLEN-1:0] c_intg_err;

  for (genvar i_word = 0; i_word < BaseWordsPerHWLEN; i_word++) begin : g_c_words
    prim_secded_inv_39_32_enc i_c_secded_enc (
      .data_i(c_no_intg_d[i_word * 32 +: 32]),
      .data_o(c_intg_d[i_word * 39 +: 39])
    );
    prim_secded_inv_39_32_dec i_c_secded_dec (
      .data_i    (c_intg_q[i_word * 39 +: 39]),
      .data_o    (/* unused because we abort on any integrity error */),
      .syndrome_o(/* unused */),
      .err_o     (c_intg_err[i_word * 2 +: 2])
    );
    assign c_no_intg_q[i_word * 32 +: 32] = c_intg_q[i_word * 39 +: 32];
  end

  // TODO: generate permutation of URND based upon netlist secret
  assign c_clear_data = urnd_data_i[HWLEN-1:0];

  always_comb begin
    c_no_intg_d = '0;
    unique case (1'b1)
      (sec_wipe_urnd_i | c_clear_en): c_no_intg_d = c_clear_data;
      default:                        c_no_intg_d = c_new_value;
    endcase
  end

  always_ff @(posedge clk_i) begin
    if (c_wr_en) begin
      c_intg_q <= c_intg_d;
    end
  end

  //////////////////
  // Register TMP //
  //////////////////
  logic                           tmp_wr_en;
  logic                           tmp_clear_en;
  logic [ExtQWLEN-1:0]            tmp_intg_d;
  logic [ExtQWLEN-1:0]            tmp_intg_q;
  logic [QWLEN-1:0]               tmp_new_value;
  logic [QWLEN-1:0]               tmp_clear_data;
  logic [QWLEN-1:0]               tmp_no_intg_d;
  logic [QWLEN-1:0]               tmp_no_intg_q;
  logic [2*BaseWordsPerQWLEN-1:0] tmp_intg_err;

  for (genvar i_word = 0; i_word < BaseWordsPerQWLEN; i_word++) begin : g_tmp_words
    prim_secded_inv_39_32_enc i_tmp_secded_enc (
      .data_i(tmp_no_intg_d[i_word * 32 +: 32]),
      .data_o(tmp_intg_d[i_word * 39 +: 39])
    );
    prim_secded_inv_39_32_dec i_tmp_secded_dec (
      .data_i    (tmp_intg_q[i_word * 39 +: 39]),
      .data_o    (/* unused because we abort on any integrity error */),
      .syndrome_o(/* unused */),
      .err_o     (tmp_intg_err[i_word * 2 +: 2])
    );
    assign tmp_no_intg_q[i_word * 32 +: 32] = tmp_intg_q[i_word * 39 +: 32];
  end

  // TODO: generate permutation of URND based upon netlist secret
  assign tmp_clear_data = urnd_data_i[QWLEN-1:0];

  always_comb begin
    tmp_no_intg_d = '0;
    unique case (1'b1)
      (sec_wipe_urnd_i | tmp_clear_en): tmp_no_intg_d = tmp_clear_data;
      default:                          tmp_no_intg_d = tmp_new_value;
    endcase
  end

  always_ff @(posedge clk_i) begin
    if (tmp_wr_en) begin
      tmp_intg_q <= tmp_intg_d;
    end
  end

  ////////////////////
  // Input blanking //
  ////////////////////
  logic [WLEN-1:0] operand_a_blanked;
  logic [WLEN-1:0] operand_b_blanked;

  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(WLEN)) u_operand_a_blanker (
    .in_i (operation_i.operand_a),
    .en_i (predec_i.op_en),
    .out_o(operand_a_blanked)
  );

  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(WLEN)) u_operand_b_blanker (
    .in_i (operation_i.operand_b),
    .en_i (predec_i.op_en),
    .out_o(operand_b_blanked)
  );

  ///////////////////
  // MOD Extractor //
  ///////////////////
  // The modulus and Montgomery constant are expected in the MOD register at:
  // q  @ [31:0]
  // mu @ [63:32]
  logic [2*39-1:0] ispr_mod_intg_blanked;
  logic            unused_ispr_mod_intg;
  logic [63:0]     mod_no_intg;
  logic [3:0]      mod_intg_err;

  // Only the first two 32-bit words are required as q and mu reside in the first 64 bits.
  // This needs blanking to avoid mixing values from MOD with the input B when performing a regular
  // multiplication.
  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(2*39)) u_mod_blanker (
    .in_i (ispr_mod_intg_i[2*39-1:0]),
    .en_i (predec_i.is_mod),
    .out_o(ispr_mod_intg_blanked)
  );

  assign unused_ispr_mod_intg = ^ispr_mod_intg_i[ExtWLEN-1:2*39];

  for (genvar i_word = 0; i_word < 2; i_word++) begin : g_mod_words
    prim_secded_inv_39_32_dec i_mod_secded_dec (
      .data_i    (ispr_mod_intg_blanked[i_word * 39 +: 39]),
      .data_o    (/* unused because we abort on any integrity error */),
      .syndrome_o(/* unused */),
      .err_o     (mod_intg_err[i_word * 2 +: 2])
    );
    assign mod_no_intg[i_word * 32 +: 32] = ispr_mod_intg_blanked[i_word * 39 +: 32];
  end

  // For the 32-bit vectorized multiplications we have to replicate the constants
  logic [QWLEN-1:0] mod_q;  // The Montgomery modulus q
  logic [QWLEN-1:0] mod_mu; // The Montgomery constant mu

  assign mod_q  = {2{mod_no_intg[31:0]}};
  assign mod_mu = {2{mod_no_intg[63:32]}};

  ///////////////////////////
  // Vectorized multiplier //
  ///////////////////////////

  // Input operand quad word selection
  logic [QWLEN-1:0] qword_a;
  logic [QWLEN-1:0] qword_b;
  logic [QWLEN-1:0] qword_b_lane;

  // This MUX is predecoded to optimize timing
  assign qword_a = operand_a_blanked[predec_dyn_i.op_a_qw_sel * QWLEN +: QWLEN];

  // Pick the lane index and replicate
  assign qword_b_lane = {2{operand_b_blanked[predec_i.lane_index * 32 +: 32]}};

  // These MUXs are predecoded to optimize timing
  assign qword_b = predec_i.is_lane ? qword_b_lane :
                                      operand_b_blanked[predec_dyn_i.op_b_qw_sel * QWLEN +: QWLEN];

  // Multiplier operand selection
  logic [QWLEN-1:0] mul_op_a;
  logic [QWLEN-1:0] mul_op_b;
  logic [HWLEN-1:0] mul_res;

  assign mul_op_a = predec_dyn_i.mul_op_a_tmp_sel ? qword_a : tmp_no_intg_q;

  // Here a regular MUX is sufficient because q and mu are blanked for regular multiplications.
  // For Montgomery these values are anyway combined.
  always_comb begin
    unique case (predec_dyn_i.mul_op_b_sel)
      MulOpB:  mul_op_b = qword_b;
      MulOpMu: mul_op_b = mod_mu;
      MulOpq:  mul_op_b = mod_q;
      default: mul_op_b = qword_b;
    endcase
  end

  otbn_vec_multiplier u_vec_multiplier (
    .operand_a_i(mul_op_a),
    .operand_b_i(mul_op_b),
    .elen_i     (predec_i.elen),
    .result_o   (mul_res)
  );

  //////////////////////////////////////////////////////////
  // Multiplier result handling for vectorized Montgomery //
  //////////////////////////////////////////////////////////
  // Store the full result to register C
  assign c_new_value = mul_res;

  // Store only the lower ELEN bits of the parallel multiplications to register TMP.
  assign tmp_new_value = {mul_res[32 * 2 +: 32], mul_res[32 * 0 +: 32]};

  // Adder operand blanking and extension
  logic [HWLEN-1:0] half_mul_res_add;
  logic [WLEN-1:0]  mul_res_add;

  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(HWLEN)) u_half_mul_res_blanker (
    .in_i (mul_res),
    .en_i (predec_dyn_i.mul_add_en),
    .out_o(half_mul_res_add)
  );

  assign mul_res_add = {{HWLEN{1'b0}}, half_mul_res_add};

  //////////////////////////////////////////////////////////////////////
  // Multiplier result handling for regular vectorized multiplication //
  //////////////////////////////////////////////////////////////////////
  // Truncating and blanking of results towards the ACC merger for vectorized multiplication
  // without modulo reduction.
  logic [QWLEN-1:0] mul_res_merger;

  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(QWLEN)) u_mul_res_merger_blanker (
    .in_i ({mul_res[32 * 2 +: 32], mul_res[32 * 0 +: 32]}),
    .en_i (predec_i.mul_merger_en),
    .out_o(mul_res_merger)
  );

  ///////////////////////////////////////////////////////////
  // Multiplier result handling for regular multiplication //
  ///////////////////////////////////////////////////////////
  // Blank and shift result prior to accumulation
  logic [HWLEN-1:0] mul_res_pre_shifted;
  logic [WLEN-1:0]  mul_res_shifted;

  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(HWLEN)) u_mul_res_shift_blanker (
    .in_i (mul_res),
    .en_i (predec_i.mul_shift_en),
    .out_o(mul_res_pre_shifted)
  );

  // Shift the HWLEN multiply result into a WLEN word before accumulating using the shift amount
  // supplied in the instruction (pre_acc_shift_imm). The shift is on a QWORD granularity and a
  // 192-bit shift will drop the upper QWORD of the multiply result.
  always_comb begin
    mul_res_shifted = '0;

    unique case (operation_i.pre_acc_shift_imm)
      2'd0:    mul_res_shifted = {{QWLEN * 2{1'b0}}, mul_res_pre_shifted};
      2'd1:    mul_res_shifted = {{QWLEN{1'b0}}, mul_res_pre_shifted, {QWLEN{1'b0}}};
      2'd2:    mul_res_shifted = {mul_res_pre_shifted, {QWLEN * 2{1'b0}}};
      2'd3:    mul_res_shifted = {mul_res_pre_shifted[QWLEN-1:0], {QWLEN * 3{1'b0}}};
      default: mul_res_shifted = {{QWLEN * 2{1'b0}}, mul_res_pre_shifted};
    endcase
  end

  `ASSERT_KNOWN_IF(PreAccShiftImmKnown, operation_i.pre_acc_shift_imm, mac_en_i)

  //////////////////////
  // Vectorized Adder //
  //////////////////////
  logic [HWLEN-1:0] c_blanked;
  logic [WLEN-1:0]  acc_add_blanked;
  logic [WLEN-1:0]  adder_op_a;
  logic [WLEN-1:0]  adder_op_b;
  logic [WLEN-1:0]  adder_result;

  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(HWLEN)) u_reg_c_blanker (
    .in_i (c_no_intg_q),
    .en_i (predec_dyn_i.c_add_en),
    .out_o(c_blanked)
  );

  // SEC_CM: DATA_REG_SW.SCA
  // acc_add_en is so if .Z set in MULQACC (zero_acc) so accumulator reads as 0
  prim_blanker #(.Width(WLEN)) u_acc_add_blanker (
    .in_i (acc_no_intg_q),
    .en_i (predec_i.acc_add_en),
    .out_o(acc_add_blanked)
  );

  // Perform the additions. The vectorized path only uses the lower 128 bits of the adder.
  // The full 256 bit width is used for bn.mulqacc instructions.
  // Here the MUXs can be implemented with OR gates because input signals are exclusively blanked
  // for the whole duration of an instruction.
  // - c_blanked is only non zero for Montgomery multiplications where mul_res_shifted is unused.
  //   Vice versa mul_res_shifted is only non zero for regular multiplications where c_blanked is
  //   unused.
  // - mul_res_add is only non zero for vectorized multiplications where acc_add_blanked is unused.
  //   Vice versa acc_add_blanked is only non zero for regular multiplications where mul_res_add is
  //   blanked.
  assign adder_op_a = {{128{1'b0}}, c_blanked} | mul_res_shifted;
  assign adder_op_b = mul_res_add              | acc_add_blanked;

  otbn_vec_adder #(
    .LVLEN(WLEN),
    .LVChunkLEN(VChunkLEN)
  ) u_vec_adder (
    .operand_a_i       (adder_op_a),
    .operand_b_i       (adder_op_b),
    .operand_b_invert_i(1'b0), // always add, never subtract
    .carries_in_i      ('0),
    .use_ext_carry_i   (predec_i.adder_carry_sel),
    .sum_o             (adder_result),
    .carries_out_o     (/* unused */)
  );

  /////////////////////////////////////////////
  // Vectorized adder modulo result handling //
  /////////////////////////////////////////////
  logic [QWLEN-1:0] adder_result_mod;
  logic [QWLEN-1:0] montg_r;

  // Montgomery upper bit selection
  // Take only the upper ELEN bits of the addition.
  // The result is "r" of the montgomery algorithm
  assign adder_result_mod = {adder_result[32 * 3 +: 32], adder_result[32 * 1 +: 32]};

  prim_blanker #(.Width(QWLEN)) u_add_mod_blanker (
    .in_i (adder_result_mod),
    .en_i (predec_dyn_i.add_mod_en),
    .out_o(montg_r)
  );

  // The conditional subtraction is not performed to optimize timing and area.
  logic [QWLEN-1:0] montg_r_cor;
  assign montg_r_cor = montg_r;

  ///////////////////////////////////////////
  // ACC merging for vectorized operations //
  ///////////////////////////////////////////
  logic [1:0]       acc_qw_sel;
  logic [QWLEN-1:0] acc_new_qw;
  logic [WLEN-1:0]  acc_old;
  logic [WLEN-1:0]  acc_merged;

  // This MUX can be implemented using a regular OR because both inputs are exclusively blanked.
  // The mul_res_merger comes directly from a blanker which is only active (passes data through) if
  // we are performing a regular vectorized multiplication (default or lane). In this case the
  // montg_r_cor is all zero as the signal is blanked with u_add_mod_blanker. During a Montgomery
  // multiplication the montg_r_cor contains the data but mul_res_merger is blanked.
  // These blankers are exclusively used for the whole duration of an instruction.
  assign acc_new_qw = montg_r_cor | mul_res_merger;

  // This blanker is used to zero the ACC register
  prim_blanker #(.Width(WLEN)) u_acc_merger_blanker (
    .in_i (acc_no_intg_q),
    .en_i (predec_dyn_i.acc_merger_en),
    .out_o(acc_old)
  );

  // Place the computed 64-bit chunk at the desired location in the ACC register.
  assign acc_merged[0*QWLEN+:QWLEN] = (acc_qw_sel == 2'd0) ? acc_new_qw : acc_old[0*QWLEN+:QWLEN];
  assign acc_merged[1*QWLEN+:QWLEN] = (acc_qw_sel == 2'd1) ? acc_new_qw : acc_old[1*QWLEN+:QWLEN];
  assign acc_merged[2*QWLEN+:QWLEN] = (acc_qw_sel == 2'd2) ? acc_new_qw : acc_old[2*QWLEN+:QWLEN];
  assign acc_merged[3*QWLEN+:QWLEN] = (acc_qw_sel == 2'd3) ? acc_new_qw : acc_old[3*QWLEN+:QWLEN];

  //////////////////////////////////////////////////////
  // Adder result handling for regular multiplication //
  //////////////////////////////////////////////////////
  logic [WLEN-1:0] adder_result_blanked;
  logic [WLEN-1:0] regular_acc_update_value;

  prim_blanker #(.Width(WLEN)) u_add_res_blanker (
    .in_i (adder_result),
    .en_i (predec_i.add_res_en),
    .out_o(adder_result_blanked)
  );

  assign regular_acc_update_value = operation_i.shift_acc ?
      {{HWLEN{1'b0}}, adder_result_blanked[HWLEN+:HWLEN]} :
      adder_result_blanked;

  /////////////////
  // Flag update //
  /////////////////
  // Vectorized operation never updates flags
  logic [1:0] adder_result_hw_is_zero;

  // Split zero check between the two halves of the result. This is used for flag setting (see
  // below).
  assign adder_result_hw_is_zero[0] = adder_result_blanked[WLEN/2-1:0] == 'h0;
  assign adder_result_hw_is_zero[1] = adder_result_blanked[WLEN/2+:WLEN/2] == 'h0;

  assign operation_flags_o.L    = adder_result_blanked[0];
  // L is always updated for .WO, and for .SO when writing to the lower half-word
  assign operation_flags_en_o.L = predec_i.is_vec       ? 1'b0                         :
                                  operation_i.shift_acc ? ~operation_i.wr_hw_sel_upper : 1'b1;

  // For .SO M is taken from the top-bit of shifted out half-word, otherwise it is taken from the
  // top-bit of the full result.
  assign operation_flags_o.M    = operation_i.shift_acc ? adder_result_blanked[WLEN/2-1] :
                                                          adder_result_blanked[WLEN-1];
  // M is always updated for .WO, and for .SO when writing to the upper half-word.
  assign operation_flags_en_o.M = predec_i.is_vec       ? 1'b0                        :
                                  operation_i.shift_acc ? operation_i.wr_hw_sel_upper : 1'b1;

  // For .SO Z is calculated from the shifted out half-word, otherwise it is calculated on the full
  // result.
  assign operation_flags_o.Z    = operation_i.shift_acc ? adder_result_hw_is_zero[0] :
                                                          &adder_result_hw_is_zero;

  // Z is updated for .WO. For .SO updates are based upon result and half-word:
  // - When writing to lower half-word always update Z.
  // - When writing to upper half-word clear Z if result is non-zero otherwise leave it alone.
  assign operation_flags_en_o.Z = predec_i.is_vec                                     ? 1'b0 :
                                  operation_i.shift_acc & operation_i.wr_hw_sel_upper ?
                                      ~adder_result_hw_is_zero[0] : 1'b1;

  // MAC never sets the carry flag
  assign operation_flags_o.C    = 1'b0;
  assign operation_flags_en_o.C = 1'b0;

  ////////////////
  // ACC update //
  ////////////////
  always_comb begin
    acc_no_intg_d = '0;
    unique case (1'b1)
      // Non-encoded inputs have to be encoded before writing to the register.
      (sec_wipe_urnd_i | acc_clear_en): begin
        acc_no_intg_d = urnd_data_i;
        acc_intg_d    = acc_intg_calc;
      end
      default: begin
        // If performing an ACC ISPR write the next accumulator value is taken from the ISPR write
        // data, otherwise it is drawn from the adder result or the vectorized ACC merger.
        if (ispr_acc_wr_en_i) begin
          acc_intg_d = ispr_acc_wr_data_intg_i;
        end else begin
          // The MUX for the input selection can be implemented with a simple OR gate because both
          // inputs are exclusively blanked. For regular multiplications acc_merged is zero because
          // the ACC merger just receives zero values. For vectorized multiplications (incl.
          // Montgomery) the regular_acc_update_value is zero because add_res_en is reset.
          // These blankers are exclusively used for the whole duration of an instruction.
          acc_no_intg_d = acc_merged | regular_acc_update_value;
          acc_intg_d    = acc_intg_calc;
        end
      end
    endcase
  end

  ///////////////////////////
  // Register Write Enable //
  ///////////////////////////
  // The raw write enables are set by the state machine. These are then combined with the input
  // signals which handle the validity of the instruction.
  logic acc_wr_en_raw;
  logic tmp_wr_en_raw;
  logic c_wr_en_raw;

  assign acc_wr_en = ((acc_wr_en_raw | acc_clear_en) & (mac_en_i & mac_commit_i))
                     | ispr_acc_wr_en_i | sec_wipe_urnd_i;
  assign tmp_wr_en = ((tmp_wr_en_raw | tmp_clear_en) & (mac_en_i & mac_commit_i))
                     | sec_wipe_urnd_i;
  assign c_wr_en   = ((c_wr_en_raw | c_clear_en) & (mac_en_i & mac_commit_i)) | sec_wipe_urnd_i;

  /////////////////////////
  // Multi-cycle control //
  /////////////////////////
  /**
   * The multi-cycle multiplications require dynamic control signals including predecoded signals.
   * This is implemented by stalling the OTBN pipeline and generating the control signals using an
   * internal state machine. When the result is valid, the pipeline is un-stalled by asserting the
   * valid flag.
   *
   * Any dynamic signal that requires predecoding is forwarded to the predecoder such that it can
   * be flopped. The predecoder will then depending on the forward request signal select between
   * predecoding signals based on the instruction or the forwarded signals .
   *
   * The following tables show the progression of the "dynamic" control signals for both
   * multi-cycle operations. There are additional control signals which do not change during the
   * execution. See the decoder / predecoder for how these are controlled. For any lane operation,
   * the qword selection control signal for operand B has no effect as the operand MUX uses
   * directly the lane index signal.
   *
   * Dynamic control signals for vectorized multiplication (QW = quad word = 64 bits)
   *
   * | Signal              |     Cycles (0-3)      | Predecoded |
   * |---------------------|-----------------------|------------|
   * | Step                | QW0 | QW1 | QW2 | QW3 |            |
   * |---------------------|-----|-----|-----|-----|------------|
   * | op_a_qw_sel         |   0 |   1 |   2 |   3 |        yes |
   * | op_b_qw_sel         |   0 |   1 |   2 |   3 |        yes |
   * | acc_qw_sel          |   0 |   1 |   2 |   3 |         no |
   * | acc_wr_en_raw       |   1 |   1 |   1 |   0 |         no |
   * | acc_clear_en        |   0 |   0 |   0 |   1 |         no |
   * | acc_merger_en       |   1 |   1 |   1 |   1 |        yes |
   * | operation_valid_raw |   0 |   0 |   0 |   1 |         no |
   *
   * Dynamic control signals for Montgomery multiplication (4 chunks processed over 3 cycles each)
   *
   * | Signal              |                       Cycles (0-11)                    | Predecoded |
   * |---------------------|--------------------------------------------------------|------------|
   * | Processed quad word |        QW0      ||       QW1       || QW2 ||    QW3    |            |
   * | Montgomery cycle    |  C0 |  C1 |  C2 ||  C0 |  C1 |  C2 || ... || ... |  C2 |            |
   * |---------------------|-----|-----|-----||-----|-----|-----||-----||-----|-----|------------|
   * | op_a_qw_sel         |   0 |   0 |   0 ||   1 |   1 |   1 ||     ||     |   3 |        yes |
   * | op_b_qw_sel         |   0 |   0 |   0 ||   1 |   1 |   1 ||     ||     |   3 |        yes |
   * | mul_op_a_tmp_sel    |   A | TMP | TMP ||   A | TMP | TMP ||     ||     | TMP |        yes |
   * | mul_op_b_sel        |   B |  Mu |   Q ||   B |  Mu |   Q ||     ||     |   Q |        yes |
   * | tmp_wr_en_raw       |   1 |   1 |   0 ||   1 |   1 |   0 ||     ||     |   0 |         no |
   * | tmp_clear_en        |   0 |   0 |   1 ||   0 |   0 |   1 ||     ||     |   1 |         no |
   * | c_wr_en_raw         |   1 |   0 |   0 ||   1 |   0 |   0 ||     ||     |   0 |         no |
   * | c_clear_en          |   0 |   0 |   1 ||   0 |   0 |   1 ||     ||     |   1 |         no |
   * | acc_qw_sel          |   0 |   0 |   0 ||   1 |   1 |   1 ||     ||     |   3 |         no |
   * | acc_wr_en_raw       |   0 |   0 |   1 ||   0 |   0 |   1 ||     ||     |   0 |         no |
   * | acc_clear_en        |   0 |   0 |   0 ||   0 |   0 |   0 ||     ||     |   1 |         no |
   * | mul_add_en          |   0 |   0 |   1 ||   0 |   0 |   1 ||     ||     |   1 |        yes |
   * | c_add_en            |   0 |   0 |   1 ||   0 |   0 |   1 ||     ||     |   1 |        yes |
   * | add_mod_en          |   0 |   0 |   1 ||   0 |   0 |   1 ||     ||     |   1 |        yes |
   * | acc_merger_en       |   0 |   0 |   1 ||   0 |   0 |   1 ||     ||     |   1 |        yes |
   * | operation_valid_raw |   0 |   0 |   0 ||   0 |   0 |   0 ||     ||     |   1 |         no |
   *
   * Because these control signal progressions have a repeating character, we generate for all
   * cycles the desired control signal "combinations" in the form of an array of signals. This
   * allows to implement the state machine as a counter which simply picks the required combination
   * based upon the current count from the arrays. We generate the progressions for each type of
   * multiplication (*_reg, *_vec, *_mod) and also separate the predecoded and regular control
   * signals to simplify the forwarding to the predecoder. The predecoded combinations are also
   * used to define the expected signals.
   *
   * In the following, the first part generates these signal combinations. The second part then is
   * the actual logic stepping through the cycles.
   */

  ///////////////////////////////////////////
  // Multi-cycle control signal generation //
  ///////////////////////////////////////////
  localparam int unsigned LatencyVec = 4;
  localparam int unsigned LatencyMod = 12;
  localparam int unsigned LatencyMax = LatencyVec > LatencyMod ? LatencyVec : LatencyMod;

  typedef struct packed {
    logic       tmp_wr_en_raw;
    logic       tmp_clear_en;
    logic       c_wr_en_raw;
    logic       c_clear_en;
    logic [1:0] acc_qw_sel;
    logic       acc_wr_en_raw;
    logic       acc_clear_en;
  } mac_contrl_t;

  localparam mac_contrl_t ControlDefault = '0;

  // The control and expected signals for a regular multiplication
  mac_contrl_t            contrl_reg;
  mac_bignum_predec_dyn_t expected_predec_dyn_reg;

  always_comb begin
    contrl_reg               = ControlDefault;
    contrl_reg.acc_wr_en_raw = 1'b1;

    expected_predec_dyn_reg             = MacBignumPredecDynDefault;
    expected_predec_dyn_reg.op_a_qw_sel = operation_i.operand_a_qw_sel;
    expected_predec_dyn_reg.op_b_qw_sel = operation_i.operand_b_qw_sel;
  end

  // The dynamic control and predecoding signals for all cycles of a vectorized multiplication.
  // See also table above.
  mac_contrl_t            contrl_vec[LatencyVec];
  mac_bignum_predec_dyn_t predec_vec[LatencyVec];

  always_comb begin
    contrl_vec = '{default: ControlDefault};
    predec_vec = '{default: MacBignumPredecDynDefault};

    for (int unsigned cycle = 0; cycle < LatencyVec; cycle++) begin
      contrl_vec[cycle].acc_qw_sel    = 2'(cycle);
      contrl_vec[cycle].acc_wr_en_raw = 1'b1;
      predec_vec[cycle].op_a_qw_sel   = 2'(cycle);
      predec_vec[cycle].op_b_qw_sel   = 2'(cycle);
      predec_vec[cycle].acc_merger_en = 1'b1;
    end

    // Disable write enable for ACC and clear ACC in last cycle
    contrl_vec[3].acc_wr_en_raw = 1'b0;
    contrl_vec[3].acc_clear_en  = 1'b1;
  end

  // The dynamic control and predecoding signals for the 3 Montgomery cycles as well as all 12
  // execution cycles. See also table above.
  localparam int unsigned LatencyMontgMul = 3;

  mac_contrl_t            contrl_mod_mul[LatencyMontgMul];
  mac_bignum_predec_dyn_t predec_mod_mul[LatencyMontgMul];
  mac_contrl_t            contrl_mod[LatencyMod];
  mac_bignum_predec_dyn_t predec_mod[LatencyMod];

  always_comb begin
    contrl_mod_mul = '{default: ControlDefault};
    predec_mod_mul = '{default: MacBignumPredecDynDefault};

    // First, construct the signals for the actual Montgomery multiplication. This is repeated for
    // each vector chunk.
    // Cycle 0
    contrl_mod_mul[0].tmp_wr_en_raw    = 1'b1;
    contrl_mod_mul[0].c_wr_en_raw      = 1'b1;
    // Cycle 1
    contrl_mod_mul[1].tmp_wr_en_raw    = 1'b1;
    predec_mod_mul[1].mul_op_a_tmp_sel = 1'b0;
    predec_mod_mul[1].mul_op_b_sel     = MulOpMu;
    // Cycle 2
    contrl_mod_mul[2].acc_wr_en_raw    = 1'b1;
    contrl_mod_mul[2].tmp_clear_en     = 1'b1; // Clear TMP with randomness
    contrl_mod_mul[2].c_clear_en       = 1'b1; // Clear C with randomness
    predec_mod_mul[2].mul_op_a_tmp_sel = 1'b0;
    predec_mod_mul[2].mul_op_b_sel     = MulOpq;
    predec_mod_mul[2].mul_add_en       = 1'b1;
    predec_mod_mul[2].c_add_en         = 1'b1;
    predec_mod_mul[2].add_mod_en       = 1'b1;
    predec_mod_mul[2].acc_merger_en    = 1'b1;

    // Construct the 4 * 3 = 12 cycles and set the correct qword selection
    for (int unsigned cycle = 0; cycle < LatencyMod; cycle++) begin
      contrl_mod[cycle]             = contrl_mod_mul[cycle % LatencyMontgMul];
      contrl_mod[cycle].acc_qw_sel  = 2'(cycle / LatencyMontgMul);
      predec_mod[cycle]             = predec_mod_mul[cycle % LatencyMontgMul];
      predec_mod[cycle].op_a_qw_sel = 2'(cycle / LatencyMontgMul);
      predec_mod[cycle].op_b_qw_sel = 2'(cycle / LatencyMontgMul);
    end

    // Clear ACC in the last cycle with randomness
    contrl_mod[LatencyMod - 1].acc_clear_en = 1'b1;
  end

  // Create helper 2D arrays to simplify the indexing in the actual signal selection. The first
  // dimension is to distinguish between regular (0) vs Montgomery (1) multiplication. The second
  // dimension represents the cycles. This allows a neat indexing using the is_mod control signal
  // as well as one common index width. See actual logic below.
  mac_contrl_t            contrl_multi[2][LatencyMax];
  mac_bignum_predec_dyn_t predec_multi[2][LatencyMax];

  always_comb begin
    // Vectorized multiplication (cycles 4-11 are unused)
    contrl_multi[0] = '{default: ControlDefault};
    predec_multi[0] = '{default: MacBignumPredecDynDefault};

    for (int unsigned cycle = 0; cycle < LatencyVec; cycle++) begin
      contrl_multi[0][cycle] = contrl_vec[cycle];
      predec_multi[0][cycle] = predec_vec[cycle];
    end

    // Montgomery multiplication
    contrl_multi[1] = '{default: ControlDefault};
    predec_multi[1] = '{default: MacBignumPredecDynDefault};

    for (int unsigned cycle = 0; cycle < LatencyMod; cycle++) begin
      contrl_multi[1][cycle] = contrl_mod[cycle];
      predec_multi[1][cycle] = predec_mod[cycle];
    end
  end

  ///////////////////////////////
  // Multi-cycle control logic //
  ///////////////////////////////
  // This is the actual logic controlling the execution and is based upon a cycle counter. This
  // counter is used as index into the previously "computed" control signal sequences. The selected
  // combination is then assigned to the actual control signals, forwarded to the predecoder or
  // used as expected signals.
  localparam int unsigned                CycleCountWidth = vbits(LatencyMax);
  localparam logic [CycleCountWidth-1:0] EndCycleVec     = CycleCountWidth'(LatencyVec - 1);
  localparam logic [CycleCountWidth-1:0] EndCycleMod     = CycleCountWidth'(LatencyMod - 1);

  logic operation_valid_raw;
  logic do_advance;

  mac_contrl_t            contrl;
  logic                   predec_dyn_next_valid_raw;
  mac_bignum_predec_dyn_t predec_dyn_next;
  mac_bignum_predec_dyn_t expected_predec_dyn;
  logic                   expected_mul_shift_en;
  logic                   expected_mul_merger_en;
  logic                   expected_add_res_en;

  logic [CycleCountWidth-1:0] current_cycle;
  logic [CycleCountWidth-1:0] next_cycle_raw;
  logic [CycleCountWidth-1:0] next_cycle;
  logic                       mod_finishing;
  logic                       vec_finishing;
  logic                       multi_finishing;

  // Evaluate whether this is the last cycle depending on type of multiplication.
  assign mod_finishing   = current_cycle == EndCycleMod;
  assign vec_finishing   = current_cycle == EndCycleVec;
  assign multi_finishing = predec_i.is_mod ? mod_finishing : vec_finishing;

  // next_cycle is used to select which predecoding signals should be forwarded. The +1 would
  // exceed the array bounds in the last cycle (as latency must not necessarily be a power of two).
  // For this case we take the signals of the first cycle but it does not matter because there
  // must be no forward request in the last cycle as in the last cycle the next instruction will be
  // predecoded. We must control and ensure this here because the predecoder does not know when BN
  // MAC will un-stall the pipeline.
  assign next_cycle = multi_finishing ? '0 : next_cycle_raw;

  `ASSERT(NoPredecDynNextForwardLastCycle_A,
          operation_valid_o |-> predec_dyn_next_valid_o == '0,
          clk_i, !rst_ni || !do_advance)

  always_comb begin
    // Default is the regular multiplication
    contrl                    = contrl_reg;
    expected_predec_dyn       = expected_predec_dyn_reg;
    // This controls whether we will forward dynamic predecode signals to the fetch stage while
    // progressing through multi-cycle states but does not factor in any errors.
    predec_dyn_next_valid_raw = 1'b0;
    predec_dyn_next           = MacBignumPredecDynDefault;

    // Static blankers
    expected_mul_shift_en  = 1'b0;
    expected_mul_merger_en = 1'b0;
    expected_add_res_en    = 1'b0;

    if (!predec_i.is_vec) begin
      // Regular multiplications are single cycle
      operation_valid_raw       = 1'b1;

      expected_mul_shift_en     = mac_en_i;
      expected_add_res_en       = mac_en_i;
    end else begin
      operation_valid_raw       = multi_finishing;
      contrl                    = contrl_multi[predec_i.is_mod][current_cycle];
      expected_predec_dyn       = predec_multi[predec_i.is_mod][current_cycle];

      // Suppress the forward request in the last cycle.
      predec_dyn_next_valid_raw = !multi_finishing;
      predec_dyn_next           = predec_multi[predec_i.is_mod][next_cycle];

      expected_mul_merger_en = predec_i.is_mod ? 1'b0 : mac_en_i;
    end
  end

  // For non modulo vectorized multiplications, the blanker must be active if the instructions
  // starts and it must definitively be high if it is already ongoing.
  `ASSERT(VecMulBlankerMulMergerEn_A,
          predec_i.is_vec && !predec_i.is_mod && ((current_cycle != '0) || mac_en_i)
          |-> expected_mul_merger_en,
          clk_i, !rst_ni || !do_advance)

  // Only advance when instruction is committing (if there is no error). Must not factor in local
  // errors as it would result in timing loops (errors factor into the commit signal).
  assign do_advance = mac_en_i & mac_commit_i;

  logic cycle_count_error;

  prim_count #(
    .Width(CycleCountWidth)
  ) u_cycle_count (
    .clk_i,
    .rst_ni,
    .clr_i             (operation_valid_o || sec_wipe_urnd_i),
    .set_i             ('0),
    .set_cnt_i         ('0),
    .incr_en_i         (1'b1),
    .decr_en_i         (1'b0),
    .step_i            (CycleCountWidth'(1)),
    .commit_i          (do_advance),
    .cnt_o             (current_cycle),
    .cnt_after_commit_o(next_cycle_raw),
    .err_o             (cycle_count_error)
  );

  // We have separate control signals to have a clean separation between the control logic and data
  // flow components.
  assign tmp_wr_en_raw = contrl.tmp_wr_en_raw;
  assign tmp_clear_en  = contrl.tmp_clear_en;
  assign c_wr_en_raw   = contrl.c_wr_en_raw;
  assign c_clear_en    = contrl.c_clear_en;
  assign acc_qw_sel    = contrl.acc_qw_sel;
  assign acc_wr_en_raw = contrl.acc_wr_en_raw;
  assign acc_clear_en  = contrl.acc_clear_en;

  assign predec_dyn_next_o       = predec_dyn_next;
  assign predec_dyn_next_valid_o = predec_dyn_next_valid_raw && do_advance;

  // Assert that counters are always in bounds. In case the count gets FIed, the counter's
  // countermeasure will fire, so there is no need of escalating these errors as state error.
  logic current_cycle_oob;
  logic next_cycle_oob;
  assign current_cycle_oob = current_cycle  > (predec_i.is_mod ? CycleCountWidth'(LatencyMod) :
                                                                 CycleCountWidth'(LatencyVec));
  assign next_cycle_oob    = next_cycle_raw > (predec_i.is_mod ? CycleCountWidth'(LatencyMod) :
                                                                 CycleCountWidth'(LatencyVec));

  // Note, these assertions must be disabled when testing the counter countermeasures as
  // these will fire when the count is manipulated to a value out of bound.
  `ASSERT(CurrentCycleIsInBounds_A, !current_cycle_oob, clk_i, !rst_ni || !do_advance)

  `ASSERT(NextCycleIsInBounds_A, !next_cycle_oob, clk_i, !rst_ni || !do_advance)

  // Out of bound checks are only used for assertions.
  logic unused_oob;
  assign unused_oob = current_cycle_oob ^ next_cycle_oob;

  // The prim_count enforces that there is an ERROR_TRIGGER_ALERT assertion checking that this
  // error escalates correctly.
  assign state_err_o = cycle_count_error;

  //////////////////////
  // Result selection //
  //////////////////////
  // Here the output MUX can be replaced with a simple OR gate because both inputs are exclusively
  // blanked. For regular multiplications the acc_merged is zero because the ACC merging just
  // receives zero inputs. For vectorized multiplications (incl. Montgomery) the
  // adder_result_blanked is blanked. These blankers are exclusively used for the whole duration of
  // an instruction.
  // For a regular multiplication shift_acc only applies to the new value written to the
  // accumulator.
  assign operation_result_o = acc_merged | adder_result_blanked;
  assign operation_valid_o  = operation_valid_raw & mac_en_i;

  /////////////////////
  // Integrity error //
  /////////////////////
  // Propagate integrity error only if a register is used and MAC is enabled
  logic tmp_used;
  logic c_used;
  logic mod_used;
  logic acc_used;
  // TMP is used if multiplier operand a is set to TMP
  assign tmp_used = mac_en_i && (!predec_dyn_i.mul_op_a_tmp_sel);
  // c is used if its blanker is enabled
  assign c_used = mac_en_i & predec_dyn_i.c_add_en;
  // MOD is used if modulo operation is active
  assign mod_used = mac_en_i && predec_i.is_mod;
  // The ACC is used if we do not reset it (regular mul) or require it to merge the current
  // quarter word
  assign acc_used = mac_en_i && (predec_dyn_i.acc_merger_en ||
                                 (!predec_i.is_vec && ~operation_i.zero_acc));

  assign operation_intg_violation_err_o = (tmp_used & |(tmp_intg_err)) ||
                                          (c_used   & |(c_intg_err))   ||
                                          (mod_used & |(mod_intg_err)) ||
                                          (acc_used & |(acc_intg_err));

  //////////////////////
  // Redundancy check //
  //////////////////////
  logic                expected_op_en;
  logic                expected_is_vec;
  logic                expected_is_mod;
  logic                expected_is_lane;
  mac_elen_e           expected_elen;
  logic [NVecProc-1:0] expected_adder_carry_sel;
  logic [2:0]          expected_lane_index;
  logic                expected_acc_add_en;

  // SEC_CM: CTRL.REDUN
  assign expected_op_en           = mac_en_i;
  assign expected_is_vec          = operation_i.is_vec;
  assign expected_is_mod          = operation_i.is_mod;
  assign expected_is_lane         = operation_i.is_lane;
  assign expected_elen            = operation_i.elen;
  assign expected_adder_carry_sel = operation_i.adder_carry_sel;
  assign expected_lane_index      = operation_i.lane_index;
  assign expected_acc_add_en      = ~operation_i.zero_acc & mac_en_i & !operation_i.is_vec;

  // Separate the predecode comparison for debugging reasons
  logic predec_error;
  logic predec_dyn_error;

  assign predec_error = |{expected_op_en           != predec_i.op_en,
                          expected_is_vec          != predec_i.is_vec,
                          expected_is_mod          != predec_i.is_mod,
                          expected_is_lane         != predec_i.is_lane,
                          expected_elen            != predec_i.elen,
                          expected_adder_carry_sel != predec_i.adder_carry_sel,
                          expected_lane_index      != predec_i.lane_index,
                          expected_acc_add_en      != predec_i.acc_add_en,
                          expected_mul_shift_en    != predec_i.mul_shift_en,
                          expected_mul_merger_en   != predec_i.mul_merger_en,
                          expected_add_res_en      != predec_i.add_res_en};

  assign predec_dyn_error = expected_predec_dyn != predec_dyn_i;

  assign predec_error_o = predec_error || predec_dyn_error;

  /////////////////////////////////////
  // Register and secure wipe output //
  /////////////////////////////////////
  assign ispr_acc_intg_o = acc_intg_q;

  assign sec_wipe_err_o = sec_wipe_urnd_i & ~sec_wipe_running_i;

  `ASSERT(NoISPRAccWrAndMacEn, ~(ispr_acc_wr_en_i & mac_en_i))
endmodule
