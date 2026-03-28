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
 * - bn.mulv(l): Vectorized multiplication of 32-bit elements from 256-bit vectors (WDRs). Operates
 *     either vector-element-wise or multiples each element of vector A with a fixed element of
 *     vector B. The later mode is referred to as lane-wise multiplication. Performs two 32-bit
 *     multiplications in parallel and takes 4 cycles to process the 256-bit vectors.
 * - bn.mulvm(l): Vectorized Montgomery multiplication of 32-bit elements from 256-bit vectors
 *     (WDRs). Also supports the lane mode. Performs two Montgomery multiplications in parallel
 *     over the duration of 3 cycles. It takes 3 * 4 = 12 cycles to process the 256-bit vectors.
 *     The final conditional subtraction step of the Montgomery algorithm is neglected to optimize
 *     area and timing. See below for more details about the Montgomery implementation.
 *
 * The multi-cycle instructions stall the OTBN pipeline by keeping the operation_valid_o flag low
 * until the computation has finished. This multi-cycle logic is controlled by an internal FSM
 * which controls the data path. It operates in tandem with a duplicate in the instruction fetch
 * stage. This duplicate generates the predecoded signals which are compared here to the locally
 * generated signals.
 *
 * The main components of this module are a vectorized 64-bit multiplier capable of computing
 * either 1 64-bit or 2 32-bit multiplications at once, a vectorized 256-bit adder as well as the
 * 256-bit wide ACC WSR. These components allow to implement the regular 64-bit multiplication with
 * accumulation in a single cycle. For the vectorized multiplications, the multiplications are
 * pipelined on the vectorized multiplier to save area. The partial results are combined to a full
 * 256-bit vector using the ACC WSR. As the Montgomery multiplication requires 3 multiplications
 * these are also pipelined on the vectorized multiplier and the final result is constructed in the
 * ACC WSR. Both vectorized instructions clear the ACC WSR at the end of the instruction using
 * random data supplied externally. See below.
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
 * values when computing a Montgomery multiplication:
 *   Cycle 1:  Reg(TMP) = [a*b]_d,     Reg(C) = a*b
 *   Cycle 2:  Reg(TMP) = [TMP*mu]_d,  Reg(C) = a*b
 *   Cycle 3:  Output   = c + (TMP)*q mod q = [c + (TMP)*q]^d
 *
 * These two hidden registers are cleared with randomness after each vector chunk (i.e., every 3
 * cycles).
 *
 * Register clearing details:
 * As described, the ACC WSR and the two hidden registers are cleared using randomness. The ACC WSR
 * is directly cleared by writing the current value of URND to it. The two hidden registers are
 * cleared with a permutation of URND as shown below. The permutation is based on a netlist secret.
 *
 *              +-------------+
 * URND --+---->| Permutation |-----+----------+
 *        |     +-------------+     |          |
 *        |                      [127:0]   [192:128]
 *        v                         v          v
 *     +-----+                   +-----+    +-----+
 *     | ACC |                   |  C  |    | TMP |
 *     +-----+                   +-----+    +-----+
 */
module otbn_mac_bignum
  import otbn_pkg::*;
#(
  // Compile-time permutation for URND permutation
  parameter bn_mac_urnd_perm_t RndCnstBnMacUrndPerm = RndCnstBnMacUrndPermDefault
) (
  input logic clk_i,
  input logic rst_ni,

  input mac_bignum_operation_t operation_i,
  // The signal mac_en_i must only used by the FSM or by assertions! Everywhere else use the
  // predecoded version. This ensures that there is a redundancy check in place.
  input logic                  mac_en_i,
  input logic                  mac_commit_i,

  output logic [WLEN-1:0] operation_result_o,
  output logic            operation_valid_o,
  output flags_t          operation_flags_o,
  output flags_t          operation_flags_en_o,
  output logic            operation_intg_violation_err_o,

  input  mac_bignum_predec_t predec_i,
  output logic               predec_error_o,

  input  logic [WLEN-1:0] urnd_data_i,
  input  logic            sec_wipe_urnd_i,
  input  logic            sec_wipe_running_i,
  output logic            sec_wipe_err_o,

  // Signals whenever the URND input is used to clear any of the internal registers. This is
  // required to advance the URND PRNG if the SecMuteUrnd parameter is set.
  output logic urnd_used_o,

  output logic [ExtWLEN-1:0] ispr_acc_intg_o,
  input  logic [ExtWLEN-1:0] ispr_acc_wr_data_intg_i,
  input  logic               ispr_acc_wr_en_i,

  input  logic [ExtWLEN-1:0] ispr_mod_intg_i,

  output logic state_err_o
);
  localparam int unsigned ELEN = QWLEN / 2;

  // URND permutations for register clearing
  logic [WLEN-1:0]  urnd_permutation;
  logic             unused_urnd_permutation;
  logic [WLEN-1:0]  acc_clear_data;
  logic [HWLEN-1:0] c_clear_data;
  logic [QWLEN-1:0] tmp_clear_data;

  for (genvar i = 0; i < WLEN; i++) begin : gen_urnd_perm
    assign urnd_permutation[i] = urnd_data_i[RndCnstBnMacUrndPerm[i]];
  end

  assign acc_clear_data = urnd_data_i;
  assign c_clear_data   = urnd_permutation[HWLEN-1:0];
  assign tmp_clear_data = urnd_permutation[HWLEN+:QWLEN];

  assign unused_urnd_permutation = ^urnd_permutation[HWLEN + QWLEN +: QWLEN];

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
    .en_i (predec_i.mac_en),
    .out_o(operand_a_blanked)
  );

  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(WLEN)) u_operand_b_blanker (
    .in_i (operation_i.operand_b),
    .en_i (predec_i.mac_en),
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

  // This MUX is predecoded to optimize timing.
  assign qword_a = operand_a_blanked[predec_i.op_a_qw_sel * QWLEN +: QWLEN];

  // The qword_b MUXing is elementwise to implement the lane functionality.
  // These 8-to-1 MUXs are predecoded to optimize timing.
  assign qword_b[   0+:ELEN] = operand_b_blanked[predec_i.op_b_elem0_sel * ELEN +: ELEN];
  assign qword_b[ELEN+:ELEN] = operand_b_blanked[predec_i.op_b_elem1_sel * ELEN +: ELEN];

  // Multiplier operand selection
  logic [QWLEN-1:0] mul_op_a;
  logic [QWLEN-1:0] mul_op_b;
  logic [HWLEN-1:0] mul_res;

  assign mul_op_a = predec_i.mul_op_a_tmp_sel ? qword_a : tmp_no_intg_q;

  // Here a regular MUX is sufficient because q and mu are blanked for regular multiplications.
  // For Montgomery these values are anyway combined.
  always_comb begin
    unique case (predec_i.mul_op_b_sel)
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
  assign tmp_new_value = {mul_res[QWLEN +: QWLEN / 2], mul_res[0 +: QWLEN / 2]};

  // Adder operand blanking and extension
  logic [HWLEN-1:0] half_mul_res_add;
  logic [WLEN-1:0]  mul_res_add;

  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(HWLEN)) u_half_mul_res_blanker (
    .in_i (mul_res),
    .en_i (predec_i.mul_add_en),
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
    .in_i (tmp_new_value),
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
      // The default is the first case but with the blanker disabled, so the output is '0.
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
    .en_i (predec_i.c_add_en),
    .out_o(c_blanked)
  );

  // SEC_CM: DATA_REG_SW.SCA
  // acc_add_en is so if .Z set in MULQACC (zero_acc) so accumulator reads as 0
  prim_blanker #(.Width(WLEN)) u_acc_add_blanker (
    .in_i (acc_no_intg_q),
    .en_i (predec_i.acc_add_en),
    .out_o(acc_add_blanked)
  );

  // Perform the additions. The vectorized path only uses the lower 128 bits of the adder and
  // operates on 64-bit elements. The full 256 bit width is used for bn.mulqacc instructions.
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
    .LVChunkLEN(QWLEN)
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
    .en_i (predec_i.add_mod_en),
    .out_o(montg_r)
  );

  // The conditional subtraction is not performed to optimize timing and area.
  // It can be performed using the bn.addvm instruction with a zero vector.
  logic [QWLEN-1:0] montg_r_cor;
  assign montg_r_cor = montg_r;

  ///////////////////////////////////////////
  // ACC merging for vectorized operations //
  ///////////////////////////////////////////
  logic [QWLEN-1:0] acc_new_qw;
  logic [WLEN-1:0]  acc_blanked;
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
    .en_i (predec_i.acc_merger_en),
    .out_o(acc_blanked)
  );

  // Place the computed 64-bit chunk at the desired location in the ACC register.
  for (genvar qw = 0; qw < VLEN/QWLEN; qw++) begin : gen_acc_merged
    assign acc_merged[qw * QWLEN +: QWLEN] = predec_i.acc_qw_sel[qw] ?
        acc_new_qw : acc_blanked[qw * QWLEN +: QWLEN];
  end

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
  assign operation_flags_en_o.Z =
      predec_i.is_vec                                     ? 1'b0                        :
      operation_i.shift_acc & operation_i.wr_hw_sel_upper ? ~adder_result_hw_is_zero[0] : 1'b1;

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
        acc_no_intg_d = acc_clear_data;
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

  assign acc_wr_en = ((acc_wr_en_raw | acc_clear_en) & (predec_i.mac_en & mac_commit_i))
                     | ispr_acc_wr_en_i | sec_wipe_urnd_i;
  assign tmp_wr_en = ((tmp_wr_en_raw | tmp_clear_en) & (predec_i.mac_en & mac_commit_i))
                     | sec_wipe_urnd_i;
  assign c_wr_en   = ((c_wr_en_raw | c_clear_en) & (predec_i.mac_en & mac_commit_i))
                     | sec_wipe_urnd_i;

  /////////////////////////
  // Multi-cycle control //
  /////////////////////////
  // The multi-cycle execution is controlled by a FSM. This FSM works in tandem with a duplicate
  // in the instruction fetch stage. The duplicate operates one cycle in advance and provides the
  // predecoded signals. These signals are compared to the ones generated here.
  mac_bignum_contrl_t contrl;
  mac_bignum_predec_t expected_predec;

  otbn_mac_bignum_fsm u_mac_bignum_fsm (
    .clk_i,
    .rst_ni,

    // This FSM here must use the decoded signals as the counterpart operates on the predecoded
    // signals. Otherwise both FSMs would be controlled with the same control signals.
    .start_i          (mac_en_i),
    .mac_en_i         (mac_en_i),
    .is_vec_i         (operation_i.is_vec),
    .is_mod_i         (operation_i.is_mod),
    .is_lane_i        (operation_i.is_lane),
    .lane_index_i     (operation_i.lane_index),
    .elen_i           (operation_i.elen),
    .adder_carry_sel_i(operation_i.adder_carry_sel),
    .acc_add_en_i     (operation_i.acc_add_en),
    .op_a_qw_sel_i    (operation_i.op_a_qw_sel_raw),
    .op_b_elem0_sel_i (operation_i.op_b_elem0_sel_raw),
    .op_b_elem1_sel_i (operation_i.op_b_elem1_sel_raw),

    .sec_wipe_i(sec_wipe_urnd_i),

    .contrl_o (contrl),
    .predec_o (expected_predec),
    .is_busy_o(/* only used in predecoder */),

    // Any tampering on the internal state will abort the execution.
    .state_err_o(state_err_o)
  );

  // For non modulo vectorized multiplications, the blanker must be active if the instructions
  // starts and it must definitively be high if it is already ongoing.
  `ASSERT(VecMulBlankerMulMergerEn_A,
          predec_i.is_vec && !predec_i.is_mod && predec_i.mac_en
          |-> predec_i.mul_merger_en,
          clk_i, !rst_ni || !predec_i.mac_en)

  // We have separate control signals to have a clean separation between the control logic and data
  // path components.
  assign tmp_wr_en_raw = contrl.tmp_wr_en_raw;
  assign tmp_clear_en  = contrl.tmp_clear_en;
  assign c_wr_en_raw   = contrl.c_wr_en_raw;
  assign c_clear_en    = contrl.c_clear_en;
  assign acc_wr_en_raw = contrl.acc_wr_en_raw;
  assign acc_clear_en  = contrl.acc_clear_en;

  // We must signal that we used URND so the PRNG is advanced even if the SecMuteUrnd parameter is
  // set.
  assign urnd_used_o = tmp_clear_en || c_clear_en || acc_clear_en;

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
  assign operation_valid_o  = predec_i.operation_valid_raw & predec_i.mac_en;

  /////////////////////
  // Integrity error //
  /////////////////////
  // Propagate integrity error only if a register is used and MAC is enabled
  logic tmp_used;
  logic c_used;
  logic mod_used;
  logic acc_used;
  // TMP is used if multiplier operand a is set to TMP
  assign tmp_used = predec_i.mac_en && !predec_i.mul_op_a_tmp_sel;
  // c is used if its blanker is enabled
  assign c_used = predec_i.mac_en & predec_i.c_add_en;
  // MOD is used if modulo operation is active
  assign mod_used = predec_i.mac_en && predec_i.is_mod;
  // The ACC is used if we do not reset it (regular mul) or require it to merge the current
  // quarter word
  assign acc_used = predec_i.mac_en && (predec_i.acc_merger_en || predec_i.acc_add_en);

  assign operation_intg_violation_err_o = (tmp_used && |(tmp_intg_err)) ||
                                          (c_used   && |(c_intg_err))   ||
                                          (mod_used && |(mod_intg_err)) ||
                                          (acc_used && |(acc_intg_err));

  //////////////////////
  // Redundancy check //
  //////////////////////
  // SEC_CM: CTRL.REDUN
  assign predec_error_o = expected_predec != predec_i;

  /////////////////////////////////////
  // Register and secure wipe output //
  /////////////////////////////////////
  assign ispr_acc_intg_o = acc_intg_q;

  assign sec_wipe_err_o = sec_wipe_urnd_i & ~sec_wipe_running_i;

  `ASSERT(NoISPRAccWrAndMacEn, ~(ispr_acc_wr_en_i & mac_en_i))

  // Only one QWORD must be overwritten at the same time.
  `ASSERT(AccQwSelOnehot_A,
          predec_i.acc_merger_en |-> $onehot(predec_i.acc_qw_sel),
          clk_i, !rst_ni || predec_error_o || state_err_o)

endmodule
