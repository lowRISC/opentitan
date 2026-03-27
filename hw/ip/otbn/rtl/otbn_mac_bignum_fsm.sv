// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module otbn_mac_bignum_fsm
  import otbn_pkg::*;
#(
  // This enforces that there is an assertion which checks that state_err_o generates an alert.
  parameter bit EnableAlertTriggerSVA = 1
)
(
  input  logic clk_i,
  input  logic rst_ni,

  input  logic                  start_i,
  input  logic                  mac_en_i,
  input  logic                  is_vec_i,
  input  logic                  is_mod_i,
  input  logic                  is_lane_i,
  input  logic [2:0]            lane_index_i,
  input  mac_elen_e             elen_i,
  input  logic [VLEN/QWLEN-1:0] adder_carry_sel_i,
  input  logic                  acc_add_en_i,
  input  logic [1:0]            op_a_qw_sel_i,
  input  logic [2:0]            op_b_elem0_sel_i,
  input  logic [2:0]            op_b_elem1_sel_i,

  output mac_bignum_contrl_t contrl_o,
  output mac_bignum_predec_t predec_o,
  output logic               is_busy_o,

  input  logic sec_wipe_i,
  output logic state_err_o
);

  import prim_util_pkg::vbits;

  /**
   * The multi-cycle multiplications require dynamic control signals including predecoded signals.
   * This is implemented by stalling the OTBN pipeline and generating the control signals using
   * this internal state machine. When the final result is ready, the pipeline is un-stalled by
   * asserting the valid flag.
   *
   * For security reasons, this FSM is instantiated twice, once in the predecoder and once in BN
   * MAC. All dynamic signals that require predecoding are generated with this FSM in the
   * instruction fetch stage such that they can be flopped. They are then forwarded to the BN MAC
   * which will compare them to the locally generated predecode signals (as expected signals).
   *
   * The following tables show the progression of the "dynamic" control signals for all
   * multi-cycle operations. There are additional control signals which do not change during the
   * execution.
   *
   * Dynamic control signals for vectorized multiplication (QW = quad word = 64 bits). In lane mode
   * the op_b_elemX_sel signals are overwritten by the FSM based upon decoded signals.
   *
   * | Signal              |     Cycles (0-3)      | Predecoded |
   * |---------------------|-----------------------|------------|
   * | Step                | QW0 | QW1 | QW2 | QW3 |            |
   * |---------------------|-----|-----|-----|-----|------------|
   * | op_a_qw_sel         |   0 |   1 |   2 |   3 |        yes |
   * | op_b_elem0_sel      |   0 |   2 |   4 |   6 |        yes |
   * | op_b_elem1_sel      |   1 |   3 |   5 |   7 |        yes |
   * | acc_qw_sel          |   0 |   1 |   2 |   3 |        yes |
   * | acc_wr_en_raw       |   1 |   1 |   1 |   0 |         no |
   * | acc_clear_en        |   0 |   0 |   0 |   1 |         no |
   * | acc_merger_en       |   1 |   1 |   1 |   1 |        yes |
   * | mul_shift_en        |   0 |   0 |   0 |   0 |        yes |
   * | add_res_en          |   0 |   0 |   0 |   0 |        yes |
   * | mul_merger_en       |   1 |   1 |   1 |   1 |        yes |
   * | operation_valid_raw |   0 |   0 |   0 |   1 |        yes |
   *
   * Dynamic control signals for Montgomery multiplication (4 chunks processed over 3 cycles each).
   * In lane mode the op_b_elemX_sel signals are overwritten by the FSM based upon decoded signals.
   *
   * | Signal              |                       Cycles (0-11)                    | Predecoded |
   * |---------------------|--------------------------------------------------------|------------|
   * | Processed quad word |        QW0      ||       QW1       || QW2 ||    QW3    |            |
   * | Montgomery cycle    |  C0 |  C1 |  C2 ||  C0 |  C1 |  C2 || ... || ... |  C2 |            |
   * |---------------------|-----|-----|-----||-----|-----|-----||-----||-----|-----|------------|
   * | op_a_qw_sel         |   0 |   0 |   0 ||   1 |   1 |   1 ||     ||     |   3 |        yes |
   * | op_b_elem0_sel      |   0 |   0 |   0 ||   2 |   2 |   2 ||     ||     |   6 |        yes |
   * | op_b_elem1_sel      |   1 |   1 |   1 ||   3 |   3 |   3 ||     ||     |   7 |        yes |
   * | mul_op_a_tmp_sel    |   A | TMP | TMP ||   A | TMP | TMP ||     ||     | TMP |        yes |
   * | mul_op_b_sel        |   B |  Mu |   Q ||   B |  Mu |   Q ||     ||     |   Q |        yes |
   * | tmp_wr_en_raw       |   1 |   1 |   0 ||   1 |   1 |   0 ||     ||     |   0 |         no |
   * | tmp_clear_en        |   0 |   0 |   1 ||   0 |   0 |   1 ||     ||     |   1 |         no |
   * | c_wr_en_raw         |   1 |   0 |   0 ||   1 |   0 |   0 ||     ||     |   0 |         no |
   * | c_clear_en          |   0 |   0 |   1 ||   0 |   0 |   1 ||     ||     |   1 |         no |
   * | acc_qw_sel          |   0 |   0 |   0 ||   1 |   1 |   1 ||     ||     |   3 |        yes |
   * | acc_wr_en_raw       |   0 |   0 |   1 ||   0 |   0 |   1 ||     ||     |   0 |         no |
   * | acc_clear_en        |   0 |   0 |   0 ||   0 |   0 |   0 ||     ||     |   1 |         no |
   * | mul_add_en          |   0 |   0 |   1 ||   0 |   0 |   1 ||     ||     |   1 |        yes |
   * | c_add_en            |   0 |   0 |   1 ||   0 |   0 |   1 ||     ||     |   1 |        yes |
   * | add_mod_en          |   0 |   0 |   1 ||   0 |   0 |   1 ||     ||     |   1 |        yes |
   * | acc_merger_en       |   0 |   0 |   1 ||   0 |   0 |   1 ||     ||     |   1 |        yes |
   * | mul_shift_en        |   0 |   0 |   0 ||   0 |   0 |   0 ||     ||     |   0 |        yes |
   * | add_res_en          |   0 |   0 |   0 ||   0 |   0 |   0 ||     ||     |   0 |        yes |
   * | mul_merger_en       |   0 |   0 |   0 ||   0 |   0 |   0 ||     ||     |   0 |        yes |
   * | operation_valid_raw |   0 |   0 |   0 ||   0 |   0 |   0 ||     ||     |   1 |        yes |
   *
   * Because these control signal progressions have a repeating character, we generate for all
   * cycles the desired control signal "combinations" in the form of an array of signals. This
   * allows to implement the state machine as a counter which simply picks the required combination
   * based upon the current count from the arrays. We generate the progressions for each type of
   * multiplication (*_reg, *_vec, *_mod) and also separate the predecoded and regular control
   * signals to simplify the flopping of the signals.
   *
   * In the following, the first part generates these signal combinations. The second part then is
   * the actual logic stepping through the cycles.
   */

  ///////////////////////////////////////////
  // Multi-cycle control signal generation //
  ///////////////////////////////////////////
  localparam mac_bignum_contrl_t ControlDefault = '0;

  typedef struct packed {
    logic [1:0]            op_a_qw_sel;
    logic [2:0]            op_b_elem0_sel;
    logic [2:0]            op_b_elem1_sel;
    logic                  mul_op_a_tmp_sel;
    mac_mul_op_b_sel_e     mul_op_b_sel;
    logic                  mul_add_en;
    logic                  c_add_en;
    logic                  add_mod_en;
    logic [VLEN/QWLEN-1:0] acc_qw_sel;
    logic                  acc_merger_en;
    logic                  mul_shift_en;
    logic                  mul_merger_en;
    logic                  add_res_en;
    logic                  operation_valid_raw;
  } mac_bignum_predec_dyn_t;

  localparam mac_bignum_predec_dyn_t PredecDynDefault = '{
    op_a_qw_sel:         2'b0,
    op_b_elem0_sel:      3'b0,
    op_b_elem1_sel:      3'b0,
    mul_op_a_tmp_sel:    1'b1,   // Select A as it is blanked
    mul_op_b_sel:        MulOpB,
    mul_add_en:          1'b0,
    c_add_en:            1'b0,
    add_mod_en:          1'b0,
    acc_qw_sel:          '0,
    acc_merger_en:       1'b0,
    mul_shift_en:        1'b0,
    mul_merger_en:       1'b0,
    add_res_en:          1'b0,
    operation_valid_raw: 1'b0
  };

  localparam int unsigned LatencyVec = 4;
  localparam int unsigned LatencyMod = 12;
  localparam int unsigned LatencyMax = LatencyVec > LatencyMod ? LatencyVec : LatencyMod;

  // The control and expected signals for a regular multiplication
  mac_bignum_contrl_t     contrl_reg;
  mac_bignum_predec_dyn_t predec_dyn_reg;

  always_comb begin
    contrl_reg               = ControlDefault;
    contrl_reg.acc_wr_en_raw = 1'b1;

    predec_dyn_reg                = PredecDynDefault;
    predec_dyn_reg.op_a_qw_sel    = op_a_qw_sel_i;
    predec_dyn_reg.op_b_elem0_sel = op_b_elem0_sel_i;
    predec_dyn_reg.op_b_elem1_sel = op_b_elem1_sel_i;
  end

  // The dynamic control and predecoding signals for all cycles of a vectorized multiplication.
  // See also table above.
  mac_bignum_contrl_t     contrl_vec[LatencyVec];
  mac_bignum_predec_dyn_t predec_vec[LatencyVec];

  always_comb begin
    contrl_vec = '{default: ControlDefault};
    predec_vec = '{default: PredecDynDefault};

    for (int unsigned cycle = 0; cycle < LatencyVec; cycle++) begin
      contrl_vec[cycle].acc_wr_en_raw  = 1'b1;
      predec_vec[cycle].op_a_qw_sel    = 2'(cycle);
      predec_vec[cycle].op_b_elem0_sel = 3'(2 * cycle);
      predec_vec[cycle].op_b_elem1_sel = 3'(2 * cycle + 1);
      predec_vec[cycle].acc_qw_sel     = (VLEN/QWLEN)'(unsigned'(1) << cycle);
      predec_vec[cycle].acc_merger_en  = 1'b1;
    end

    // Disable write enable for ACC and clear ACC in last cycle
    contrl_vec[3].acc_wr_en_raw = 1'b0;
    contrl_vec[3].acc_clear_en  = 1'b1;
  end

  // The dynamic control and predecoding signals for the 3 Montgomery cycles as well as all 12
  // execution cycles. See also table above.
  localparam int unsigned LatencyMontgMul = 3;

  mac_bignum_contrl_t     contrl_mod_mul[LatencyMontgMul];
  mac_bignum_predec_dyn_t predec_mod_mul[LatencyMontgMul];
  mac_bignum_contrl_t     contrl_mod[LatencyMod];
  mac_bignum_predec_dyn_t predec_mod[LatencyMod];

  always_comb begin
    contrl_mod_mul = '{default: ControlDefault};
    predec_mod_mul = '{default: PredecDynDefault};

    // First, construct the signals for the 3 Montgomery multiplication cycles. This pattern is
    // then repeated 4 times to process all 8 vector elements (2 at the same time).
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
      contrl_mod[cycle]                = contrl_mod_mul[cycle % LatencyMontgMul];
      predec_mod[cycle]                = predec_mod_mul[cycle % LatencyMontgMul];
      predec_mod[cycle].op_a_qw_sel    = 2'(cycle / LatencyMontgMul);
      predec_mod[cycle].op_b_elem0_sel = 3'(2 * (cycle / LatencyMontgMul));
      predec_mod[cycle].op_b_elem1_sel = 3'(2 * (cycle / LatencyMontgMul) + 1);
      predec_mod[cycle].acc_qw_sel     = (VLEN/QWLEN)'(unsigned'(1)) << (cycle / LatencyMontgMul);
    end

    // Clear ACC in the last cycle with randomness
    contrl_mod[LatencyMod - 1].acc_clear_en = 1'b1;
  end

  // Create helper 2D arrays to simplify the indexing in the actual signal selection. The first
  // dimension is to distinguish between regular (0) vs Montgomery (1) multiplication. The second
  // dimension represents the cycles. This allows a neat indexing using the is_mod control signal
  // as well as one common index width. See actual logic below.
  mac_bignum_contrl_t     contrl_multi[2][LatencyMax];
  mac_bignum_predec_dyn_t predec_multi[2][LatencyMax];

  always_comb begin
    // Vectorized multiplication (cycles 4-11 are unused)
    contrl_multi[0] = '{default: ControlDefault};
    predec_multi[0] = '{default: PredecDynDefault};

    for (int unsigned cycle = 0; cycle < LatencyVec; cycle++) begin
      contrl_multi[0][cycle] = contrl_vec[cycle];
      predec_multi[0][cycle] = predec_vec[cycle];
    end

    // Montgomery multiplication
    contrl_multi[1] = '{default: ControlDefault};
    predec_multi[1] = '{default: PredecDynDefault};

    for (int unsigned cycle = 0; cycle < LatencyMod; cycle++) begin
      contrl_multi[1][cycle] = contrl_mod[cycle];
      predec_multi[1][cycle] = predec_mod[cycle];
    end
  end

  //////////////////////////////////
  // Multi-cycle signal selection //
  //////////////////////////////////
  // This is the actual logic controlling the execution and is based upon a cycle counter. This
  // counter is used as index into the above "computed" static control signal sequences. The
  // selected combination is then assigned to the actual control signals, forwarded to the
  // predecoder or used as expected signals.
  localparam int unsigned                CycleCountWidth = vbits(LatencyMax);
  localparam logic [CycleCountWidth-1:0] EndCycleVec     = CycleCountWidth'(LatencyVec - 1);
  localparam logic [CycleCountWidth-1:0] EndCycleMod     = CycleCountWidth'(LatencyMod - 1);

  mac_bignum_predec_dyn_t     predec_dyn;
  logic [CycleCountWidth-1:0] current_cycle;
  logic                       mod_finishing;
  logic                       vec_finishing;
  logic                       multi_finishing;

  // Evaluate whether this is the last cycle depending on type of multiplication.
  assign mod_finishing   = current_cycle == EndCycleMod;
  assign vec_finishing   = current_cycle == EndCycleVec;
  assign multi_finishing = is_mod_i ? mod_finishing : vec_finishing;

  always_comb begin
    // Default is the regular multiplication
    contrl_o   = contrl_reg;
    predec_dyn = predec_dyn_reg;

    if (is_vec_i) begin
      contrl_o                       = contrl_multi[is_mod_i][current_cycle];
      predec_dyn                     = predec_multi[is_mod_i][current_cycle];
      predec_dyn.operation_valid_raw = mac_en_i & multi_finishing;
      predec_dyn.mul_merger_en       = is_mod_i ? 1'b0 : mac_en_i;
    end else begin
      // Regular multiplications are single cycle, set valid flag immediately.
      predec_dyn.operation_valid_raw = mac_en_i;
      predec_dyn.mul_shift_en        = mac_en_i;
      predec_dyn.add_res_en          = mac_en_i;
    end

    // Overwrite operand b selection if in lane mode
    if (is_lane_i) begin
      predec_dyn.op_b_elem0_sel = lane_index_i;
      predec_dyn.op_b_elem1_sel = lane_index_i;
    end
  end

  // Combine the static and dynamic predecoded signals into one signal.
  assign predec_o = '{
    mac_en:              mac_en_i,
    is_vec:              is_vec_i,
    is_mod:              is_mod_i,
    is_lane:             is_lane_i,
    lane_index:          lane_index_i,
    elen:                elen_i,
    adder_carry_sel:     adder_carry_sel_i,
    acc_add_en:          acc_add_en_i,
    op_a_qw_sel:         predec_dyn.op_a_qw_sel,
    op_b_elem0_sel:      predec_dyn.op_b_elem0_sel,
    op_b_elem1_sel:      predec_dyn.op_b_elem1_sel,
    mul_op_a_tmp_sel:    predec_dyn.mul_op_a_tmp_sel,
    mul_op_b_sel:        predec_dyn.mul_op_b_sel,
    mul_add_en:          predec_dyn.mul_add_en,
    c_add_en:            predec_dyn.c_add_en,
    add_mod_en:          predec_dyn.add_mod_en,
    acc_qw_sel:          predec_dyn.acc_qw_sel,
    acc_merger_en:       predec_dyn.acc_merger_en,
    mul_shift_en:        predec_dyn.mul_shift_en,
    mul_merger_en:       predec_dyn.mul_merger_en,
    add_res_en:          predec_dyn.add_res_en,
    operation_valid_raw: predec_dyn.operation_valid_raw
  };

  assign is_busy_o = current_cycle != 0;

  // Check that the counter is always in bounds so no undefined control signals are set.
  logic current_cycle_oob;
  assign current_cycle_oob = current_cycle  >= (is_mod_i ? CycleCountWidth'(LatencyMod) :
                                                           CycleCountWidth'(LatencyVec));

  // To be disabled when testing the out of bound check alert.
  `ASSERT(CurrentCycleIsInBounds_A, !current_cycle_oob, clk_i, !rst_ni || !mac_en_i)

  assign state_err_o = current_cycle_oob;

  ///////////////////
  // Cycle counter //
  ///////////////////
  logic [CycleCountWidth-1:0] cycle_count_d, cycle_count_q;
  logic cycle_do_step;
  logic cycle_clear;
  logic [CycleCountWidth-1:0] cycle_increment;

  assign current_cycle = cycle_count_q;

  assign cycle_clear     = predec_dyn.operation_valid_raw || sec_wipe_i;
  assign cycle_do_step   = mac_en_i && (start_i || is_busy_o);
  assign cycle_increment = CycleCountWidth'(1);

  always_comb begin
    cycle_count_d = cycle_count_q;

    if (cycle_clear) begin
      cycle_count_d = '0;
    end else if (cycle_do_step) begin
      // Wraparound should never happen but is ok.
      cycle_count_d = cycle_count_q + cycle_increment;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cycle_count_q <= '0;
    end else begin
      cycle_count_q <= cycle_count_d;
    end
  end

  //////////////////////
  // Alert assertions //
  //////////////////////
`ifdef INC_ASSERT
  //VCS coverage off
  // pragma coverage off

  // There is an alert assertion in otbn.sv which checks that state_err_o triggers an alert similar
  // to how it is checked that errors from prim blocks result in an alert. This unused signal is
  // connected / used if such an assertion is present, ensuring the assertion is not forgotten.
  logic unused_assert_connected;
  `ASSERT_INIT_NET(AssertConnected_A, unused_assert_connected === 1'b1 || !EnableAlertTriggerSVA)
`endif

endmodule
