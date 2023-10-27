// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module implements the LFSR timer for triggering periodic consistency and integrity checks in
// OTP. In particular, this module contains two 40bit counters (one for the consistency and one
// for the integrity checks) and a 40bit LFSR to draw pseudo random wait counts.
//
// The integ_period_msk_i and cnsty_period_msk_i mask signals are used to mask off the LFSR outputs
// and hence determine the maximum wait count that can be drawn. If these values are set to
// zero, the corresponding timer is disabled.
//
// Once a particular check timer has expired, the module will send out a check request to all
// partitions and wait for an acknowledgment. If a particular partition encounters an integrity or
// consistency mismatch, this will be directly reported via the error and alert logic.
//
// In order to guard against wedged partition controllers or arbitration lock ups due to tampering
// attempts, this check timer module also supports a 32bit timeout that can optionally be
// programmed. If a particular check times out, chk_timeout_o will be asserted, which will raise
// an alert via the error logic.
//
// The EntropyWidth LSBs of the LFSR are reseeded with fresh entropy from EDN once
// LfsrUsageThreshold values have been drawn from the LFSR.
//
// It is also possible to trigger one-off checks via integ_chk_trig_i and cnsty_chk_trig_i.
// This can be useful if SW chooses to leave the periodic checks disabled.
//

`include "prim_flop_macros.sv"

module otp_ctrl_lfsr_timer
  import otp_ctrl_pkg::*;
  import otp_ctrl_reg_pkg::*;
#(
  // Compile time random constants, to be overriden by topgen.
  parameter lfsr_seed_t RndCnstLfsrSeed = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t RndCnstLfsrPerm = RndCnstLfsrPermDefault
) (
  input                            clk_i,
  input                            rst_ni,
  output logic                     edn_req_o,          // request to EDN
  input                            edn_ack_i,          // ack from EDN
  input        [EdnDataWidth-1:0]  edn_data_i,         // from EDN
  input                            timer_en_i,         // enable timer
  input                            otp_prog_busy_i,    // indicates whether prog ops are in progress
  input                            integ_chk_trig_i,   // one-off trigger for integrity check
  input                            cnsty_chk_trig_i,   // one-off trigger for consistency check
  output logic                     chk_pending_o,      // indicates whether there are pending checks
  input        [31:0]              timeout_i,          // check timeout
  input        [31:0]              integ_period_msk_i, // maximum integrity check mask
  input        [31:0]              cnsty_period_msk_i, // maximum consistency check mask
  output logic [NumPart-1:0]       integ_chk_req_o,    // request to all partitions
  output logic [NumPart-1:0]       cnsty_chk_req_o,    // request to all partitions
  input        [NumPart-1:0]       integ_chk_ack_i,    // response from partitions
  input        [NumPart-1:0]       cnsty_chk_ack_i,    // response from partitions
  input  lc_ctrl_pkg::lc_tx_t      escalate_en_i,      // escalation input, moves FSM into ErrorSt
  output logic                     chk_timeout_o,      // a check has timed out
  output logic                     fsm_err_o           // the FSM has reached an invalid state
);

  ////////////////////
  // Reseed counter //
  ////////////////////

  // Count how many times the LFSR has been used to generate a value.
  // Once we've reached the limit, we request new entropy from EDN to reseed
  // the LFSR. Note that this is not a blocking operation for the timer below.
  // I.e., the timer is allowed to continue its operation, and may draw more
  // values, even if the EDN reseed request is still in progress.
  logic reseed_en, lfsr_en;
  logic [$clog2(LfsrUsageThreshold+1)-1:0] reseed_cnt_d, reseed_cnt_q;
  assign reseed_cnt_d = (reseed_en) ? '0                  :
                        (edn_req_o) ? reseed_cnt_q        :
                        (lfsr_en)   ? reseed_cnt_q + 1'b1 :
                                      reseed_cnt_q;

  assign edn_req_o = (reseed_cnt_q >= LfsrUsageThreshold);
  assign reseed_en = edn_req_o & edn_ack_i;

  ///////////////////////////
  // Tandem LFSR Instances //
  ///////////////////////////

  logic lfsr_err;
  logic [LfsrWidth-1:0] entropy;
  logic [LfsrWidth-1:0] lfsr_state;
  assign entropy = (reseed_en) ? edn_data_i[LfsrWidth-1:0] : '0;

  // We employ two redundant LFSRs to guard against FI attacks.
  // If any of the two is glitched and the two LFSR states do not agree,
  // the FSM below is moved into a terminal error state.
  // SEC_CM: TIMER.LFSR.REDUN
  prim_double_lfsr #(
    .LfsrDw      ( LfsrWidth      ),
    .EntropyDw   ( LfsrWidth      ),
    .StateOutDw  ( LfsrWidth      ),
    .DefaultSeed ( RndCnstLfsrSeed ),
    .StatePermEn ( 1'b1            ),
    .StatePerm   ( RndCnstLfsrPerm ),
    .ExtSeedSVA  ( 1'b0            )
  ) u_prim_double_lfsr (
    .clk_i,
    .rst_ni,
    .seed_en_i  ( 1'b0                 ),
    .seed_i     ( '0                   ),
    .lfsr_en_i  ( reseed_en || lfsr_en ),
    .entropy_i  ( entropy              ),
    .state_o    ( lfsr_state           ),
    .err_o      ( lfsr_err             )
  );

  // Not all entropy bits are used.
  logic unused_seed;
  assign unused_seed = ^edn_data_i;

  `ASSERT_INIT(EdnIsWideEnough_A, EdnDataWidth >= LfsrWidth)

  //////////////////////////////
  // Tandem Counter Instances //
  //////////////////////////////

  // We employ redundant counters to guard against FI attacks.
  // If any of them is glitched and the redundant counter states do not agree,
  // the FSM below is moved into a terminal error state.
  logic [LfsrWidth-1:0] integ_cnt, cnsty_cnt, integ_cnt_set_val, cnsty_cnt_set_val;
  logic [LfsrWidth-1:0] integ_mask, cnsty_mask;
  logic integ_set_period, integ_set_timeout, integ_cnt_zero;
  logic cnsty_set_period, cnsty_set_timeout, cnsty_cnt_zero;
  logic integ_cnt_set, cnsty_cnt_set, integ_cnt_err, cnsty_cnt_err;
  logic timeout_zero, integ_msk_zero, cnsty_msk_zero, cnsty_cnt_pause;

  assign timeout_zero   = (timeout_i == '0);
  assign integ_msk_zero = (integ_period_msk_i == '0);
  assign cnsty_msk_zero = (cnsty_period_msk_i == '0);
  assign integ_cnt_zero = (integ_cnt == '0);
  assign cnsty_cnt_zero = (cnsty_cnt == '0);

  assign integ_cnt_set = integ_set_period || integ_set_timeout;
  assign cnsty_cnt_set = cnsty_set_period || cnsty_set_timeout;

  assign integ_mask  = {integ_period_msk_i, {LfsrWidth-32{1'b1}}};
  assign cnsty_mask  = {cnsty_period_msk_i, {LfsrWidth-32{1'b1}}};
  assign integ_cnt_set_val = (integ_set_period) ? (lfsr_state & integ_mask) : LfsrWidth'(timeout_i);
  assign cnsty_cnt_set_val = (cnsty_set_period) ? (lfsr_state & cnsty_mask) : LfsrWidth'(timeout_i);

  // SEC_CM: TIMER_INTEG.CTR.REDUN
  prim_count #(
    .Width(LfsrWidth)
  ) u_prim_count_integ (
    .clk_i,
    .rst_ni,
    .clr_i(1'b0),
    .set_i(integ_cnt_set),
    .set_cnt_i(integ_cnt_set_val),
    .incr_en_i(1'b0),
    .decr_en_i(!integ_cnt_zero),
    .step_i(LfsrWidth'(1)),
    .cnt_o(integ_cnt),
    .cnt_next_o(),
    .err_o(integ_cnt_err)
  );

  // SEC_CM: TIMER_CNSTY.CTR.REDUN
  prim_count #(
    .Width(LfsrWidth)
  ) u_prim_count_cnsty (
    .clk_i,
    .rst_ni,
    .clr_i(1'b0),
    .set_i(cnsty_cnt_set),
    .set_cnt_i(cnsty_cnt_set_val),
    .incr_en_i(1'b0),
    .decr_en_i(!cnsty_cnt_zero && !cnsty_cnt_pause),
    .step_i(LfsrWidth'(1)),
    .cnt_o(cnsty_cnt),
    .cnt_next_o(),
    .err_o(cnsty_cnt_err)
  );

  /////////////////////
  // Request signals //
  /////////////////////

  logic set_all_integ_reqs, set_all_cnsty_reqs;
  logic [NumPart-1:0] integ_chk_req_d, integ_chk_req_q;
  logic [NumPart-1:0] cnsty_chk_req_d, cnsty_chk_req_q;
  assign integ_chk_req_o = integ_chk_req_q;
  assign cnsty_chk_req_o = cnsty_chk_req_q;
  assign integ_chk_req_d = (set_all_integ_reqs) ? {NumPart{1'b1}} :
                                                  integ_chk_req_q & ~integ_chk_ack_i;
  assign cnsty_chk_req_d = (set_all_cnsty_reqs) ? {NumPart{1'b1}} :
                                                  cnsty_chk_req_q & ~cnsty_chk_ack_i;


  // external triggers
  logic clr_integ_chk_trig, clr_cnsty_chk_trig;
  logic integ_chk_trig_d, integ_chk_trig_q;
  logic cnsty_chk_trig_d, cnsty_chk_trig_q;
  assign integ_chk_trig_d = (integ_chk_trig_q & ~clr_integ_chk_trig) | integ_chk_trig_i;
  assign cnsty_chk_trig_d = (cnsty_chk_trig_q & ~clr_cnsty_chk_trig) | cnsty_chk_trig_i;

  ////////////////////////////
  // Ping and Timeout Logic //
  ////////////////////////////

  // SEC_CM: TIMER.FSM.SPARSE
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 5 -n 9 \
  //      -s 628816752 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (60.00%)
  //  6: ||||||||||||| (40.00%)
  //  7: --
  //  8: --
  //  9: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 6
  // Minimum Hamming weight: 4
  // Maximum Hamming weight: 6
  //
  localparam int StateWidth = 9;
  typedef enum logic [StateWidth-1:0] {
    ResetSt     = 9'b100100101,
    IdleSt      = 9'b001101110,
    IntegWaitSt = 9'b010110011,
    CnstyWaitSt = 9'b111010110,
    ErrorSt     = 9'b001011001
  } state_e;

  state_e state_d, state_q;
  logic chk_timeout_d, chk_timeout_q;

  assign chk_timeout_o = chk_timeout_q;

  always_comb begin : p_fsm
    state_d = state_q;

    // LFSR and counter signals
    lfsr_en = 1'b0;
    integ_set_period  = 1'b0;
    cnsty_set_period  = 1'b0;
    integ_set_timeout = 1'b0;
    cnsty_set_timeout = 1'b0;
    cnsty_cnt_pause    = 1'b0;

    // Requests going to partitions.
    set_all_integ_reqs = '0;
    set_all_cnsty_reqs = '0;

    // Status signals going to CSRs and error logic.
    chk_timeout_d = chk_timeout_q;
    chk_pending_o = cnsty_chk_trig_q || integ_chk_trig_q;
    fsm_err_o = 1'b0;

    // Clear signals for external triggers
    clr_integ_chk_trig = 1'b0;
    clr_cnsty_chk_trig = 1'b0;

    unique case (state_q)
      ///////////////////////////////////////////////////////////////////
      // Wait until enabled. We never return to this state
      // once enabled!
      ResetSt: begin
        if (timer_en_i) begin
          state_d = IdleSt;
          lfsr_en = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait here until one of the two timers expires (if enabled) or if
      // a check is triggered externally.
      IdleSt: begin
        if ((!integ_msk_zero && integ_cnt_zero) || integ_chk_trig_q) begin
          state_d = IntegWaitSt;
          integ_set_timeout = 1'b1;
          set_all_integ_reqs = 1'b1;
          clr_integ_chk_trig = integ_chk_trig_q;
        end else if ((!cnsty_msk_zero && cnsty_cnt_zero) || cnsty_chk_trig_q) begin
          state_d = CnstyWaitSt;
          cnsty_set_timeout = 1'b1;
          set_all_cnsty_reqs = 1'b1;
          clr_cnsty_chk_trig = cnsty_chk_trig_q;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for all the partitions to respond and go back to idle.
      // If the timeout is enabled, bail out into terminal error state
      // if the timeout counter expires (this will raise an alert).
      IntegWaitSt: begin
        chk_pending_o = 1'b1;
        if (!timeout_zero && integ_cnt_zero) begin
          state_d = ErrorSt;
          chk_timeout_d = 1'b1;
        end else if (integ_chk_req_q == '0) begin
          state_d = IdleSt;
          // This draws the next wait period.
          integ_set_period = 1'b1;
          lfsr_en = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for all the partitions to respond and go back to idle.
      // If the timeout is enabled, bail out into terminal error state
      // if the timeout counter expires (this will raise an alert).
      CnstyWaitSt: begin
        chk_pending_o = 1'b1;
        // Note that consistency checks go back and read from OTP. Hence,
        // life cycle transitions and DAI programming operations
        // may interfere with these checks and cause them to take longer
        // than typically expected. Therefore, the timeout counter is stopped
        // during programming operations.
        cnsty_cnt_pause = otp_prog_busy_i;
        if (!timeout_zero && cnsty_cnt_zero) begin
          state_d = ErrorSt;
          chk_timeout_d = 1'b1;
        end else if (cnsty_chk_req_q == '0) begin
          state_d = IdleSt;
          // This draws the next wait period.
          cnsty_set_period = 1'b1;
          lfsr_en = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Terminal error state. This raises an alert.
      ErrorSt: begin
        // Continuously clear pending checks.
        clr_integ_chk_trig = 1'b1;
        clr_cnsty_chk_trig = 1'b1;
        if (!chk_timeout_q) begin
          fsm_err_o = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // This should never happen, hence we directly jump into the
      // error state, where an alert will be triggered.
      default: begin
        state_d = ErrorSt;
        fsm_err_o = 1'b1;
      end
      ///////////////////////////////////////////////////////////////////
    endcase // state_q

    // Unconditionally jump into the terminal error state in case of escalation,
    // or if the two LFSR or counter states do not agree.
    // SEC_CM: TIMER.FSM.LOCAL_ESC, TIMER.FSM.GLOBAL_ESC
    if (lfsr_err || integ_cnt_err || cnsty_cnt_err || escalate_en_i != lc_ctrl_pkg::Off) begin
       state_d = ErrorSt;
       fsm_err_o = 1'b1;
    end
  end

  ///////////////
  // Registers //
  ///////////////

  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, ResetSt)

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      integ_chk_req_q  <= '0;
      cnsty_chk_req_q  <= '0;
      chk_timeout_q    <= 1'b0;
      reseed_cnt_q     <= '0;
      integ_chk_trig_q <= 1'b0;
      cnsty_chk_trig_q <= 1'b0;
    end else begin
      integ_chk_req_q  <= integ_chk_req_d;
      cnsty_chk_req_q  <= cnsty_chk_req_d;
      chk_timeout_q    <= chk_timeout_d;
      reseed_cnt_q     <= reseed_cnt_d;
      integ_chk_trig_q <= integ_chk_trig_d;
      cnsty_chk_trig_q <= cnsty_chk_trig_d;
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_KNOWN(EdnReqKnown_A,      edn_req_o)
  `ASSERT_KNOWN(ChkPendingKnown_A,  chk_pending_o)
  `ASSERT_KNOWN(IntegChkReqKnown_A, integ_chk_req_o)
  `ASSERT_KNOWN(CnstyChkReqKnown_A, cnsty_chk_req_o)
  `ASSERT_KNOWN(ChkTimeoutKnown_A,  chk_timeout_o)

endmodule : otp_ctrl_lfsr_timer
