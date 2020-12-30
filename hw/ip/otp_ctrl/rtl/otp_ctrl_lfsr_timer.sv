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
// The EntropyWidth LSBs of the LFSR are periodically reseeded with fresh entropy from
// CSRNG every 2^ReseedLfsrWidth cycles.
//
// It is also possible to trigger one-off checks via integ_chk_trig_i and cnsty_chk_trig_i.
// This can be useful if SW chooses to leave the periodic checks disabled.
//

`include "prim_assert.sv"

module otp_ctrl_lfsr_timer
  import otp_ctrl_pkg::*;
  import otp_ctrl_reg_pkg::*;
#(
  // Entropy reseeding is triggered every time this counter expires.
  parameter int         ReseedLfsrWidth = 16,
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

  logic reseed_en;
  logic [ReseedLfsrWidth-1:0] reseed_timer_d, reseed_timer_q;

  assign reseed_timer_d = (reseed_timer_q > '0) ? reseed_timer_q - 1'b1   :
                          (reseed_en)           ? {ReseedLfsrWidth{1'b1}} : '0;
  assign edn_req_o = (reseed_timer_q == '0);
  assign reseed_en = edn_req_o & edn_ack_i;

  //////////
  // PRNG //
  //////////

  logic lfsr_en;
  logic [LfsrWidth-1:0] lfsr_state;

  prim_lfsr #(
    .LfsrDw      ( LfsrWidth      ),
    .EntropyDw   ( LfsrWidth      ),
    .StateOutDw  ( LfsrWidth      ),
    .DefaultSeed ( RndCnstLfsrSeed ),
    .StatePermEn ( 1'b1            ),
    .StatePerm   ( RndCnstLfsrPerm ),
    .ExtSeedSVA  ( 1'b0            ) // ext seed is unused
  ) i_prim_lfsr (
    .clk_i,
    .rst_ni,
    .seed_en_i  ( 1'b0       ),
    .seed_i     ( '0         ),
    .lfsr_en_i  ( lfsr_en | reseed_en                                ),
    .entropy_i  ( edn_data_i[LfsrWidth-1:0] & {LfsrWidth{reseed_en}} ),
    .state_o    ( lfsr_state )
  );

  // Not all entropy bits are used.
  logic unused_seed;
  assign unused_seed = ^edn_data_i;

  `ASSERT_INIT(EdnIsWideEnough_A, EdnDataWidth >= LfsrWidth)

  //////////////
  // Counters //
  //////////////

  logic [LfsrWidth-1:0] integ_cnt_d, integ_cnt_q;
  logic [LfsrWidth-1:0] cnsty_cnt_d, cnsty_cnt_q;
  logic [LfsrWidth-1:0] integ_mask, cnsty_mask;
  logic integ_load_period, integ_load_timeout, integ_cnt_zero;
  logic cnsty_load_period, cnsty_load_timeout, cnsty_cnt_zero;
  logic timeout_zero, integ_msk_zero, cnsty_msk_zero, cnsty_cnt_pause;

  assign integ_mask  = {integ_period_msk_i, {LfsrWidth-32{1'b1}}};
  assign cnsty_mask  = {cnsty_period_msk_i, {LfsrWidth-32{1'b1}}};

  assign integ_cnt_d = (integ_load_period)  ? lfsr_state & integ_mask :
                       (integ_load_timeout) ? LfsrWidth'(timeout_i)   :
                       (integ_cnt_zero)     ? '0                      :
                                              integ_cnt_q - 1'b1;


  assign cnsty_cnt_d = (cnsty_load_period)  ? lfsr_state & cnsty_mask :
                       (cnsty_load_timeout) ? LfsrWidth'(timeout_i)   :
                       (cnsty_cnt_zero)     ? '0                      :
                       (cnsty_cnt_pause)    ? cnsty_cnt_q             :
                                              cnsty_cnt_q - 1'b1;

  assign timeout_zero   = (timeout_i == '0);
  assign integ_msk_zero = (integ_period_msk_i == '0);
  assign cnsty_msk_zero = (cnsty_period_msk_i == '0);
  assign integ_cnt_zero = (integ_cnt_q == '0);
  assign cnsty_cnt_zero = (cnsty_cnt_q == '0);

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


  ////////////////////////////
  // Ping and Timeout Logic //
  ////////////////////////////

  // Encoding generated with ./sparse-fsm-encode.py -d 5 -m 5 -n 9 -s 628816752
  // Hamming distance histogram:
  //
  // 0: --
  // 1: --
  // 2: --
  // 3: --
  // 4: --
  // 5: |||||||||||||||||||| (60.00%)
  // 6: ||||||||||||| (40.00%)
  // 7: --
  // 8: --
  // 9: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 6
  //
  localparam int StateWidth = 9;
  typedef enum logic [StateWidth-1:0] {
    ResetSt     = 9'b011111011,
    IdleSt      = 9'b000100000,
    IntegWaitSt = 9'b110010101,
    CnstyWaitSt = 9'b001010110,
    ErrorSt     = 9'b100101111
  } state_e;

  state_e state_d, state_q;
  logic chk_timeout_d, chk_timeout_q;

  assign chk_timeout_o = chk_timeout_q;

  always_comb begin : p_fsm
    state_d = state_e'(state_q);

    // LFSR and counter signals
    lfsr_en = 1'b0;
    integ_load_period  = 1'b0;
    cnsty_load_period  = 1'b0;
    integ_load_timeout = 1'b0;
    cnsty_load_timeout = 1'b0;
    cnsty_cnt_pause    = 1'b0;

    // Requests going to partitions.
    set_all_integ_reqs = '0;
    set_all_cnsty_reqs = '0;

    // Status signals going to CSRs and error logic.
    chk_timeout_d = 1'b0;
    chk_pending_o = 1'b0;
    fsm_err_o = 1'b0;

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
        if ((!integ_msk_zero && integ_cnt_zero) || integ_chk_trig_i) begin
          state_d = IntegWaitSt;
          integ_load_timeout = 1'b1;
          set_all_integ_reqs = 1'b1;
        end else if ((!cnsty_msk_zero && cnsty_cnt_zero) || cnsty_chk_trig_i) begin
          state_d = CnstyWaitSt;
          cnsty_load_timeout = 1'b1;
          set_all_cnsty_reqs = 1'b1;
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
          integ_load_period = 1'b1;
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
          cnsty_load_period = 1'b1;
          lfsr_en = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Terminal error state. This raises an alert.
      ErrorSt: begin
        if (!chk_timeout_q) begin
          fsm_err_o = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // This should never happen, hence we directly jump into the
      // error state, where an alert will be triggered.
      default: begin
        state_d = ErrorSt;
      end
      ///////////////////////////////////////////////////////////////////
    endcase // state_q

    // Unconditionally jump into the terminal error state in case of escalation.
    if (escalate_en_i != lc_ctrl_pkg::Off) begin
      state_d = ErrorSt;
    end
  end

  ///////////////
  // Registers //
  ///////////////

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  logic [StateWidth-1:0] state_raw_q;
  assign state_q = state_e'(state_raw_q);
  prim_flop #(
    .Width(StateWidth),
    .ResetValue(StateWidth'(ResetSt))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .d_i ( state_d     ),
    .q_o ( state_raw_q )
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      integ_cnt_q <= '0;
      cnsty_cnt_q <= '0;
      integ_chk_req_q <= '0;
      cnsty_chk_req_q <= '0;
      chk_timeout_q   <= 1'b0;
      reseed_timer_q  <= {ReseedLfsrWidth{1'b1}};
    end else begin
      integ_cnt_q <= integ_cnt_d;
      cnsty_cnt_q <= cnsty_cnt_d;
      integ_chk_req_q <= integ_chk_req_d;
      cnsty_chk_req_q <= cnsty_chk_req_d;
      chk_timeout_q   <= chk_timeout_d;
      reseed_timer_q  <= reseed_timer_d;
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
