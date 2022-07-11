// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Main Life Cycle Controller FSM.

`include "prim_assert.sv"

module lc_ctrl_fsm
  import lc_ctrl_pkg::*;
  import lc_ctrl_state_pkg::*;
#(// Random netlist constants
  parameter lc_keymgr_div_t RndCnstLcKeymgrDivInvalid    = LcKeymgrDivWidth'(0),
  parameter lc_keymgr_div_t RndCnstLcKeymgrDivTestDevRma = LcKeymgrDivWidth'(1),
  parameter lc_keymgr_div_t RndCnstLcKeymgrDivProduction = LcKeymgrDivWidth'(2),
  parameter lc_token_mux_t  RndCnstInvalidTokens         = {TokenMuxBits{1'b1}}
) (
  // This module is combinational, but we
  // need the clock and reset for the assertions.
  input                         clk_i,
  input                         rst_ni,
  // Initialization request from power manager.
  input                         init_req_i,
  output logic                  init_done_o,
  output logic                  idle_o,
  // Escalatio input
  input                         esc_scrap_state0_i,
  input                         esc_scrap_state1_i,
  // Life cycle state vector from OTP.
  input                         lc_state_valid_i,
  input  lc_state_e             lc_state_i,
  input  lc_cnt_e               lc_cnt_i,
  input  lc_tx_t                secrets_valid_i,
  // Defines whether we switch to an external clock when initiating a transition.
  input                         use_ext_clock_i,
  // Token input from OTP (these are all hash post-images).
  input  lc_token_t             test_unlock_token_i,
  input  lc_token_t             test_exit_token_i,
  input  lc_tx_t                test_tokens_valid_i,
  input  lc_token_t             rma_token_i,
  input  lc_tx_t                rma_token_valid_i,
  // Transition trigger interface.
  input                         trans_cmd_i,
  input  ext_dec_lc_state_t     trans_target_i,
  // Decoded life cycle state for CSRs.
  output ext_dec_lc_state_t     dec_lc_state_o,
  output dec_lc_cnt_t           dec_lc_cnt_o,
  output dec_lc_id_state_e      dec_lc_id_state_o,
  // Token hashing interface
  output logic                  token_hash_req_o,
  output logic                  token_hash_req_chk_o,
  input                         token_hash_ack_i,
  input                         token_hash_err_i,
  input                         token_if_fsm_err_i,
  input  lc_token_t             hashed_token_i,
  // OTP programming interface
  output logic                  otp_prog_req_o,
  output lc_state_e             otp_prog_lc_state_o,
  output lc_cnt_e               otp_prog_lc_cnt_o,
  input                         otp_prog_ack_i,
  input                         otp_prog_err_i,
  // Error outputs going to CSRs
  output logic                  trans_success_o,
  output logic                  trans_cnt_oflw_error_o,
  output logic                  trans_invalid_error_o,
  output logic                  token_invalid_error_o,
  output logic                  flash_rma_error_o,
  output logic                  otp_prog_error_o,
  output logic                  state_invalid_error_o,
  // Local life cycle signal
  output lc_tx_t                lc_raw_test_rma_o,
  // Life cycle broadcast outputs.
  output lc_tx_t                lc_dft_en_o,
  output lc_tx_t                lc_nvm_debug_en_o,
  output lc_tx_t                lc_hw_debug_en_o,
  output lc_tx_t                lc_cpu_en_o,
  output lc_tx_t                lc_creator_seed_sw_rw_en_o,
  output lc_tx_t                lc_owner_seed_sw_rw_en_o,
  output lc_tx_t                lc_iso_part_sw_rd_en_o,
  output lc_tx_t                lc_iso_part_sw_wr_en_o,
  output lc_tx_t                lc_seed_hw_rd_en_o,
  output lc_tx_t                lc_keymgr_en_o,
  output lc_tx_t                lc_escalate_en_o,
  output lc_tx_t                lc_check_byp_en_o,
  // Request and feedback to/from clock manager and AST.
  output lc_tx_t                lc_clk_byp_req_o,
  input  lc_tx_t                lc_clk_byp_ack_i,
  // Request and feedback to/from flash controller
  output lc_tx_t                lc_flash_rma_req_o,
  input  lc_tx_t                lc_flash_rma_ack_i,
  // State group diversification value for keymgr
  output lc_keymgr_div_t        lc_keymgr_div_o
);

  /////////////////////////////
  // Synchronizers / Buffers //
  /////////////////////////////

  // We use multiple copies of these signals in the
  // FSM checks below.
  lc_tx_t [2:0] lc_clk_byp_ack;
  lc_tx_t [1:0] lc_flash_rma_ack;

  prim_lc_sync #(
    .NumCopies(3)
  ) u_prim_lc_sync_clk_byp_ack (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_clk_byp_ack_i),
    .lc_en_o(lc_clk_byp_ack)
  );

  prim_lc_sync #(
    .NumCopies(2)
  ) u_prim_lc_sync_flash_rma_ack (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_flash_rma_ack_i),
    .lc_en_o(lc_flash_rma_ack)
  );

  ///////////////
  // FSM Logic //
  ///////////////
  fsm_state_e fsm_state_d, fsm_state_q;

  // Continuously feed in valid signal for LC state.
  logic lc_state_valid_d, lc_state_valid_q;
  assign lc_state_valid_d = lc_state_valid_i;

  // Encoded state vector.
  lc_state_e    lc_state_d, lc_state_q, next_lc_state;
  lc_cnt_e      lc_cnt_d, lc_cnt_q, next_lc_cnt;

  // Feed the next lc state reg back to the programming interface of OTP.
  assign otp_prog_lc_state_o = next_lc_state;
  assign otp_prog_lc_cnt_o   = next_lc_cnt;

  // Conditional LC signal outputs
  lc_tx_t lc_clk_byp_req, lc_flash_rma_req, lc_check_byp_en;

  `ASSERT_KNOWN(LcStateKnown_A,   lc_state_q   )
  `ASSERT_KNOWN(LcCntKnown_A,     lc_cnt_q     )
  `ASSERT_KNOWN(FsmStateKnown_A,  fsm_state_q  )

  // Hashed token to compare against.
  logic [1:0] hashed_token_valid_mux;
  lc_token_t hashed_token_mux;

  // Multibit state error from state decoder
  logic [5:0] state_invalid_error;

  // SEC_CM: MAIN.CTRL_FLOW.CONSISTENCY
  always_comb begin : p_fsm
    // FSM default state assignments.
    fsm_state_d   = fsm_state_q;
    lc_state_d    = lc_state_q;
    lc_cnt_d      = lc_cnt_q;

    // Token hashing.
    token_hash_req_o     = 1'b0;
    token_hash_req_chk_o = 1'b1;

    // OTP Interface
    otp_prog_req_o = 1'b0;

    // Defaults for status/error signals.
    token_invalid_error_o = 1'b0;
    otp_prog_error_o      = 1'b0;
    flash_rma_error_o     = 1'b0;
    trans_success_o       = 1'b0;
    state_invalid_error_o = 1'b0;

    // Status indication going to power manager.
    init_done_o = 1'b1;
    idle_o      = 1'b0;

    // These signals remain asserted once set to On.
    // Note that the remaining life cycle signals are decoded in
    // the lc_ctrl_signal_decode submodule.
    lc_clk_byp_req   = lc_clk_byp_req_o;
    lc_flash_rma_req = lc_flash_rma_req_o;
    lc_check_byp_en  = lc_check_byp_en_o;

    unique case (fsm_state_q)
      ///////////////////////////////////////////////////////////////////
      // Wait here until OTP has initialized and the
      // power manager sends an initialization request.
      ResetSt: begin
        init_done_o = 1'b0;
        lc_clk_byp_req   = Off;
        lc_flash_rma_req = Off;
        lc_check_byp_en  = Off;
        if (init_req_i && lc_state_valid_q) begin
          fsm_state_d = IdleSt;
          // Fetch LC state vector from OTP.
          lc_state_d  = lc_state_i;
          lc_cnt_d    = lc_cnt_i;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Idle state where life cycle control signals are broadcast.
      // Note that the life cycle signals are decoded and broadcast
      // in the lc_ctrl_signal_decode submodule.
      IdleSt: begin
        idle_o = 1'b1;
        // Continuously fetch LC state vector from OTP.
        // The state is locked in once a transition is started.
        lc_state_d    = lc_state_i;
        lc_cnt_d      = lc_cnt_i;
        // If the life cycle state is SCRAP, we move the FSM into a terminal
        // SCRAP state that does not allow any transitions to be initiated anymore.
        if (lc_state_q == LcStScrap) begin
          fsm_state_d = ScrapSt;
        // Initiate a transition. This will first increment the
        // life cycle counter before hashing and checking the token.
        end else if (trans_cmd_i) begin
          fsm_state_d = ClkMuxSt;
        end
        // If we are in a non-PROD life cycle state, steer the clock mux if requested. This
        // action is available in IdleSt so that the mux can be steered without having to initiate
        // a life cycle transition. If a transition is initiated however, the life cycle controller
        // will wait for the clock mux acknowledgement in the ClkMuxSt state before proceeding.
        if (lc_state_q inside {LcStRaw,
                               LcStTestLocked0,
                               LcStTestLocked1,
                               LcStTestLocked2,
                               LcStTestLocked3,
                               LcStTestLocked4,
                               LcStTestLocked5,
                               LcStTestLocked6,
                               LcStTestUnlocked0,
                               LcStTestUnlocked1,
                               LcStTestUnlocked2,
                               LcStTestUnlocked3,
                               LcStTestUnlocked4,
                               LcStTestUnlocked5,
                               LcStTestUnlocked6,
                               LcStTestUnlocked7,
                               LcStRma}) begin
          if (use_ext_clock_i) begin
            lc_clk_byp_req = On;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Clock mux state. If we are in RAW, TEST* or RMA, it is permissible
      // to switch to an external clock source. If the bypass request is
      // asserted, we have to wait until the clock mux and clock manager
      // have switched the mux and the clock divider. Also, we disable the
      // life cycle partition checks at this point since we are going to
      // alter the contents in the OTP memory array, which could lead to
      // spurious escalations.
      ClkMuxSt: begin
        lc_check_byp_en = On;
        if (lc_state_q inside {LcStRaw,
                               LcStTestLocked0,
                               LcStTestLocked1,
                               LcStTestLocked2,
                               LcStTestLocked3,
                               LcStTestLocked4,
                               LcStTestLocked5,
                               LcStTestLocked6,
                               LcStTestUnlocked0,
                               LcStTestUnlocked1,
                               LcStTestUnlocked2,
                               LcStTestUnlocked3,
                               LcStTestUnlocked4,
                               LcStTestUnlocked5,
                               LcStTestUnlocked6,
                               LcStTestUnlocked7,
                               LcStRma}) begin
          if (use_ext_clock_i) begin
            lc_clk_byp_req = On;
            if (lc_clk_byp_ack[0] == On) begin
              fsm_state_d = CntIncrSt;
            end
          end else begin
            fsm_state_d = CntIncrSt;
          end
        end else begin
          fsm_state_d = CntIncrSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // This increments the life cycle counter state.
      CntIncrSt: begin
        // If the counter has reached the maximum, bail out.
        if (trans_cnt_oflw_error_o) begin
          fsm_state_d = PostTransSt;
        end else begin
          fsm_state_d = CntProgSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // This programs the life cycle counter state.
      CntProgSt: begin
        otp_prog_req_o = 1'b1;

        // If the clock mux has been steered, double check that this is still the case.
        // Otherwise abort the transition operation.
        if (lc_clk_byp_req_o != lc_clk_byp_ack[1]) begin
            fsm_state_d = PostTransSt;
            otp_prog_error_o = 1'b1;
        end

        // Check return value and abort if there
        // was an error.
        if (otp_prog_ack_i) begin
          if (otp_prog_err_i) begin
            fsm_state_d = PostTransSt;
            otp_prog_error_o = 1'b1;
          end else begin
            fsm_state_d = TransCheckSt;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // First transition valid check. This will be repeated several
      // times below.
      TransCheckSt: begin
        if (trans_invalid_error_o) begin
          fsm_state_d = PostTransSt;
        end else begin
          fsm_state_d = TokenHashSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Hash and compare the token, no matter whether this transition
      // is conditional or not. Unconditional transitions just use a known
      // all-zero token value. That way, we always compare a hashed token
      // and guarantee that no other control flow path exists that could
      // bypass the token check.
      // SEC_CM: TOKEN.DIGEST
      TokenHashSt: begin
        token_hash_req_o = 1'b1;
        if (token_hash_ack_i) begin
          // This is the first comparison.
          // The token is compared two more times further below.
          // Also note that conditional transitions won't be possible if the
          // corresponding token is not valid. This only applies to tokens stored in
          // OTP. I.e., these tokens first have to be provisioned, before they can be used.
          if (hashed_token_i == hashed_token_mux &&
              !token_hash_err_i &&
              &hashed_token_valid_mux) begin
            fsm_state_d = FlashRmaSt;
          end else begin
            fsm_state_d = PostTransSt;
            token_invalid_error_o = 1'b1;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Flash RMA state. Note that we check the flash response again
      // two times later below.
      FlashRmaSt: begin
        if (trans_target_i == {DecLcStateNumRep{DecLcStRma}}) begin
          lc_flash_rma_req = On;
          if (lc_flash_rma_ack[0] == On) begin
            fsm_state_d = TokenCheck0St;
          end
        end else begin
          fsm_state_d = TokenCheck0St;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Check again two times whether this transition and the hashed
      // token are valid. Also check again whether the flash RMA
      // response is valid.
      // SEC_CM: TOKEN.DIGEST
      TokenCheck0St,
      TokenCheck1St: begin
        if (trans_invalid_error_o) begin
          fsm_state_d = PostTransSt;
        end else begin
          // If any of these RMA are conditions are true,
          // all of them must be true at the same time.
          if ((trans_target_i != {DecLcStateNumRep{DecLcStRma}} &&
               lc_flash_rma_req_o == Off && lc_flash_rma_ack[1] == Off) ||
              (trans_target_i == {DecLcStateNumRep{DecLcStRma}} &&
               lc_flash_rma_req_o == On && lc_flash_rma_ack[1] == On)) begin
            if (hashed_token_i == hashed_token_mux &&
                !token_hash_err_i &&
                &hashed_token_valid_mux) begin
              if (fsm_state_q == TokenCheck1St) begin
                // This is the only way we can get into the
                // programming state.
                fsm_state_d = TransProgSt;
              end else begin
                fsm_state_d = TokenCheck1St;
              end
            end else begin
              fsm_state_d = PostTransSt;
              token_invalid_error_o = 1'b1;
            end
          // The flash RMA process failed.
          end else begin
              fsm_state_d = PostTransSt;
              flash_rma_error_o = 1'b1;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Initiate OTP transaction. Note that the concurrent
      // LC state check is continuously checking whether the
      // new LC state remains valid. Once the ack returns we are
      // done with the transition and can go into the terminal PosTransSt.
      TransProgSt: begin
        otp_prog_req_o = 1'b1;

        // If the clock mux has been steered, double check that this is still the case.
        // Otherwise abort the transition operation.
        if (lc_clk_byp_req_o != lc_clk_byp_ack[2]) begin
          fsm_state_d = PostTransSt;
          otp_prog_error_o = 1'b1;
        // Also double check that the RMA signals remain stable.
        // Otherwise abort the transition operation.
        end else if ((trans_target_i != {DecLcStateNumRep{DecLcStRma}} &&
                      (lc_flash_rma_req_o != Off || lc_flash_rma_ack[1] != Off)) ||
                     (trans_target_i == {DecLcStateNumRep{DecLcStRma}} &&
                      (lc_flash_rma_req_o != On || lc_flash_rma_ack[1] != On))) begin
          fsm_state_d = PostTransSt;
          flash_rma_error_o = 1'b1;
        end else if (otp_prog_ack_i) begin
          fsm_state_d = PostTransSt;
          otp_prog_error_o = otp_prog_err_i;
          trans_success_o  = ~otp_prog_err_i;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Terminal states.
      ScrapSt,
      PostTransSt: ;


      EscalateSt: begin
        // During an escalation it is okay to de-assert token_hash_req without receivng ACK.
        token_hash_req_chk_o = 1'b0;
      end

      InvalidSt: begin
        // During an escalation it is okay to de-assert token_hash_req without receivng ACK.
        token_hash_req_chk_o = 1'b0;
        state_invalid_error_o = 1'b1;
      end
      ///////////////////////////////////////////////////////////////////
      // Go to terminal error state if we get here.
      default: begin
        fsm_state_d = InvalidSt;
        state_invalid_error_o = 1'b1;
      end
      ///////////////////////////////////////////////////////////////////
    endcase

    // SEC_CM: MAIN.FSM.GLOBAL_ESC
    if (esc_scrap_state0_i || esc_scrap_state1_i) begin
      fsm_state_d = EscalateSt;
    // SEC_CM: MAIN.FSM.LOCAL_ESC
    // If at any time the life cycle state encoding or any other FSM state within this module
    // is not valid, we jump into the terminal error state right away.
    // Note that state_invalid_error is a multibit error signal
    // with different error sources - need to reduce this to one bit here.
    end else if ((|state_invalid_error | token_if_fsm_err_i) && (fsm_state_q != EscalateSt)) begin
      fsm_state_d = InvalidSt;
      state_invalid_error_o = 1'b1;
    end
  end

  /////////////////
  // State Flops //
  /////////////////

  `PRIM_FLOP_SPARSE_FSM(u_fsm_state_regs, fsm_state_d, fsm_state_q, fsm_state_e, ResetSt)
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, lc_state_d, lc_state_q, lc_state_e, LcStScrap)
  `PRIM_FLOP_SPARSE_FSM(u_cnt_regs, lc_cnt_d, lc_cnt_q, lc_cnt_e, LcCnt24)

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      lc_state_valid_q <= 1'b0;
    end else begin
      lc_state_valid_q <= lc_state_valid_d;
    end
  end

  ///////////////
  // Token mux //
  ///////////////

  lc_ctrl_pkg::lc_tx_t [3:0] rma_token_valid;
  prim_lc_sync #(
    .NumCopies(4),
    .AsyncOn(0),
    .ResetValueIsOn(0)
  ) u_prim_lc_sync_rma_token_valid (
    .clk_i,
    .rst_ni,
    .lc_en_i(rma_token_valid_i),
    .lc_en_o(rma_token_valid)
  );

  lc_ctrl_pkg::lc_tx_t [7:0] test_tokens_valid;
  prim_lc_sync #(
    .NumCopies(8),
    .AsyncOn(0),
    .ResetValueIsOn(0)
  ) u_prim_lc_sync_test_token_valid (
    .clk_i,
    .rst_ni,
    .lc_en_i(test_tokens_valid_i),
    .lc_en_o(test_tokens_valid)
  );

  // SEC_CM: TOKEN_MUX.CTRL.REDUN
  // The token mux is split into two halves for which we use separate mux select signals
  // that have both been generated from separately buffered multibit lifecycle signals.
  logic [2**TokenIdxWidth-1:0][LcTokenWidth/2-1:0] hashed_tokens_lower, hashed_tokens_upper;
  // These helper signals are only there to increase readability of the mux code below.
  logic [LcTokenWidth/2-1:0] test_unlock_token_lower, test_unlock_token_upper;
  logic [LcTokenWidth/2-1:0] test_exit_token_lower, test_exit_token_upper;
  logic [LcTokenWidth/2-1:0] rma_token_lower, rma_token_upper;
  assign {test_unlock_token_lower, test_unlock_token_upper} = test_unlock_token_i;
  assign {test_exit_token_lower, test_exit_token_upper}     = test_exit_token_i;
  assign {rma_token_lower, rma_token_upper}                 = rma_token_i;

  // SEC_CM: TOKEN.DIGEST
  // This indexes the correct token, based on the transition arc.
  // Note that we always perform a token comparison, even in case of
  // unconditional transitions. In the case of unconditional tokens
  // we just pass an all-zero constant through the hashing function.
  always_comb begin : p_token_assign
    // Set the invalid token indices to a random netlist constant, rather than all-zero.
    {hashed_tokens_lower, hashed_tokens_upper} = RndCnstInvalidTokens;
    // All-zero token for unconditional transitions.
    {hashed_tokens_lower[ZeroTokenIdx],
     hashed_tokens_upper[ZeroTokenIdx]} = AllZeroTokenHashed;
    {hashed_tokens_lower[RawUnlockTokenIdx],
     hashed_tokens_upper[RawUnlockTokenIdx]} = RndCnstRawUnlockTokenHashed;
    // This mux has two separate halves, steered with separately buffered life cycle signals.
    if (test_tokens_valid[0] == On) begin
      hashed_tokens_lower[TestUnlockTokenIdx] = test_unlock_token_lower;
    end
    if (test_tokens_valid[1] == On) begin
      hashed_tokens_upper[TestUnlockTokenIdx] = test_unlock_token_upper;
    end
    // This mux has two separate halves, steered with separately buffered life cycle signals.
    if (test_tokens_valid[2] == On) begin
      hashed_tokens_lower[TestExitTokenIdx] = test_exit_token_lower;
    end
    if (test_tokens_valid[3] == On) begin
      hashed_tokens_upper[TestExitTokenIdx] = test_exit_token_upper;
    end
    // This mux has two separate halves, steered with separately buffered life cycle signals.
    if (rma_token_valid[0] == On) begin
      hashed_tokens_lower[RmaTokenIdx] = rma_token_lower;
    end
    if (rma_token_valid[1] == On) begin
      hashed_tokens_upper[RmaTokenIdx] = rma_token_upper;
    end
  end

  // SEC_CM: TOKEN_VALID.MUX.REDUN
  // The token valid mux is duplicated.
  logic [TokenIdxWidth-1:0] token_idx0, token_idx1;
  logic [2**TokenIdxWidth-1:0] hashed_tokens_valid0, hashed_tokens_valid1;
  always_comb begin : p_token_valid_assign
    // First mux
    hashed_tokens_valid0                     = '0;
    hashed_tokens_valid0[ZeroTokenIdx]       = 1'b1; // always valid
    hashed_tokens_valid0[RawUnlockTokenIdx]  = 1'b1; // always valid
    hashed_tokens_valid0[TestUnlockTokenIdx] = (test_tokens_valid[4] == On);
    hashed_tokens_valid0[TestExitTokenIdx]   = (test_tokens_valid[5] == On);
    hashed_tokens_valid0[RmaTokenIdx]        = (rma_token_valid[2] == On);
    hashed_tokens_valid0[InvalidTokenIdx]    = 1'b0; // always invalid
    // Second mux
    hashed_tokens_valid1                     = '0;
    hashed_tokens_valid1[ZeroTokenIdx]       = 1'b1; // always valid
    hashed_tokens_valid1[RawUnlockTokenIdx]  = 1'b1; // always valid
    hashed_tokens_valid1[TestUnlockTokenIdx] = (test_tokens_valid[6] == On);
    hashed_tokens_valid1[TestExitTokenIdx]   = (test_tokens_valid[7] == On);
    hashed_tokens_valid1[RmaTokenIdx]        = (rma_token_valid[3] == On);
    hashed_tokens_valid1[InvalidTokenIdx]    = 1'b0; // always invalid
  end

  // SEC_CM: STATE.CONFIG.SPARSE
  // The trans_target_i signal comes from the CSR and uses a replication encoding,
  // hence we can use different indices of the array.
  assign token_idx0 = (int'(dec_lc_state_o[0]) < NumLcStates &&
                       int'(trans_target_i[0]) < NumLcStates) ?
                      TransTokenIdxMatrix[dec_lc_state_o[0]][trans_target_i[0]] :
                      InvalidTokenIdx;
  assign token_idx1 = (int'(dec_lc_state_o[1]) < NumLcStates &&
                       int'(trans_target_i[1]) < NumLcStates) ?
                      TransTokenIdxMatrix[dec_lc_state_o[1]][trans_target_i[1]] :
                      InvalidTokenIdx;
  assign hashed_token_mux = {hashed_tokens_lower[token_idx0],
                             hashed_tokens_upper[token_idx1]};
  assign hashed_token_valid_mux = {hashed_tokens_valid0[token_idx0],
                                   hashed_tokens_valid1[token_idx1]};

  // If the indices are inconsistent, we also trigger a transition error.
  // We do not trigger an alert right away if this happens, since it could
  // be due to an invalid value programmed to the CSRs.
  logic trans_invalid_error;
  assign trans_invalid_error_o = trans_invalid_error || (token_idx0 != token_idx1);

  ////////////////////////////////////////////////////////////////////
  // Decoding and transition logic for redundantly encoded LC state //
  ////////////////////////////////////////////////////////////////////

  // This decodes the state into a format that can be exposed in the CSRs,
  // and flags any errors in the state encoding. Errors will move the
  // main FSM into INVALID right away.
  lc_ctrl_state_decode u_lc_ctrl_state_decode (
    .lc_state_valid_i      ( lc_state_valid_q  ),
    .lc_state_i            ( lc_state_q        ),
    .lc_cnt_i              ( lc_cnt_q          ),
    .secrets_valid_i,
    .fsm_state_i           ( fsm_state_q       ),
    .dec_lc_state_o,
    .dec_lc_id_state_o,
    .dec_lc_cnt_o,
    .state_invalid_error_o (state_invalid_error)
  );

  // LC transition checker logic and next state generation.
  lc_ctrl_state_transition u_lc_ctrl_state_transition (
    .lc_state_i            ( lc_state_q     ),
    .lc_cnt_i              ( lc_cnt_q       ),
    .dec_lc_state_i        ( dec_lc_state_o ),
    .fsm_state_i           ( fsm_state_q    ),
    .trans_target_i,
    .next_lc_state_o       ( next_lc_state  ),
    .next_lc_cnt_o         ( next_lc_cnt    ),
    .trans_cnt_oflw_error_o,
    .trans_invalid_error_o ( trans_invalid_error )
  );

  // LC signal decoder and broadcasting logic.
  lc_ctrl_signal_decode #(
    .RndCnstLcKeymgrDivInvalid    ( RndCnstLcKeymgrDivInvalid    ),
    .RndCnstLcKeymgrDivTestDevRma ( RndCnstLcKeymgrDivTestDevRma ),
    .RndCnstLcKeymgrDivProduction ( RndCnstLcKeymgrDivProduction )
  ) u_lc_ctrl_signal_decode (
    .clk_i,
    .rst_ni,
    .lc_state_valid_i   ( lc_state_valid_q ),
    .lc_state_i         ( lc_state_q       ),
    .secrets_valid_i,
    .fsm_state_i        ( fsm_state_q      ),
    .lc_raw_test_rma_o,
    .lc_dft_en_o,
    .lc_nvm_debug_en_o,
    .lc_hw_debug_en_o,
    .lc_cpu_en_o,
    .lc_creator_seed_sw_rw_en_o,
    .lc_owner_seed_sw_rw_en_o,
    .lc_iso_part_sw_rd_en_o,
    .lc_iso_part_sw_wr_en_o,
    .lc_seed_hw_rd_en_o,
    .lc_keymgr_en_o,
    .lc_escalate_en_o,
    .lc_keymgr_div_o
  );


  // Conditional signals set by main FSM.
  prim_lc_sender u_prim_lc_sender_clk_byp_req (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_clk_byp_req),
    .lc_en_o(lc_clk_byp_req_o)
  );
  prim_lc_sender u_prim_lc_sender_flash_rma_req (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_flash_rma_req),
    .lc_en_o(lc_flash_rma_req_o)
  );
  prim_lc_sender u_prim_lc_sender_check_byp_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_check_byp_en),
    .lc_en_o(lc_check_byp_en_o)
  );

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT(EscStaysOnOnceAsserted_A,
      lc_escalate_en_o == On
      |=>
      lc_escalate_en_o == On)

  `ASSERT(ClkBypStaysOnOnceAsserted_A,
      lc_clk_byp_req_o == On
      |=>
      lc_clk_byp_req_o == On)

  `ASSERT(FlashRmaStaysOnOnceAsserted_A,
      lc_flash_rma_req_o == On
      |=>
      lc_flash_rma_req_o == On)

  `ASSERT(NoClkBypInProdStates_A,
      lc_state_q inside {LcStProd, LcStProdEnd, LcStDev}
      |=>
      lc_clk_byp_req_o == Off)

  `ASSERT(SecCmCFITerminal0_A,
      fsm_state_q == PostTransSt
      |=>
      fsm_state_q inside {PostTransSt, InvalidSt, EscalateSt})

  `ASSERT(SecCmCFITerminal1_A,
      fsm_state_q == ScrapSt
      |=>
      fsm_state_q inside {ScrapSt, InvalidSt, EscalateSt})

  `ASSERT(SecCmCFITerminal2_A,
      fsm_state_q == EscalateSt
      |=>
      fsm_state_q == EscalateSt)

  `ASSERT(SecCmCFITerminal3_A,
      fsm_state_q == InvalidSt
      |=>
      fsm_state_q inside {InvalidSt, EscalateSt})

  // Check that the FSM is linear and does not contain any loops
  `ASSERT_FPV_LINEAR_FSM(SecCmCFILinear_A, fsm_state_q, fsm_state_e)

endmodule : lc_ctrl_fsm
