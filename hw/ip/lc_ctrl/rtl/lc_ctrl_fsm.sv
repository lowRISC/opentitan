// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Main Life Cycle Controller FSM.

module lc_ctrl_fsm
  import lc_ctrl_pkg::*;
(
  // This module is combinational, but we
  // need the clock and reset for the assertions.
  input                         clk_i,
  input                         rst_ni,
  // Initialization request from power manager.
  input                         init_req_i,
  output logic                  init_done_o,
  output logic                  idle_o,
  // Escalatio input
  input                         esc_scrap_state_i,
  input                         esc_wipe_secrets_i,
  // Life cycle state vector from OTP.
  input                         lc_state_valid_i,
  input  lc_state_e             lc_state_i,
  input  lc_id_state_e          lc_id_state_i,
  input  lc_cnt_e               lc_cnt_i,
  // Token input from OTP.
  input  lc_token_t             test_unlock_token_i,
  input  lc_token_t             test_exit_token_i,
  input  lc_token_t             rma_token_i,
  // Transition trigger interface.
  input                         trans_cmd_i,
  input  dec_lc_state_e         trans_target_i,
  // Decoded life cycle state for CSRs.
  output dec_lc_state_e         dec_lc_state_o,
  output dec_lc_cnt_t           dec_lc_cnt_o,
  output dec_lc_id_state_e      dec_lc_id_state_o,
  // Token hashing interface
  output logic                  token_hash_req_o,
  input                         token_hash_ack_i,
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
  // Life cycle broadcast outputs.
  output lc_tx_t                lc_dft_en_o,
  output lc_tx_t                lc_nvm_debug_en_o,
  output lc_tx_t                lc_hw_debug_en_o,
  output lc_tx_t                lc_cpu_en_o,
  output lc_tx_t                lc_provision_wr_en_o,
  output lc_tx_t                lc_provision_rd_en_o,
  output lc_tx_t                lc_keymgr_en_o,
  output lc_tx_t                lc_escalate_en_o,
    // Request and feedback to/from clock manager and AST.
  output lc_tx_t                lc_clk_byp_req_o,
  input  lc_tx_t                lc_clk_byp_ack_i,
  // Request and feedback to/from flash controller
  output lc_tx_t                lc_flash_rma_req_o,
  input  lc_tx_t                lc_flash_rma_ack_i
);

  ///////////////
  // FSM Logic //
  ///////////////
  fsm_state_e fsm_state_d, fsm_state_q;

  // Continously feed in valid signal for LC state.
  logic lc_state_valid_d, lc_state_valid_q;
  assign lc_state_valid_d = lc_state_valid_i;

  // Encoded state vector.
  lc_state_e    lc_state_d, lc_state_q, next_lc_state;
  lc_cnt_e      lc_cnt_d, lc_cnt_q, next_lc_cnt;
  lc_id_state_e lc_id_state_d, lc_id_state_q;

  // Working register for hashed token.
  lc_token_t hashed_token_d, hashed_token_q;

  // Feed the lc state reg back to the programming interface of OTP.
  assign otp_prog_lc_state_o = lc_state_q;
  assign otp_prog_lc_cnt_o   = lc_cnt_q;

  // Conditional LC signal outputs
  lc_tx_t lc_clk_byp_req_d, lc_clk_byp_req_q;
  lc_tx_t lc_flash_rma_req_d, lc_flash_rma_req_q;

  `ASSERT_KNOWN(LcStateKnown_A,   lc_state_q   )
  `ASSERT_KNOWN(LcCntKnown_A,     lc_cnt_q     )
  `ASSERT_KNOWN(LcIdStateKnown_A, lc_id_state_q)
  `ASSERT_KNOWN(FsmStateKnown_A,  fsm_state_q  )

  // Hashed token to compare against.
  logic [LcTokenWidth-1:0] hashed_token_mux;

  always_comb begin : p_fsm
    // FSM default state assignments.
    fsm_state_d   = fsm_state_q;
    lc_state_d    = lc_state_q;
    lc_cnt_d      = lc_cnt_q;
    lc_id_state_d = lc_id_state_q;

    // Token hashing.
    token_hash_req_o = 1'b0;
    hashed_token_d   = hashed_token_q;

    // OTP Interface
    otp_prog_req_o = 1'b0;

    // Defaults for status/error signals.
    token_invalid_error_o = 1'b0;
    otp_prog_error_o      = 1'b0;
    flash_rma_error_o     = 1'b0;
    trans_success_o       = 1'b0;

    // Status indication going to power manager.
    init_done_o = 1'b1;
    idle_o      = 1'b1;

    // The clock bypass and RMA signals remain asserted once set to ON.
    // Note that the remaining life cycle signals are decoded in
    // the lc_ctrl_signal_decode submodule.
    lc_clk_byp_req_d   = lc_clk_byp_req_q;
    lc_flash_rma_req_d = lc_flash_rma_req_q;

    unique case (fsm_state_q)
      ///////////////////////////////////////////////////////////////////
      // Wait here until OTP has initialized and the
      // power manager sends an initialization request.
      ResetSt: begin
        init_done_o = 1'b0;
        if (init_req_i && lc_state_valid_q) begin
          fsm_state_d = IdleSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Idle state where life cycle control signals are broadcast.
      // Note that the life cycle signals are decoded and broadcast
      // in the lc_ctrl_signal_decode submodule.
      IdleSt: begin
        idle_o = 1'b1;
        // Continuously fetch LC state from OTP.
        lc_state_d    = lc_state_i;
        lc_cnt_d      = lc_cnt_i;
        lc_id_state_d = lc_id_state_i;

        // Initiate a transition. This will first increment the
        // life cycle counter before hashing and checking the token.
        if (trans_cmd_i) begin
          fsm_state_d = ClkMuxSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Clock mux state. If in RAW or TEST_LOCKED the bypass request is
      // asserted and we have to wait until the clock mux and clock manager
      // have switched the mux and the clock divider.
      ClkMuxSt: begin
        if (lc_state_q inside {LcStRaw,
                               LcStTestLocked0,
                               LcStTestLocked1,
                               LcStTestLocked2}) begin
          lc_clk_byp_req_d = On;
          if (lc_clk_byp_ack_i == On) begin
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
          lc_cnt_d = next_lc_cnt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // This programs the life cycle counter state.
      CntProgSt: begin
        otp_prog_req_o = 1'b1;
        // Check return value and
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
      TokenHashSt: begin
        token_hash_req_o = 1'b1;
        if (token_hash_ack_i) begin
          // This is the first comparison.
          // The token is registered and then
          // compared two more times further below.
          hashed_token_d = hashed_token_i;
          if (hashed_token_i == hashed_token_mux) begin
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
        if (trans_target_i == DecLcStRma) begin
          lc_flash_rma_req_d = On;
          if (lc_flash_rma_ack_i == On) begin
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
      TokenCheck0St,
      TokenCheck1St: begin
        if (trans_invalid_error_o) begin
          fsm_state_d = PostTransSt;
        end else begin
          // If any of these RMA are conditions are true,
          // all of them must be true at the same time.
          if ((trans_target_i != DecLcStRma &&
               lc_flash_rma_req_q == Off    &&
               lc_flash_rma_ack_i == Off)   ||
              (trans_target_i == DecLcStRma &&
               lc_flash_rma_req_q == On     &&
               lc_flash_rma_ack_i == On)) begin
            if (hashed_token_i == hashed_token_mux) begin
              if (fsm_state_q == TokenCheck1St) begin
                // This is the only way we can get into the
                // programming state.
                fsm_state_d = TransProgSt;
                lc_state_d = next_lc_state;
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
        if (otp_prog_ack_i) begin
          fsm_state_d = PostTransSt;
          otp_prog_error_o = otp_prog_err_i;
          trans_success_o  = ~otp_prog_err_i;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Terminal error states.
      PostTransSt,
      EscalateSt,
      InvalidSt: ;
      ///////////////////////////////////////////////////////////////////
      // Go to terminal error state if we get here.
      default: fsm_state_d = InvalidSt;
      ///////////////////////////////////////////////////////////////////
    endcase

    // If at any time the life cycle state encoding is not valid,
    // we jump into the terminal error state right away.
    if (state_invalid_error_o) begin
      fsm_state_d = InvalidSt;
    end else if (esc_scrap_state_i) begin
      fsm_state_d = EscalateSt;
    end
  end

  /////////////////
  // State Flops //
  /////////////////

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  logic [FsmStateWidth-1:0] fsm_state_raw_q;
  assign fsm_state_q = fsm_state_e'(fsm_state_raw_q);
  prim_flop #(
    .Width(FsmStateWidth),
    .ResetValue(FsmStateWidth'(ResetSt))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .d_i ( fsm_state_d ),
    .q_o ( fsm_state_raw_q )
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      lc_state_q         <= LcStScrap;
      lc_cnt_q           <= LcCnt16;
      lc_id_state_q      <= LcIdPersonalized;
      lc_state_valid_q   <= 1'b0;
      hashed_token_q     <= {LcTokenWidth{1'b1}};
      lc_clk_byp_req_q   <= Off;
      lc_flash_rma_req_q <= Off;
    end else begin
      lc_state_q         <= lc_state_d;
      lc_cnt_q           <= lc_cnt_d;
      lc_id_state_q      <= lc_id_state_d;
      lc_state_valid_q   <= lc_state_valid_d;
      hashed_token_q     <= hashed_token_d;
      lc_clk_byp_req_q   <= lc_clk_byp_req_d;
      lc_flash_rma_req_q <= lc_flash_rma_req_d;
    end
  end

  ///////////////
  // Token mux //
  ///////////////

  // This indexes the correct token, based on the transition arc.
  // Note that we always perform a token comparison, even in case of
  // unconditional transitions. In the case of unconditional tokens
  // we just pass an all-zero constant through the hashing function.
  logic [2**TokenIdxWidth-1:0][LcTokenWidth-1:0] hashed_tokens;
  logic [TokenIdxWidth-1:0] token_idx;
  always_comb begin : p_token_assign
    hashed_tokens = '0;
    hashed_tokens[ZeroTokenIdx]       = AllZeroTokenHashed;
    hashed_tokens[RawUnlockTokenIdx]  = RawUnlockTokenHashed;
    hashed_tokens[TestUnlockTokenIdx] = test_unlock_token_i;
    hashed_tokens[TestExitTokenIdx]   = test_exit_token_i;
    hashed_tokens[RmaTokenIdx]        = rma_token_i;
    hashed_tokens[InvalidTokenIdx]    = '0;
  end

  assign token_idx = TransTokenIdxMatrix[dec_lc_state_o][trans_target_i];
  assign hashed_token_mux = hashed_tokens[token_idx];

  ////////////////////////////////////////////////////////////////////
  // Decoding and transition logic for redundantly encoded LC state //
  ////////////////////////////////////////////////////////////////////

  // This decodes the state into a format that can be exposed in the CSRs,
  // and flags any errors in the state encoding. Errors will move the
  // main FSM into INVALID right away.
  lc_ctrl_state_decode u_lc_ctrl_state_decode (
    .lc_state_valid_i  ( lc_state_valid_q ),
    .lc_state_i        ( lc_state_q       ),
    .lc_id_state_i     ( lc_id_state_q    ),
    .lc_cnt_i          ( lc_cnt_q         ),
    .fsm_state_i       ( fsm_state_q      ),
    .dec_lc_state_o,
    .dec_lc_id_state_o,
    .dec_lc_cnt_o,
    .state_invalid_error_o
  );

  // LC transition checker logic and next state generation.
  lc_ctrl_state_transition u_lc_ctrl_state_transition (
    .lc_state_i            ( lc_state_q     ),
    .lc_cnt_i              ( lc_cnt_q       ),
    .dec_lc_state_i        ( dec_lc_state_o ),
    .trans_target_i,
    .next_lc_state_o       ( next_lc_state  ),
    .next_lc_cnt_o         ( next_lc_cnt    ),
    .trans_cnt_oflw_error_o,
    .trans_invalid_error_o
  );

  // LC signal decoder and broadcasting logic.
  lc_ctrl_signal_decode u_lc_ctrl_signal_decode (
    .clk_i,
    .rst_ni,
    .lc_state_valid_i   ( lc_state_valid_q ),
    .lc_state_i         ( lc_state_q       ),
    .lc_id_state_i      ( lc_id_state_q    ),
    .fsm_state_i        ( fsm_state_q      ),
    .esc_wipe_secrets_i,
    .lc_dft_en_o,
    .lc_nvm_debug_en_o,
    .lc_hw_debug_en_o,
    .lc_cpu_en_o,
    .lc_provision_wr_en_o,
    .lc_provision_rd_en_o,
    .lc_keymgr_en_o,
    .lc_escalate_en_o
  );

  // Conditional signals set by main FSM.
  assign lc_clk_byp_req_o   = lc_clk_byp_req_q;
  assign lc_flash_rma_req_o = lc_flash_rma_req_q;

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT(ClkBypStaysOnOnceAsserted_A,
      lc_escalate_en_q == On
      |=>
      lc_escalate_en_q == On)

  `ASSERT(FlashRmaStaysOnOnceAsserted_A,
      lc_flash_rma_req_o == On
      |=>
      lc_flash_rma_req_o == On)

endmodule : lc_ctrl_fsm
