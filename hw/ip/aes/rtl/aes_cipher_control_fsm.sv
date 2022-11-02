// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES cipher core control FSM
//
// This module contains the AES cipher core control FSM.

`include "prim_assert.sv"

module aes_cipher_control_fsm import aes_pkg::*;
#(
  parameter bit         SecMasking  = 0,
  parameter sbox_impl_e SecSBoxImpl = SBoxImplDom
) (
  input  logic             clk_i,
  input  logic             rst_ni,

  // Input handshake signals
  input  logic             in_valid_i,           // Sparsify using multi-rail.
  output logic             in_ready_o,           // Sparsify using multi-rail.

  // Output handshake signals
  output logic             out_valid_o,          // Sparsify using multi-rail.
  input  logic             out_ready_i,          // Sparsify using multi-rail.

  // Control and sync signals
  input  logic             cfg_valid_i,          // Used for SVAs only.
  input  ciph_op_e         op_i,
  input  key_len_e         key_len_i,
  input  logic             crypt_i,              // Sparsify using multi-rail.
  input  logic             dec_key_gen_i,        // Sparsify using multi-rail.
  input  logic             prng_reseed_i,
  input  logic             key_clear_i,
  input  logic             data_out_clear_i,
  input  logic             mux_sel_err_i,
  input  logic             sp_enc_err_i,
  input  logic             rnd_ctr_err_i,
  input  logic             op_err_i,
  input  logic             alert_fatal_i,
  output logic             alert_o,

  // Control signals for masking PRNG
  output logic             prng_update_o,
  output logic             prng_reseed_req_o,
  input  logic             prng_reseed_ack_i,

  // Control and sync signals for cipher data path
  output state_sel_e       state_sel_o,
  output logic             state_we_o,           // Sparsify using multi-rail.
  output logic             sub_bytes_en_o,       // Sparsify using multi-rail.
  input  logic             sub_bytes_out_req_i,  // Sparsify using multi-rail.
  output logic             sub_bytes_out_ack_o,  // Sparsify using multi-rail.
  output add_rk_sel_e      add_rk_sel_o,

  // Control and sync signals for key expand data path
  output key_full_sel_e    key_full_sel_o,
  output logic             key_full_we_o,        // Sparsify using multi-rail.
  output key_dec_sel_e     key_dec_sel_o,
  output logic             key_dec_we_o,         // Sparsify using multi-rail.
  output logic             key_expand_en_o,      // Sparsify using multi-rail.
  input  logic             key_expand_out_req_i, // Sparsify using multi-rail.
  output logic             key_expand_out_ack_o, // Sparsify using multi-rail.
  output logic             key_expand_clear_o,
  output logic [3:0]       rnd_ctr_o,
  output key_words_sel_e   key_words_sel_o,
  output round_key_sel_e   round_key_sel_o,

  // Register signals
  input  logic             crypt_q_i,            // Sparsify using multi-rail.
  output logic             crypt_d_o,            // Sparsify using multi-rail.
  input  logic             dec_key_gen_q_i,      // Sparsify using multi-rail.
  output logic             dec_key_gen_d_o,      // Sparsify using multi-rail.
  input  logic             prng_reseed_q_i,
  output logic             prng_reseed_d_o,
  input  logic             key_clear_q_i,
  output logic             key_clear_d_o,
  input  logic             data_out_clear_q_i,
  output logic             data_out_clear_d_o
);

  // cfg_valid_i is used for SVAs only.
  logic unused_cfg_valid;
  assign unused_cfg_valid = cfg_valid_i;

  // Tie off unused inputs.
  if (!SecMasking) begin : gen_unused_prng_reseed
    logic unused_prng_reseed;
    assign unused_prng_reseed = prng_reseed_i;
  end

  // Signals
  aes_cipher_ctrl_e aes_cipher_ctrl_ns, aes_cipher_ctrl_cs;
  logic             advance;
  logic       [2:0] cyc_ctr_d, cyc_ctr_q;
  logic             cyc_ctr_expr;
  logic             prng_reseed_done_d, prng_reseed_done_q;
  logic       [3:0] rnd_ctr_d, rnd_ctr_q;
  logic       [3:0] num_rounds_d, num_rounds_q;
  logic       [3:0] num_rounds_regular;

  // Use separate signal for number of regular rounds.
  assign num_rounds_regular = num_rounds_q - 4'd1;

  // FSM
  always_comb begin : aes_cipher_ctrl_fsm

    // Handshake signals
    in_ready_o           = 1'b0;
    out_valid_o          = 1'b0;

    // Masking PRNG signals
    prng_update_o        = 1'b0;
    prng_reseed_req_o    = 1'b0;

    // Cipher data path
    state_sel_o          = STATE_ROUND;
    state_we_o           = 1'b0;
    add_rk_sel_o         = ADD_RK_ROUND;
    sub_bytes_en_o       = 1'b0;
    sub_bytes_out_ack_o  = 1'b0;

    // Key expand data path
    key_full_sel_o       = KEY_FULL_ROUND;
    key_full_we_o        = 1'b0;
    key_dec_sel_o        = KEY_DEC_EXPAND;
    key_dec_we_o         = 1'b0;
    key_expand_en_o      = 1'b0;
    key_expand_out_ack_o = 1'b0;
    key_expand_clear_o   = 1'b0;
    key_words_sel_o      = KEY_WORDS_ZERO;
    round_key_sel_o      = ROUND_KEY_DIRECT;

    // FSM
    aes_cipher_ctrl_ns   = aes_cipher_ctrl_cs;
    num_rounds_d         = num_rounds_q;
    rnd_ctr_d            = rnd_ctr_q;
    crypt_d_o            = crypt_q_i;
    dec_key_gen_d_o      = dec_key_gen_q_i;
    prng_reseed_d_o      = prng_reseed_q_i;
    key_clear_d_o        = key_clear_q_i;
    data_out_clear_d_o   = data_out_clear_q_i;
    prng_reseed_done_d   = prng_reseed_done_q | prng_reseed_ack_i;
    advance              = 1'b0;
    cyc_ctr_d            = (SecSBoxImpl == SBoxImplDom) ? cyc_ctr_q + 3'd1 : 3'd0;

    // Alert
    alert_o              = 1'b0;

    unique case (aes_cipher_ctrl_cs)

      CIPHER_CTRL_IDLE: begin
        cyc_ctr_d = 3'd0;

        // Signal that we are ready, wait for handshake.
        in_ready_o = 1'b1;
        if (in_valid_i) begin
          if (SecMasking && prng_reseed_i && !dec_key_gen_i && !crypt_i) begin
            // Reseed the masking PRNG without starting encryption/decryption or generation of the
            // start key for decryption.
            prng_reseed_d_o    = 1'b1;
            prng_reseed_done_d = 1'b0;
            aes_cipher_ctrl_ns = CIPHER_CTRL_PRNG_RESEED;

          end else if (key_clear_i || data_out_clear_i) begin
            // Clear internal key registers. The cipher core muxes are used to clear the data
            // output registers.
            key_clear_d_o      = key_clear_i;
            data_out_clear_d_o = data_out_clear_i;

            // To clear the data output registers, we must first clear the state.
            aes_cipher_ctrl_ns = data_out_clear_i ? CIPHER_CTRL_CLEAR_S : CIPHER_CTRL_CLEAR_KD;

          end else if (dec_key_gen_i || crypt_i) begin
            // Start encryption/decryption or generation of start key for decryption.
            crypt_d_o       = ~dec_key_gen_i & crypt_i;
            dec_key_gen_d_o =  dec_key_gen_i;

            // Latch whether we shall reseed the masking PRNG.
            prng_reseed_d_o = SecMasking & prng_reseed_i;

            // Load input data to state
            state_sel_o = dec_key_gen_i ? STATE_CLEAR : STATE_INIT;
            state_we_o  = 1'b1;

            // Make the masking PRNG advance. The current pseudo-random data is used to mask the
            // input data.
            prng_update_o = dec_key_gen_i ? 1'b0 : SecMasking;

            // Init key expand
            key_expand_clear_o = 1'b1;

            // Load full key
            key_full_sel_o = dec_key_gen_i ? KEY_FULL_ENC_INIT :
                        (op_i == CIPH_FWD) ? KEY_FULL_ENC_INIT :
                        (op_i == CIPH_INV) ? KEY_FULL_DEC_INIT :
                                             KEY_FULL_ENC_INIT;
            key_full_we_o  = 1'b1;

            // Load num_rounds, initialize round counter.
            num_rounds_d = (key_len_i == AES_128) ? 4'd10 :
                           (key_len_i == AES_192) ? 4'd12 :
                                                    4'd14;
            rnd_ctr_d          = '0;
            aes_cipher_ctrl_ns = CIPHER_CTRL_INIT;

          end else begin
            // Handshake without a valid command. We should never get here. If we do (e.g. via a
            // malicious glitch), error out immediately.
            aes_cipher_ctrl_ns = CIPHER_CTRL_ERROR;
          end
        end
      end

      CIPHER_CTRL_INIT: begin
        // Initial round: just add key to state
        add_rk_sel_o = ADD_RK_INIT;

        // Select key words for initial add_round_key
        key_words_sel_o = (dec_key_gen_q_i)            ? KEY_WORDS_ZERO :
            (key_len_i == AES_128)                     ? KEY_WORDS_0123 :
            (key_len_i == AES_192 && op_i == CIPH_FWD) ? KEY_WORDS_0123 :
            (key_len_i == AES_192 && op_i == CIPH_INV) ? KEY_WORDS_2345 :
            (key_len_i == AES_256 && op_i == CIPH_FWD) ? KEY_WORDS_0123 :
            (key_len_i == AES_256 && op_i == CIPH_INV) ? KEY_WORDS_4567 : KEY_WORDS_ZERO;

        // Clear masking PRNG reseed status.
        prng_reseed_done_d = 1'b0;

        // AES-256 has two round keys available right from beginning. Pseudo-random data is
        // required by KeyExpand only.
        if (key_len_i != AES_256) begin
          // Advance in sync with KeyExpand. Based on the S-Box implementation, it can take
          // multiple cycles to finish. Wait for handshake. The DOM S-Boxes consume fresh PRD
          // only in the first clock cycle. By requesting the PRNG update in any clock cycle
          // other than the last one, the PRD fed into the DOM S-Boxes is guaranteed to be stable.
          // This is better in terms of SCA resistance. Request the PRNG update in the first cycle.
          advance         = key_expand_out_req_i & cyc_ctr_expr;
          prng_update_o   = (SecSBoxImpl == SBoxImplDom) ? cyc_ctr_q == 3'd0 : SecMasking;
          key_expand_en_o = 1'b1;
          if (advance) begin
            key_expand_out_ack_o = 1'b1;
            state_we_o           = ~dec_key_gen_q_i;
            key_full_we_o        = 1'b1;
            rnd_ctr_d            = rnd_ctr_q + 4'b0001;
            cyc_ctr_d            = 3'd0;
            aes_cipher_ctrl_ns   = CIPHER_CTRL_ROUND;
          end
        end else begin
          state_we_o         = ~dec_key_gen_q_i;
          rnd_ctr_d          = rnd_ctr_q + 4'b0001;
          cyc_ctr_d          = 3'd0;
          aes_cipher_ctrl_ns = CIPHER_CTRL_ROUND;
        end
      end

      CIPHER_CTRL_ROUND: begin
        // Normal rounds

        // Select key words for add_round_key
        key_words_sel_o = (dec_key_gen_q_i)            ? KEY_WORDS_ZERO :
            (key_len_i == AES_128)                     ? KEY_WORDS_0123 :
            (key_len_i == AES_192 && op_i == CIPH_FWD) ? KEY_WORDS_2345 :
            (key_len_i == AES_192 && op_i == CIPH_INV) ? KEY_WORDS_0123 :
            (key_len_i == AES_256 && op_i == CIPH_FWD) ? KEY_WORDS_4567 :
            (key_len_i == AES_256 && op_i == CIPH_INV) ? KEY_WORDS_0123 : KEY_WORDS_ZERO;

        // Keep requesting PRNG reseeding until it is acknowledged.
        prng_reseed_req_o = SecMasking & prng_reseed_q_i & ~prng_reseed_done_q;

        // Select round key: direct or mixed (equivalent inverse cipher)
        round_key_sel_o = (op_i == CIPH_FWD) ? ROUND_KEY_DIRECT :
                          (op_i == CIPH_INV) ? ROUND_KEY_MIXED  : ROUND_KEY_DIRECT;

        // Advance in sync with SubBytes and KeyExpand. Based on the S-Box implementation, both can
        // take multiple cycles to finish. Wait for handshake. The DOM S-Boxes consume fresh PRD
        // only in the first clock cycle. By requesting the PRNG update in any clock cycle other
        // than the last one, the PRD fed into the DOM S-Boxes is guaranteed to be stable. This is
        // better in terms of SCA resistance. Request the PRNG update in the first cycle. Non-DOM
        // S-Boxes need fresh PRD in every clock cycle.
        advance = key_expand_out_req_i & cyc_ctr_expr & (dec_key_gen_q_i | sub_bytes_out_req_i);
        prng_update_o   = (SecSBoxImpl == SBoxImplDom) ? cyc_ctr_q == 3'd0 : SecMasking;
        sub_bytes_en_o  = ~dec_key_gen_q_i;
        key_expand_en_o = 1'b1;

        if (advance) begin
          sub_bytes_out_ack_o  = ~dec_key_gen_q_i;
          key_expand_out_ack_o = 1'b1;

          state_we_o    = ~dec_key_gen_q_i;
          key_full_we_o = 1'b1;

          // Update round
          rnd_ctr_d     = rnd_ctr_q + 4'b0001;
          cyc_ctr_d     = 3'd0;

          // Are we doing the last regular round?
          if (rnd_ctr_q >= num_rounds_regular) begin
            aes_cipher_ctrl_ns = CIPHER_CTRL_FINISH;

            if (dec_key_gen_q_i) begin
              // Write decryption key.
              key_dec_we_o = 1'b1;

              // Indicate that we are done, try to perform the handshake. But we don't wait here.
              // If we don't get the handshake now, we will wait in the finish state. When using
              // masking, we only finish if the masking PRNG has been reseeded.
              out_valid_o = SecMasking ? (prng_reseed_q_i ? prng_reseed_done_q : 1'b1) : 1'b1;
              if (out_valid_o && out_ready_i) begin
                // Go to idle state directly.
                dec_key_gen_d_o    = 1'b0;
                prng_reseed_d_o    = 1'b0;
                aes_cipher_ctrl_ns = CIPHER_CTRL_IDLE;
              end
            end
          end // rnd_ctr_q
        end // SubBytes/KeyExpand REQ/ACK
      end

      CIPHER_CTRL_FINISH: begin
        // Final round

        // Select key words for add_round_key
        key_words_sel_o = (dec_key_gen_q_i)            ? KEY_WORDS_ZERO :
            (key_len_i == AES_128)                     ? KEY_WORDS_0123 :
            (key_len_i == AES_192 && op_i == CIPH_FWD) ? KEY_WORDS_2345 :
            (key_len_i == AES_192 && op_i == CIPH_INV) ? KEY_WORDS_0123 :
            (key_len_i == AES_256 && op_i == CIPH_FWD) ? KEY_WORDS_4567 :
            (key_len_i == AES_256 && op_i == CIPH_INV) ? KEY_WORDS_0123 : KEY_WORDS_ZERO;

        // Skip mix_columns
        add_rk_sel_o = ADD_RK_FINAL;

        // Keep requesting PRNG reseeding until it is acknowledged.
        prng_reseed_req_o = SecMasking & prng_reseed_q_i & ~prng_reseed_done_q;

        // SEC_CM: DATA_REG.KEY.SCA
        // Once we're done, we won't need the state anymore. We actually clear it when progressing
        // to the next state.
        state_sel_o = STATE_CLEAR;

        // SEC_CM: DATA_REG.LOCAL_ESC
        // Advance in sync with SubBytes. Based on the S-Box implementation, it can take multiple
        // cycles to finish. Only indicate that we are done if:
        // - we have valid output (SubBytes finished),
        // - the masking PRNG has been reseeded (if masking is used),
        // - all mux selector signals are valid (don't release data in case of errors), and
        // - all sparsely encoded signals are valid (don't release data in case of errors).
        // Perform both handshakes simultaneously.
        advance        = (sub_bytes_out_req_i & cyc_ctr_expr) | dec_key_gen_q_i;
        sub_bytes_en_o = ~dec_key_gen_q_i;
        out_valid_o    = (mux_sel_err_i || sp_enc_err_i || op_err_i) ? 1'b0         :
            SecMasking ? (prng_reseed_q_i ? prng_reseed_done_q & advance : advance) : advance;

        // Stop updating the cycle counter once we have valid output.
        cyc_ctr_d =
            (SecSBoxImpl == SBoxImplDom) ? (!advance ? cyc_ctr_q + 3'd1 : cyc_ctr_q) : 3'd0;

        // The DOM S-Boxes consume fresh PRD only in the first clock cycle. By requesting the PRNG
        // update in any clock cycle other than the last one, the PRD fed into the DOM S-Boxes is
        // guaranteed to be stable. This is better in terms of SCA resistance. Request the PRNG
        // update in the first cycle. We update it only once and in the last cycle for non-DOM
        // S-Boxes where otherwise updating the PRNG while being stalled would cause the S-Boxes
        // to be re-evaluated, thereby creating additional SCA leakage.
        prng_update_o =
            (SecSBoxImpl == SBoxImplDom) ? cyc_ctr_q == 3'd0 : out_valid_o & out_ready_i;

        if (out_valid_o && out_ready_i) begin
          sub_bytes_out_ack_o = ~dec_key_gen_q_i;

          // Clear the state.
          state_we_o          = 1'b1;
          crypt_d_o           = 1'b0;
          cyc_ctr_d           = 3'd0;
          // If we were generating the decryption key and didn't get the handshake in the last
          // regular round, we should clear dec_key_gen now.
          dec_key_gen_d_o     = 1'b0;
          prng_reseed_d_o     = 1'b0;
          aes_cipher_ctrl_ns  = CIPHER_CTRL_IDLE;
        end
      end

      CIPHER_CTRL_PRNG_RESEED: begin
        // Keep requesting PRNG reseeding until it is acknowledged.
        prng_reseed_req_o = prng_reseed_q_i & ~prng_reseed_done_q;

        // Once we're done, wait for handshake.
        out_valid_o = prng_reseed_done_q;
        if (out_valid_o && out_ready_i) begin
          prng_reseed_d_o    = 1'b0;
          aes_cipher_ctrl_ns = CIPHER_CTRL_IDLE;
        end
      end

      CIPHER_CTRL_CLEAR_S: begin
        // Clear the state with pseudo-random data.
        state_we_o         = 1'b1;
        state_sel_o        = STATE_CLEAR;
        aes_cipher_ctrl_ns = CIPHER_CTRL_CLEAR_KD;
      end

      CIPHER_CTRL_CLEAR_KD: begin
        // Clear internal key registers and/or external data output registers.
        if (key_clear_q_i) begin
          key_full_sel_o = KEY_FULL_CLEAR;
          key_full_we_o  = 1'b1;
          key_dec_sel_o  = KEY_DEC_CLEAR;
          key_dec_we_o   = 1'b1;
        end
        if (data_out_clear_q_i) begin
          // Forward the state (previously cleared with psuedo-random data).
          // SEC_CM: DATA_REG.SEC_WIPE
          add_rk_sel_o    = ADD_RK_INIT;
          key_words_sel_o = KEY_WORDS_ZERO;
          round_key_sel_o = ROUND_KEY_DIRECT;
        end
        // Indicate that we are done, wait for handshake.
        out_valid_o = 1'b1;
        if (out_ready_i) begin
          key_clear_d_o      = 1'b0;
          data_out_clear_d_o = 1'b0;
          aes_cipher_ctrl_ns = CIPHER_CTRL_IDLE;
        end
      end

      CIPHER_CTRL_ERROR: begin
        // SEC_CM: CIPHER.FSM.LOCAL_ESC
        // Terminal error state
        alert_o = 1'b1;
      end

      // We should never get here. If we do (e.g. via a malicious glitch), error out immediately.
      default: begin
        aes_cipher_ctrl_ns = CIPHER_CTRL_ERROR;
        alert_o = 1'b1;
      end
    endcase

    // Unconditionally jump into the terminal error state in case a mux selector or a sparsely
    // encoded signal becomes invalid, in case we have detected a fault in the round counter,
    // or if a fatal alert has been triggered.
    if (mux_sel_err_i || sp_enc_err_i || rnd_ctr_err_i || op_err_i || alert_fatal_i) begin
      aes_cipher_ctrl_ns = CIPHER_CTRL_ERROR;
    end
  end

  // SEC_CM: CIPHER.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, aes_cipher_ctrl_ns,
      aes_cipher_ctrl_cs, aes_cipher_ctrl_e, CIPHER_CTRL_IDLE)

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_fsm
    if (!rst_ni) begin
      prng_reseed_done_q <= 1'b0;
      rnd_ctr_q          <= '0;
      num_rounds_q       <= '0;
    end else begin
      prng_reseed_done_q <= prng_reseed_done_d;
      rnd_ctr_q          <= rnd_ctr_d;
      num_rounds_q       <= num_rounds_d;
    end
  end

  assign rnd_ctr_o = rnd_ctr_q;

  if (SecSBoxImpl == SBoxImplDom) begin : gen_cyc_ctr
    always_ff @(posedge clk_i or negedge rst_ni) begin : reg_cyc_ctr
      if (!rst_ni) begin
        cyc_ctr_q <= 3'd0;
      end else begin
        cyc_ctr_q <= cyc_ctr_d;
      end
    end
    assign cyc_ctr_expr = cyc_ctr_q >= 3'd4;
  end else begin : gen_no_cyc_ctr
    logic [2:0] unused_cyc_ctr;
    assign cyc_ctr_q      = cyc_ctr_d;
    assign unused_cyc_ctr = cyc_ctr_q;
    assign cyc_ctr_expr   = 1'b1;
  end

  ////////////////
  // Assertions //
  ////////////////

  // Create a lint error to reduce the risk of accidentally disabling the masking.
  `ASSERT_STATIC_LINT_ERROR(AesCipherControlFsmSecMaskingNonDefault, SecMasking == 1)

  // Create a lint error to reduce the risk of accidentally using a less secure SBox
  // implementation.
  `ASSERT_STATIC_LINT_ERROR(AesCipherControlFsmSecSBoxImplNonDefault, SecSBoxImpl == SBoxImplDom)

  // Selectors must be known/valid
  `ASSERT(AesCiphOpValid, cfg_valid_i |-> op_i inside {
      CIPH_FWD,
      CIPH_INV
      })
  `ASSERT(AesKeyLenValid, cfg_valid_i |-> key_len_i inside {
      AES_128,
      AES_192,
      AES_256
      })
  `ASSERT(AesCipherControlStateValid, !alert_o |-> aes_cipher_ctrl_cs inside {
      CIPHER_CTRL_IDLE,
      CIPHER_CTRL_INIT,
      CIPHER_CTRL_ROUND,
      CIPHER_CTRL_FINISH,
      CIPHER_CTRL_PRNG_RESEED,
      CIPHER_CTRL_CLEAR_S,
      CIPHER_CTRL_CLEAR_KD
      })

endmodule
