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
  parameter bit         Masking  = 0,
  parameter sbox_impl_e SBoxImpl = SBoxImplLut
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
  input  logic             key_clear_i,
  input  logic             data_out_clear_i,
  input  logic             mux_sel_err_i,
  input  logic             sp_enc_err_i,
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
  output key_words_sel_e   key_words_sel_o,
  output round_key_sel_e   round_key_sel_o,

  // Register signals
  input  logic [3:0]       rnd_ctr_q_i,
  output logic [3:0]       rnd_ctr_d_o,
  input  logic [3:0]       rnd_ctr_rem_q_i,
  output logic [3:0]       rnd_ctr_rem_d_o,
  input  logic [3:0]       num_rounds_q_i,
  output logic [3:0]       num_rounds_d_o,
  input  logic             rnd_ctr_err_i,
  input  logic             crypt_q_i,            // Sparsify using multi-rail.
  output logic             crypt_d_o,            // Sparsify using multi-rail.
  input  logic             dec_key_gen_q_i,      // Sparsify using multi-rail.
  output logic             dec_key_gen_d_o,      // Sparsify using multi-rail.
  input  logic             key_clear_q_i,
  output logic             key_clear_d_o,
  input  logic             data_out_clear_q_i,
  output logic             data_out_clear_d_o
);

  // Types
  // $ ./sparse-fsm-encode.py -d 3 -m 7 -n 6 \
  //      -s 31468618 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (57.14%)
  //  4: ||||||||||||||| (42.86%)
  //  5: --
  //  6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 4
  //
  localparam int StateWidth = 6;
  typedef enum logic [StateWidth-1:0] {
    IDLE     = 6'b111100,
    INIT     = 6'b101001,
    ROUND    = 6'b010000,
    FINISH   = 6'b100010,
    CLEAR_S  = 6'b011011,
    CLEAR_KD = 6'b110111,
    ERROR    = 6'b001110
  } aes_cipher_ctrl_e;

  // cfg_valid_i is used for SVAs only.
  logic unused_cfg_valid;
  assign unused_cfg_valid = cfg_valid_i;

  // Signals
  aes_cipher_ctrl_e aes_cipher_ctrl_ns, aes_cipher_ctrl_cs;
  logic             advance;
  logic             prng_reseed_done_d, prng_reseed_done_q;
  logic       [3:0] num_rounds_regular;

  // Use separate signal for number of regular rounds.
  assign num_rounds_regular = num_rounds_q_i - 4'd1;

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
    num_rounds_d_o       = num_rounds_q_i;
    rnd_ctr_d_o          = rnd_ctr_q_i;
    rnd_ctr_rem_d_o      = rnd_ctr_rem_q_i;
    crypt_d_o            = crypt_q_i;
    dec_key_gen_d_o      = dec_key_gen_q_i;
    key_clear_d_o        = key_clear_q_i;
    data_out_clear_d_o   = data_out_clear_q_i;
    prng_reseed_done_d   = prng_reseed_done_q | prng_reseed_ack_i;
    advance              = 1'b0;

    // Alert
    alert_o              = 1'b0;

    unique case (aes_cipher_ctrl_cs)

      IDLE: begin
        dec_key_gen_d_o = 1'b0;

        // Signal that we are ready, wait for handshake.
        in_ready_o = 1'b1;
        if (in_valid_i) begin
          if (key_clear_i || data_out_clear_i) begin
            // Clear internal key registers. The cipher core muxes are used to clear the data
            // output registers.
            key_clear_d_o      = key_clear_i;
            data_out_clear_d_o = data_out_clear_i;

            // To clear the data output registers, we must first clear the state.
            aes_cipher_ctrl_ns = data_out_clear_i ? CLEAR_S : CLEAR_KD;

          end else if (dec_key_gen_i || crypt_i) begin
            // Start encryption/decryption or generation of start key for decryption.
            crypt_d_o       = ~dec_key_gen_i & crypt_i;
            dec_key_gen_d_o =  dec_key_gen_i;

            // Load input data to state
            state_sel_o = dec_key_gen_i ? STATE_CLEAR : STATE_INIT;
            state_we_o  = 1'b1;

            // Make the masking PRNG advance. The current pseudo-random data is used to mask the
            // input data.
            prng_update_o = dec_key_gen_i ? 1'b0 : Masking;

            // Init key expand
            key_expand_clear_o = 1'b1;

            // Load full key
            key_full_sel_o = dec_key_gen_i ? KEY_FULL_ENC_INIT :
                        (op_i == CIPH_FWD) ? KEY_FULL_ENC_INIT :
                                             KEY_FULL_DEC_INIT;
            key_full_we_o  = 1'b1;

            // Load num_rounds, initialize round counters.
            num_rounds_d_o = (key_len_i == AES_128) ? 4'd10 :
                             (key_len_i == AES_192) ? 4'd12 :
                                                      4'd14;
            rnd_ctr_rem_d_o    = num_rounds_d_o;
            rnd_ctr_d_o        = '0;
            aes_cipher_ctrl_ns = INIT;

          end else begin
            // Handshake without a valid command. We should never get here. If we do (e.g. via a
            // malicious glitch), error out immediately.
            aes_cipher_ctrl_ns = ERROR;
          end
        end
      end

      INIT: begin
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
          // multiple cycles to finish. Wait for handshake. The DOM S-Boxes take fresh PRD
          // in every cycle except the last.
          advance         = key_expand_out_req_i;
          prng_update_o   = (SBoxImpl == SBoxImplDom) ? advance : Masking;
          key_expand_en_o = 1'b1;
          if (advance) begin
            key_expand_out_ack_o = 1'b1;
            state_we_o           = ~dec_key_gen_q_i;
            key_full_we_o        = 1'b1;
            rnd_ctr_d_o          = rnd_ctr_q_i     + 4'b0001;
            rnd_ctr_rem_d_o      = rnd_ctr_rem_q_i - 4'b0001;
            aes_cipher_ctrl_ns   = ROUND;
          end
        end else begin
          state_we_o         = ~dec_key_gen_q_i;
          rnd_ctr_d_o        = rnd_ctr_q_i     + 4'b0001;
          rnd_ctr_rem_d_o    = rnd_ctr_rem_q_i - 4'b0001;
          aes_cipher_ctrl_ns = ROUND;
        end
      end

      ROUND: begin
        // Normal rounds

        // Select key words for add_round_key
        key_words_sel_o = (dec_key_gen_q_i)            ? KEY_WORDS_ZERO :
            (key_len_i == AES_128)                     ? KEY_WORDS_0123 :
            (key_len_i == AES_192 && op_i == CIPH_FWD) ? KEY_WORDS_2345 :
            (key_len_i == AES_192 && op_i == CIPH_INV) ? KEY_WORDS_0123 :
            (key_len_i == AES_256 && op_i == CIPH_FWD) ? KEY_WORDS_4567 :
            (key_len_i == AES_256 && op_i == CIPH_INV) ? KEY_WORDS_0123 : KEY_WORDS_ZERO;

        // Keep requesting PRNG reseeding until it is acknowledged.
        prng_reseed_req_o = Masking & ~prng_reseed_done_q;

        // Select round key: direct or mixed (equivalent inverse cipher)
        round_key_sel_o = (op_i == CIPH_FWD) ? ROUND_KEY_DIRECT : ROUND_KEY_MIXED;

        // Advance in sync with SubBytes and KeyExpand. Based on the S-Box implementation, both can
        // take multiple cycles to finish. Wait for handshake. Make the masking PRNG advance every
        // cycle. The DOM S-Boxes take fresh PRD in every cycle except the last.
        advance         = (dec_key_gen_q_i | sub_bytes_out_req_i) & key_expand_out_req_i;
        prng_update_o   = (SBoxImpl == SBoxImplDom) ? ~advance : Masking;
        sub_bytes_en_o  = ~dec_key_gen_q_i;
        key_expand_en_o = 1'b1;
        if (advance) begin
          sub_bytes_out_ack_o  = ~dec_key_gen_q_i;
          key_expand_out_ack_o = 1'b1;

          state_we_o    = ~dec_key_gen_q_i;
          key_full_we_o = 1'b1;

          // Update round
          rnd_ctr_d_o     = rnd_ctr_q_i     + 4'b0001;
          rnd_ctr_rem_d_o = rnd_ctr_rem_q_i - 4'b0001;

          // Are we doing the last regular round?
          if (rnd_ctr_q_i == num_rounds_regular) begin
            aes_cipher_ctrl_ns = FINISH;

            if (dec_key_gen_q_i) begin
              // Write decryption key.
              key_dec_we_o = 1'b1;

              // Indicate that we are done, try to perform the handshake. But we don't wait here.
              // If we don't get the handshake now, we will wait in the finish state. When using
              // masking, we only finish if the masking PRNG has been reseeded.
              out_valid_o = Masking ? prng_reseed_done_q : 1'b1;
              if (out_valid_o && out_ready_i) begin
                // Go to idle state directly.
                dec_key_gen_d_o    = 1'b0;
                aes_cipher_ctrl_ns = IDLE;
              end
            end
          end // rnd_ctr_q_i
        end // SubBytes/KeyExpand REQ/ACK
      end

      FINISH: begin
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
        prng_reseed_req_o = Masking & ~prng_reseed_done_q;

        // Once we're done, we won't need the state anymore. We actually clear it when progressing
        // to the next state.
        state_sel_o = STATE_CLEAR;

        // Advance in sync with SubBytes. Based on the S-Box implementation, it can take multiple
        // cycles to finish. Only indicate that we are done if:
        // - we have valid output (SubBytes finished),
        // - the masking PRNG has been reseeded (if masking is used),
        // - all mux selector signals are valid (don't release data in case of errors), and
        // - all sparsely encoded signals are valid (don't release data in case of errors).
        // Perform both handshakes simultaneously.
        advance        = sub_bytes_out_req_i | dec_key_gen_q_i;
        sub_bytes_en_o = ~dec_key_gen_q_i;
        out_valid_o    = (mux_sel_err_i || sp_enc_err_i) ? 1'b0 :
                         Masking ? prng_reseed_done_q & advance : advance;
        // When using DOM S-Boxes, make the masking PRNG advance every cycle until the output is
        // ready. For other S-Boxes, make it advance once only. Updating it while being stalled
        // would cause non-DOM S-Boxes to be re-evaluated, thereby creating additional SCA leakage.
        prng_update_o = (SBoxImpl == SBoxImplDom) ? ~advance                  :
                                          Masking ? out_valid_o & out_ready_i : 1'b0;
        if (out_valid_o && out_ready_i) begin
          sub_bytes_out_ack_o = ~dec_key_gen_q_i;

          // Clear the state.
          state_we_o          = 1'b1;
          crypt_d_o           = 1'b0;
          // If we were generating the decryption key and didn't get the handshake in the last
          // regular round, we should clear dec_key_gen now.
          dec_key_gen_d_o     = 1'b0;
          aes_cipher_ctrl_ns  = IDLE;
        end
      end

      CLEAR_S: begin
        // Clear the state with pseudo-random data.
        state_we_o         = 1'b1;
        state_sel_o        = STATE_CLEAR;
        aes_cipher_ctrl_ns = CLEAR_KD;
      end

      CLEAR_KD: begin
        // Clear internal key registers and/or external data output registers.
        if (key_clear_q_i) begin
          key_full_sel_o = KEY_FULL_CLEAR;
          key_full_we_o  = 1'b1;
          key_dec_sel_o  = KEY_DEC_CLEAR;
          key_dec_we_o   = 1'b1;
        end
        if (data_out_clear_q_i) begin
          // Forward the state (previously cleared with psuedo-random data).
          add_rk_sel_o    = ADD_RK_INIT;
          key_words_sel_o = KEY_WORDS_ZERO;
          round_key_sel_o = ROUND_KEY_DIRECT;
        end
        // Indicate that we are done, wait for handshake.
        out_valid_o = 1'b1;
        if (out_ready_i) begin
          key_clear_d_o      = 1'b0;
          data_out_clear_d_o = 1'b0;
          aes_cipher_ctrl_ns = IDLE;
        end
      end

      ERROR: begin
        // Terminal error state
        alert_o = 1'b1;
      end

      // We should never get here. If we do (e.g. via a malicious glitch), error out immediately.
      default: begin
        aes_cipher_ctrl_ns = ERROR;
      end
    endcase

    // Unconditionally jump into the terminal error state in case a mux selector or a sparsely
    // encoded signal becomes invalid, or in case we have detected a fault in the round counter.
    if (mux_sel_err_i || sp_enc_err_i || rnd_ctr_err_i) begin
      aes_cipher_ctrl_ns = ERROR;
    end
  end

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  logic [StateWidth-1:0] aes_cipher_ctrl_cs_raw;
  assign aes_cipher_ctrl_cs = aes_cipher_ctrl_e'(aes_cipher_ctrl_cs_raw);
  prim_flop #(
    .Width(StateWidth),
    .ResetValue(StateWidth'(IDLE))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .d_i ( aes_cipher_ctrl_ns     ),
    .q_o ( aes_cipher_ctrl_cs_raw )
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_fsm
    if (!rst_ni) begin
      prng_reseed_done_q <= 1'b0;
    end else begin
      prng_reseed_done_q <= prng_reseed_done_d;
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid
  `ASSERT_KNOWN(AesCiphOpKnown, op_i)
  `ASSERT(AesKeyLenValid, cfg_valid_i |-> key_len_i inside {
      AES_128,
      AES_192,
      AES_256
      })
  `ASSERT(AesControlStateValid, !alert_o |-> aes_cipher_ctrl_cs inside {
      IDLE,
      INIT,
      ROUND,
      FINISH,
      CLEAR_S,
      CLEAR_KD
      })

endmodule
