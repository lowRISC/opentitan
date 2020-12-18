// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES cipher core control
//
// This module controls the AES cipher core including the key expand module.

`include "prim_assert.sv"

module aes_cipher_control
#(
  parameter bit Masking = 0
) (
  input  logic                    clk_i,
  input  logic                    rst_ni,

  // Input handshake signals
  input  logic                    in_valid_i,
  output logic                    in_ready_o,

  // Output handshake signals
  output logic                    out_valid_o,
  input  logic                    out_ready_i,

  // Control and sync signals
  input  logic                    cfg_valid_i,
  input  aes_pkg::ciph_op_e       op_i,
  input  aes_pkg::key_len_e       key_len_i,
  input  logic                    crypt_i,
  output logic                    crypt_o,
  input  logic                    dec_key_gen_i,
  output logic                    dec_key_gen_o,
  input  logic                    key_clear_i,
  output logic                    key_clear_o,
  input  logic                    data_out_clear_i,
  output logic                    data_out_clear_o,

  // Control signals for masking PRNG
  output logic                    prng_update_o,
  output logic                    prng_reseed_req_o,
  input  logic                    prng_reseed_ack_i,

  // Control and sync signals for cipher data path
  output aes_pkg::state_sel_e     state_sel_o,
  output logic                    state_we_o,
  output logic                    sub_bytes_en_o,
  input  logic                    sub_bytes_out_req_i,
  output logic                    sub_bytes_out_ack_o,
  output aes_pkg::add_rk_sel_e    add_rk_sel_o,

  // Control and sync signals for key expand data path
  output aes_pkg::ciph_op_e       key_expand_op_o,
  output aes_pkg::key_full_sel_e  key_full_sel_o,
  output logic                    key_full_we_o,
  output aes_pkg::key_dec_sel_e   key_dec_sel_o,
  output logic                    key_dec_we_o,
  output logic                    key_expand_en_o,
  input  logic                    key_expand_out_req_i,
  output logic                    key_expand_out_ack_o,
  output logic                    key_expand_clear_o,
  output logic [3:0]              key_expand_round_o,
  output aes_pkg::key_words_sel_e key_words_sel_o,
  output aes_pkg::round_key_sel_e round_key_sel_o
);

  import aes_pkg::*;

  // Types
  typedef enum logic [2:0] {
    IDLE, INIT, ROUND, FINISH, CLEAR_S, CLEAR_KD
  } aes_cipher_ctrl_e;

  aes_cipher_ctrl_e aes_cipher_ctrl_ns, aes_cipher_ctrl_cs;

  // Signals
  logic [3:0] round_d, round_q;
  logic [3:0] num_rounds_d, num_rounds_q;
  logic [3:0] num_rounds_regular;
  logic       crypt_d, crypt_q;
  logic       dec_key_gen_d, dec_key_gen_q;
  logic       key_clear_d, key_clear_q;
  logic       data_out_clear_d, data_out_clear_q;
  logic       prng_reseed_done_d, prng_reseed_done_q;

  // cfg_valid_i is used for gating assertions only.
  logic       unused_cfg_valid;
  assign unused_cfg_valid = cfg_valid_i;

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
    round_d              = round_q;
    num_rounds_d         = num_rounds_q;
    crypt_d              = crypt_q;
    dec_key_gen_d        = dec_key_gen_q;
    key_clear_d          = key_clear_q;
    data_out_clear_d     = data_out_clear_q;
    prng_reseed_done_d   = prng_reseed_done_q | prng_reseed_ack_i;

    unique case (aes_cipher_ctrl_cs)

      IDLE: begin
        dec_key_gen_d = 1'b0;

        // Signal that we are ready, wait for handshake.
        in_ready_o = 1'b1;
        if (in_valid_i) begin
          if (key_clear_i || data_out_clear_i) begin
            // Clear internal key registers. The cipher core muxes are used to clear the data
            // output registers.
            key_clear_d      = key_clear_i;
            data_out_clear_d = data_out_clear_i;

            // To clear the data output registers, we must first clear the state.
            aes_cipher_ctrl_ns = data_out_clear_i ? CLEAR_S : CLEAR_KD;

          end else if (dec_key_gen_i || crypt_i) begin
            // Start encryption/decryption or generation of start key for decryption.
            crypt_d       = ~dec_key_gen_i;
            dec_key_gen_d =  dec_key_gen_i;

            // Load input data to state
            state_sel_o = dec_key_gen_d ? STATE_CLEAR : STATE_INIT;
            state_we_o  = 1'b1;

            // Make the masking PRNG advance. The current pseudo-random data is used to mask the
            // input data.
            prng_update_o = dec_key_gen_d ? 1'b0 : Masking;

            // Init key expand
            key_expand_clear_o = 1'b1;

            // Load full key
            key_full_sel_o = dec_key_gen_d ? KEY_FULL_ENC_INIT :
                        (op_i == CIPH_FWD) ? KEY_FULL_ENC_INIT :
                                             KEY_FULL_DEC_INIT;
            key_full_we_o  = 1'b1;

            // Load num_rounds, clear round
            round_d      = '0;
            num_rounds_d = (key_len_i == AES_128) ? 4'd10 :
                           (key_len_i == AES_192) ? 4'd12 :
                                                    4'd14;
            aes_cipher_ctrl_ns = INIT;
          end
        end
      end

      INIT: begin
        // Initial round: just add key to state
        add_rk_sel_o = ADD_RK_INIT;

        // Select key words for initial add_round_key
        key_words_sel_o = dec_key_gen_q                ? KEY_WORDS_ZERO :
            (key_len_i == AES_128)                     ? KEY_WORDS_0123 :
            (key_len_i == AES_192 && op_i == CIPH_FWD) ? KEY_WORDS_0123 :
            (key_len_i == AES_192 && op_i == CIPH_INV) ? KEY_WORDS_2345 :
            (key_len_i == AES_256 && op_i == CIPH_FWD) ? KEY_WORDS_0123 :
            (key_len_i == AES_256 && op_i == CIPH_INV) ? KEY_WORDS_4567 : KEY_WORDS_ZERO;

        // Clear masking PRNG reseed status.
        prng_reseed_done_d = 1'b0;

        // AES-256 has two round keys available right from beginning. Pseudo-random data is
        // required by KeyExpand only, and only if it is actually advancing.
        if (key_len_i != AES_256) begin
          // Advance in sync with KeyExpand. Based on the S-Box implementation, it can take
          // multiple cycles to finish. Wait for handshake.
          key_expand_en_o = 1'b1;
          if (key_expand_out_req_i) begin
            key_expand_out_ack_o = 1'b1;
            state_we_o           = ~dec_key_gen_q;
            key_full_we_o        = 1'b1;
            prng_update_o        = Masking;
            aes_cipher_ctrl_ns   = ROUND;
          end
        end else begin
          state_we_o         = ~dec_key_gen_q;
          aes_cipher_ctrl_ns = ROUND;
        end
      end

      ROUND: begin
        // Normal rounds

        // Select key words for add_round_key
        key_words_sel_o = dec_key_gen_q                ? KEY_WORDS_ZERO :
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
        // take multiple cycles to finish. Wait for handshake.
        sub_bytes_en_o  = ~dec_key_gen_q;
        key_expand_en_o = 1'b1;
        if ((dec_key_gen_q || sub_bytes_out_req_i) && key_expand_out_req_i) begin
          sub_bytes_out_ack_o  = ~dec_key_gen_q;
          key_expand_out_ack_o = 1'b1;

          state_we_o    = ~dec_key_gen_q;
          key_full_we_o = 1'b1;

          // Update round
          round_d = round_q + 4'b0001;

          // Make the masking PRNG advance once per round only. Updating it while waiting for key
          // expand would cause the SBoxes to be re-evaluated, thereby creating additional SCA
          // leakage.
          prng_update_o = Masking;

          // Are we doing the last regular round?
          if (round_q == num_rounds_regular) begin
            aes_cipher_ctrl_ns = FINISH;

            if (dec_key_gen_q) begin
              // Write decryption key.
              key_dec_we_o = 1'b1;

              // Indicate that we are done, try to perform the handshake. But we don't wait here.
              // If we don't get the handshake now, we will wait in the finish state. When using
              // masking, we only finish if the masking PRNG has been reseeded.
              out_valid_o = Masking ? prng_reseed_done_q : 1'b1;
              if (out_valid_o && out_ready_i) begin
                // Go to idle state directly.
                dec_key_gen_d      = 1'b0;
                aes_cipher_ctrl_ns = IDLE;
              end
            end
          end // round_q
        end // SubBytes/KeyExpand REQ/ACK
      end

      FINISH: begin
        // Final round

        // Select key words for add_round_key
        key_words_sel_o = dec_key_gen_q                ? KEY_WORDS_ZERO :
            (key_len_i == AES_128)                     ? KEY_WORDS_0123 :
            (key_len_i == AES_192 && op_i == CIPH_FWD) ? KEY_WORDS_2345 :
            (key_len_i == AES_192 && op_i == CIPH_INV) ? KEY_WORDS_0123 :
            (key_len_i == AES_256 && op_i == CIPH_FWD) ? KEY_WORDS_4567 :
            (key_len_i == AES_256 && op_i == CIPH_INV) ? KEY_WORDS_0123 : KEY_WORDS_ZERO;

        // Skip mix_columns
        add_rk_sel_o = ADD_RK_FINAL;

        // Advance in sync with SubBytes. Based on the S-Box implementation, it can take multiple
        // cycles to finish. Only indicate that we are done if:
        // - we have valid output (SubBytes finished), and
        // - the masking PRNG has been reseeded (if masking is used).
        // Perform both handshakes simultaneously.
        sub_bytes_en_o = ~dec_key_gen_q;
        out_valid_o    = (dec_key_gen_q | sub_bytes_out_req_i) & (Masking == prng_reseed_done_q);
        if (out_valid_o && out_ready_i) begin
          sub_bytes_out_ack_o = ~dec_key_gen_q;

          // We don't need the state anymore, clear it.
          state_we_o          = 1'b1;
          state_sel_o         = STATE_CLEAR;
          crypt_d             = 1'b0;
          // Make the masking PRNG advance once only. Updating it while being stalled would
          // cause the SBoxes to be re-evaluated, thereby creating additional SCA leakage.
          prng_update_o       = Masking;
          // If we were generating the decryption key and didn't get the handshake in the last
          // regular round, we should clear dec_key_gen now.
          dec_key_gen_d       = 1'b0;
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
        if (key_clear_q) begin
          key_full_sel_o = KEY_FULL_CLEAR;
          key_full_we_o  = 1'b1;
          key_dec_sel_o  = KEY_DEC_CLEAR;
          key_dec_we_o   = 1'b1;
        end
        if (data_out_clear_q) begin
          // Forward the state (previously cleared with psuedo-random data).
          add_rk_sel_o    = ADD_RK_INIT;
          key_words_sel_o = KEY_WORDS_ZERO;
          round_key_sel_o = ROUND_KEY_DIRECT;
        end
        // Indicate that we are done, wait for handshake.
        out_valid_o = 1'b1;
        if (out_ready_i) begin
          key_clear_d        = 1'b0;
          data_out_clear_d   = 1'b0;
          aes_cipher_ctrl_ns = IDLE;
        end
      end

      default: aes_cipher_ctrl_ns = IDLE;
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_fsm
    if (!rst_ni) begin
      aes_cipher_ctrl_cs <= IDLE;
      round_q            <= '0;
      num_rounds_q       <= '0;
      crypt_q            <= 1'b0;
      dec_key_gen_q      <= 1'b0;
      key_clear_q        <= 1'b0;
      data_out_clear_q   <= 1'b0;
      prng_reseed_done_q <= 1'b0;
    end else begin
      aes_cipher_ctrl_cs <= aes_cipher_ctrl_ns;
      round_q            <= round_d;
      num_rounds_q       <= num_rounds_d;
      crypt_q            <= crypt_d;
      dec_key_gen_q      <= dec_key_gen_d;
      key_clear_q        <= key_clear_d;
      data_out_clear_q   <= data_out_clear_d;
      prng_reseed_done_q <= prng_reseed_done_d;
    end
  end

  // Use separate signal for number of regular rounds.
  assign num_rounds_regular = num_rounds_q - 4'd2;

  // Use separate signals for key expand operation and round.
  assign key_expand_op_o    = (dec_key_gen_d || dec_key_gen_q) ? CIPH_FWD : op_i;
  assign key_expand_round_o = round_d;

  // Let the main controller know whate we are doing.
  assign crypt_o          = crypt_q;
  assign dec_key_gen_o    = dec_key_gen_q;
  assign key_clear_o      = key_clear_q;
  assign data_out_clear_o = data_out_clear_q;

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
  `ASSERT(AesControlStateValid, aes_cipher_ctrl_cs inside {
      IDLE,
      INIT,
      ROUND,
      FINISH,
      CLEAR_S,
      CLEAR_KD
      })

endmodule
