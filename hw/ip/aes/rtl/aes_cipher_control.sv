// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES cipher core control
//
// This module controls the AES cipher core including the key expand module.

`include "prim_assert.sv"

module aes_cipher_control (
  input  logic                    clk_i,
  input  logic                    rst_ni,

  // Input handshake signals
  input  logic                    in_valid_i,
  output logic                    in_ready_o,

  // Output handshake signals
  output logic                    out_valid_o,
  input  logic                    out_ready_i,

  // Control and sync signals
  input  aes_pkg::ciph_op_e       op_i,
  input  aes_pkg::key_len_e       key_len_i,
  input  logic                    start_i,
  input  logic                    dec_key_gen_i,
  output logic                    dec_key_gen_o,
  input  logic                    key_clear_i,
  output logic                    key_clear_o,
  input  logic                    data_out_clear_i,
  output logic                    data_out_clear_o,

  // Control outputs cipher data path
  output aes_pkg::state_sel_e     state_sel_o,
  output logic                    state_we_o,
  output aes_pkg::add_rk_sel_e    add_rk_sel_o,

  // Control outputs key expand data path
  output aes_pkg::ciph_op_e       key_expand_op_o,
  output aes_pkg::key_full_sel_e  key_full_sel_o,
  output logic                    key_full_we_o,
  output aes_pkg::key_dec_sel_e   key_dec_sel_o,
  output logic                    key_dec_we_o,
  output logic                    key_expand_step_o,
  output logic                    key_expand_clear_o,
  output logic [3:0]              key_expand_round_o,
  output aes_pkg::key_words_sel_e key_words_sel_o,
  output aes_pkg::round_key_sel_e round_key_sel_o
);

  import aes_pkg::*;

  // Types
  typedef enum logic [2:0] {
    IDLE, INIT, ROUND, FINISH, CLEAR
  } aes_cipher_ctrl_e;

  aes_cipher_ctrl_e aes_cipher_ctrl_ns, aes_cipher_ctrl_cs;

  // Signals
  logic [3:0] round_d, round_q;
  logic [3:0] num_rounds_d, num_rounds_q;
  logic [3:0] num_rounds_regular;
  logic       dec_key_gen_d, dec_key_gen_q;
  logic       key_clear_d, key_clear_q;
  logic       data_out_clear_d, data_out_clear_q;

  // FSM
  always_comb begin : aes_cipher_ctrl_fsm

    // Handshake signals
    in_ready_o         = 1'b0;
    out_valid_o        = 1'b0;

    // Cipher data path
    state_sel_o        = STATE_ROUND;
    state_we_o         = 1'b0;
    add_rk_sel_o       = ADD_RK_ROUND;

    // Key expand data path
    key_full_sel_o     = KEY_FULL_ROUND;
    key_full_we_o      = 1'b0;
    key_dec_sel_o      = KEY_DEC_EXPAND;
    key_dec_we_o       = 1'b0;
    key_expand_step_o  = 1'b0;
    key_expand_clear_o = 1'b0;
    key_words_sel_o    = KEY_WORDS_ZERO;
    round_key_sel_o    = ROUND_KEY_DIRECT;

    // FSM
    aes_cipher_ctrl_ns = aes_cipher_ctrl_cs;
    round_d            = round_q;
    num_rounds_d       = num_rounds_q;
    dec_key_gen_d      = dec_key_gen_q;
    key_clear_d        = key_clear_q;
    data_out_clear_d   = data_out_clear_q;

    unique case (aes_cipher_ctrl_cs)

      IDLE: begin
        dec_key_gen_d = 1'b0;

        // Signal that we are ready, wait for handshake.
        in_ready_o = 1'b1;
        if (in_valid_i) begin
          if (start_i) begin
            // Start generation of start key for decryption.
            dec_key_gen_d = dec_key_gen_i;

            // Load input data to state
            state_sel_o = dec_key_gen_d ? STATE_CLEAR : STATE_INIT;
            state_we_o  = 1'b1;

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
          end else if (key_clear_i || data_out_clear_i) begin
            key_clear_d      = key_clear_i;
            data_out_clear_d = data_out_clear_i;

            aes_cipher_ctrl_ns = CLEAR;
          end
        end
      end

      INIT: begin
        // Initial round: just add key to state
        state_we_o   = ~dec_key_gen_q;
        add_rk_sel_o = ADD_RK_INIT;

        // Select key words for initial add_round_key
        key_words_sel_o = dec_key_gen_q                ? KEY_WORDS_ZERO :
            (key_len_i == AES_128)                     ? KEY_WORDS_0123 :
            (key_len_i == AES_192 && op_i == CIPH_FWD) ? KEY_WORDS_0123 :
            (key_len_i == AES_192 && op_i == CIPH_INV) ? KEY_WORDS_2345 :
            (key_len_i == AES_256 && op_i == CIPH_FWD) ? KEY_WORDS_0123 :
            (key_len_i == AES_256 && op_i == CIPH_INV) ? KEY_WORDS_4567 : KEY_WORDS_ZERO;

        // Make key expand advance - AES-256 has two round keys available right from beginning.
        if (key_len_i != AES_256) begin
          key_expand_step_o = 1'b1;
          key_full_we_o     = 1'b1;
        end

        aes_cipher_ctrl_ns = ROUND;
      end

      ROUND: begin
        // Normal rounds
        state_we_o = ~dec_key_gen_q;

        // Select key words for add_round_key
        key_words_sel_o = dec_key_gen_q                ? KEY_WORDS_ZERO :
            (key_len_i == AES_128)                     ? KEY_WORDS_0123 :
            (key_len_i == AES_192 && op_i == CIPH_FWD) ? KEY_WORDS_2345 :
            (key_len_i == AES_192 && op_i == CIPH_INV) ? KEY_WORDS_0123 :
            (key_len_i == AES_256 && op_i == CIPH_FWD) ? KEY_WORDS_4567 :
            (key_len_i == AES_256 && op_i == CIPH_INV) ? KEY_WORDS_0123 : KEY_WORDS_ZERO;

        // Make key expand advance
        key_expand_step_o = 1'b1;
        key_full_we_o     = 1'b1;

        // Select round key: direct or mixed (equivalent inverse cipher)
        round_key_sel_o = (op_i == CIPH_FWD) ? ROUND_KEY_DIRECT : ROUND_KEY_MIXED;

        // Update round
        round_d = round_q + 4'b1;

        // Are we doing the last regular round?
        if (round_q == num_rounds_regular) begin
          aes_cipher_ctrl_ns = FINISH;

          if (dec_key_gen_q) begin
            // Write decryption key.
            key_dec_we_o = 1'b1;

            // Indicate that we are done, try to perform the handshake. But we don't wait here
            // as the decryption key is valid only during one cycle. If we don't get the
            // handshake now, we will wait in the finish state.
            out_valid_o = 1'b1;
            if (out_ready_i) begin
              // Go to idle state directly.
              dec_key_gen_d      = 1'b0;
              aes_cipher_ctrl_ns = IDLE;
            end
          end
        end
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

        // Indicate that we are done, wait for handshake.
        out_valid_o = 1'b1;
        if (out_ready_i) begin
          // We don't need the state anymore, clear it.
          state_we_o         = 1'b1;
          state_sel_o        = STATE_CLEAR;
          // If we were generating the decryption key and didn't get the handshake in the last
          // regular round, we should clear dec_key_gen now.
          dec_key_gen_d      = 1'b0;
          aes_cipher_ctrl_ns = IDLE;
        end
      end

      CLEAR: begin
        if (key_clear_q) begin
          key_full_sel_o = KEY_FULL_CLEAR;
          key_full_we_o  = 1'b1;
          key_dec_sel_o  = KEY_DEC_CLEAR;
          key_dec_we_o   = 1'b1;
        end
        if (data_out_clear_q) begin
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
      dec_key_gen_q      <= 1'b0;
      key_clear_q        <= 1'b0;
      data_out_clear_q   <= 1'b0;
    end else begin
      aes_cipher_ctrl_cs <= aes_cipher_ctrl_ns;
      round_q            <= round_d;
      num_rounds_q       <= num_rounds_d;
      dec_key_gen_q      <= dec_key_gen_d;
      key_clear_q        <= key_clear_d;
      data_out_clear_q   <= data_out_clear_d;
    end
  end

  // Use separate signal for number of regular rounds.
  assign num_rounds_regular = num_rounds_q - 4'd2;

  // Use separate signals for key expand operation and round.
  assign key_expand_op_o    = (dec_key_gen_d || dec_key_gen_q) ? CIPH_FWD : op_i;
  assign key_expand_round_o = round_d;

  // Let the main controller know whate we are doing.
  assign dec_key_gen_o    = dec_key_gen_q;
  assign key_clear_o      = key_clear_q;
  assign data_out_clear_o = data_out_clear_q;

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid
  `ASSERT_KNOWN(AesCiphOpKnown, op_i)
  `ASSERT(AesKeyLenValid, key_len_i inside {
      AES_128,
      AES_192,
      AES_256
      })
  `ASSERT(AesControlStateValid, aes_cipher_ctrl_cs inside {
      IDLE,
      INIT,
      ROUND,
      FINISH,
      CLEAR
      })

endmodule
