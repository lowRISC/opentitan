// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES cipher core control
//
// This module controls the AES cipher core including the key expand module.

`include "prim_assert.sv"

module aes_cipher_control import aes_pkg::*;
#(
  parameter bit         Masking  = 0,
  parameter sbox_impl_e SBoxImpl = SBoxImplLut
) (
  input  logic                    clk_i,
  input  logic                    rst_ni,

  // Input handshake signals
  input  sp2v_e                   in_valid_i,
  output sp2v_e                   in_ready_o,

  // Output handshake signals
  output sp2v_e                   out_valid_o,
  input  sp2v_e                   out_ready_i,

  // Control and sync signals
  input  logic                    cfg_valid_i,
  input  ciph_op_e                op_i,
  input  key_len_e                key_len_i,
  input  sp2v_e                   crypt_i,
  output sp2v_e                   crypt_o,
  input  sp2v_e                   dec_key_gen_i,
  output sp2v_e                   dec_key_gen_o,
  input  logic                    key_clear_i,
  output logic                    key_clear_o,
  input  logic                    data_out_clear_i,
  output logic                    data_out_clear_o,
  input  logic                    mux_sel_err_i,
  input  logic                    sp_enc_err_i,
  output logic                    alert_o,

  // Control signals for masking PRNG
  output logic                    prng_update_o,
  output logic                    prng_reseed_req_o,
  input  logic                    prng_reseed_ack_i,

  // Control and sync signals for cipher data path
  output state_sel_e              state_sel_o,
  output sp2v_e                   state_we_o,
  output sp2v_e                   sub_bytes_en_o,
  input  sp2v_e                   sub_bytes_out_req_i,
  output sp2v_e                   sub_bytes_out_ack_o,
  output add_rk_sel_e             add_rk_sel_o,

  // Control and sync signals for key expand data path
  output ciph_op_e                key_expand_op_o,
  output key_full_sel_e           key_full_sel_o,
  output sp2v_e                   key_full_we_o,
  output key_dec_sel_e            key_dec_sel_o,
  output sp2v_e                   key_dec_we_o,
  output sp2v_e                   key_expand_en_o,
  input  sp2v_e                   key_expand_out_req_i,
  output sp2v_e                   key_expand_out_ack_o,
  output logic                    key_expand_clear_o,
  output logic [3:0]              key_expand_round_o,
  output key_words_sel_e          key_words_sel_o,
  output round_key_sel_e          round_key_sel_o
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

  aes_cipher_ctrl_e aes_cipher_ctrl_ns, aes_cipher_ctrl_cs;

  // Signals
  logic [3:0] rnd_ctr_d, rnd_ctr_q;
  logic [3:0] rnd_ctr_rem_d, rnd_ctr_rem_q;
  logic [3:0] rnd_ctr_sum;
  logic [3:0] num_rounds_d, num_rounds_q;
  logic [3:0] num_rounds_regular;
  logic       rnd_ctr_parity, rnd_ctr_parity_d, rnd_ctr_parity_q;
  logic       rnd_ctr_err, rnd_ctr_err_sum, rnd_ctr_err_parity;
  sp2v_e      crypt_d, crypt_q;
  sp2v_e      dec_key_gen_d, dec_key_gen_q;
  logic       key_clear_d, key_clear_q;
  logic       data_out_clear_d, data_out_clear_q;
  logic       prng_reseed_done_d, prng_reseed_done_q;
  sp2v_e      sub_bytes_out_req;
  sp2v_e      key_expand_out_req;
  sp2v_e      advance, advance_chk;
  sp2v_e      in_valid;
  sp2v_e      out_ready;
  sp2v_e      crypt;
  sp2v_e      dec_key_gen;
  logic       sp_enc_err;

  // cfg_valid_i is used for gating assertions only.
  logic       unused_cfg_valid;
  assign unused_cfg_valid = cfg_valid_i;

  // FSM
  always_comb begin : aes_cipher_ctrl_fsm

    // Handshake signals
    in_ready_o           = SP2V_LOW;
    out_valid_o          = SP2V_LOW;

    // Masking PRNG signals
    prng_update_o        = 1'b0;
    prng_reseed_req_o    = 1'b0;

    // Cipher data path
    state_sel_o          = STATE_ROUND;
    state_we_o           = SP2V_LOW;
    add_rk_sel_o         = ADD_RK_ROUND;
    sub_bytes_en_o       = SP2V_LOW;
    sub_bytes_out_ack_o  = SP2V_LOW;

    // Key expand data path
    key_full_sel_o       = KEY_FULL_ROUND;
    key_full_we_o        = SP2V_LOW;
    key_dec_sel_o        = KEY_DEC_EXPAND;
    key_dec_we_o         = SP2V_LOW;
    key_expand_en_o      = SP2V_LOW;
    key_expand_out_ack_o = SP2V_LOW;
    key_expand_clear_o   = 1'b0;
    key_words_sel_o      = KEY_WORDS_ZERO;
    round_key_sel_o      = ROUND_KEY_DIRECT;

    // FSM
    aes_cipher_ctrl_ns   = aes_cipher_ctrl_cs;
    num_rounds_d         = num_rounds_q;
    rnd_ctr_d            = rnd_ctr_q;
    rnd_ctr_rem_d        = rnd_ctr_rem_q;
    crypt_d              = crypt_q;
    dec_key_gen_d        = dec_key_gen_q;
    key_clear_d          = key_clear_q;
    data_out_clear_d     = data_out_clear_q;
    prng_reseed_done_d   = prng_reseed_done_q | prng_reseed_ack_i;
    advance              = SP2V_LOW;

    // Alert
    alert_o              = 1'b0;

    unique case (aes_cipher_ctrl_cs)

      IDLE: begin
        dec_key_gen_d = SP2V_LOW;

        // Signal that we are ready, wait for handshake.
        in_ready_o = SP2V_HIGH;
        if (in_valid == SP2V_HIGH) begin
          if (key_clear_i || data_out_clear_i) begin
            // Clear internal key registers. The cipher core muxes are used to clear the data
            // output registers.
            key_clear_d      = key_clear_i;
            data_out_clear_d = data_out_clear_i;

            // To clear the data output registers, we must first clear the state.
            aes_cipher_ctrl_ns = data_out_clear_i ? CLEAR_S : CLEAR_KD;

          end else if (dec_key_gen == SP2V_HIGH || crypt == SP2V_HIGH) begin
            // Start encryption/decryption or generation of start key for decryption.
            crypt_d       = (dec_key_gen_i == SP2V_LOW) ? crypt : SP2V_LOW;
            dec_key_gen_d =  dec_key_gen_i;

            // Load input data to state
            state_sel_o = (dec_key_gen_i == SP2V_HIGH) ? STATE_CLEAR : STATE_INIT;
            state_we_o  = SP2V_HIGH;

            // Make the masking PRNG advance. The current pseudo-random data is used to mask the
            // input data.
            prng_update_o = (dec_key_gen_i == SP2V_HIGH) ? 1'b0 : Masking;

            // Init key expand
            key_expand_clear_o = 1'b1;

            // Load full key
            key_full_sel_o = (dec_key_gen_i == SP2V_HIGH) ? KEY_FULL_ENC_INIT :
                                       (op_i == CIPH_FWD) ? KEY_FULL_ENC_INIT :
                                                            KEY_FULL_DEC_INIT;
            key_full_we_o  = SP2V_HIGH;

            // Load num_rounds, initialize round counters.
            num_rounds_d = (key_len_i == AES_128) ? 4'd10 :
                           (key_len_i == AES_192) ? 4'd12 :
                                                    4'd14;
            rnd_ctr_rem_d      = num_rounds_d;
            rnd_ctr_d          = '0;
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
        key_words_sel_o = (dec_key_gen_q == SP2V_HIGH) ? KEY_WORDS_ZERO :
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
          advance         = key_expand_out_req;
          prng_update_o   = (SBoxImpl == SBoxImplDom) ? (advance_chk == SP2V_LOW) : Masking;
          key_expand_en_o = SP2V_HIGH;
          if (advance_chk == SP2V_HIGH) begin
            key_expand_out_ack_o = SP2V_HIGH;
            state_we_o           = (dec_key_gen_q == SP2V_LOW) ? SP2V_HIGH : SP2V_LOW;
            key_full_we_o        = SP2V_HIGH;
            rnd_ctr_d            = rnd_ctr_q     + 4'b0001;
            rnd_ctr_rem_d        = rnd_ctr_rem_q - 4'b0001;
            aes_cipher_ctrl_ns   = ROUND;
          end
        end else begin
          state_we_o         = (dec_key_gen_q == SP2V_LOW) ? SP2V_HIGH : SP2V_LOW;
          rnd_ctr_d          = rnd_ctr_q     + 4'b0001;
          rnd_ctr_rem_d      = rnd_ctr_rem_q - 4'b0001;
          aes_cipher_ctrl_ns = ROUND;
        end
      end

      ROUND: begin
        // Normal rounds

        // Select key words for add_round_key
        key_words_sel_o = (dec_key_gen_q == SP2V_HIGH) ? KEY_WORDS_ZERO :
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
        advance         = ((dec_key_gen_q == SP2V_HIGH || sub_bytes_out_req == SP2V_HIGH) &&
            key_expand_out_req == SP2V_HIGH) ? SP2V_HIGH : SP2V_LOW;
        prng_update_o   = (SBoxImpl == SBoxImplDom) ? (advance_chk == SP2V_LOW) : Masking;
        sub_bytes_en_o  = (dec_key_gen_q == SP2V_LOW) ? SP2V_HIGH : SP2V_LOW;
        key_expand_en_o = SP2V_HIGH;
        if (advance_chk == SP2V_HIGH) begin
          sub_bytes_out_ack_o  = (dec_key_gen_q == SP2V_LOW) ? SP2V_HIGH : SP2V_LOW;
          key_expand_out_ack_o = SP2V_HIGH;

          state_we_o    = (dec_key_gen_q == SP2V_LOW) ? SP2V_HIGH : SP2V_LOW;
          key_full_we_o = SP2V_HIGH;

          // Update round
          rnd_ctr_d     = rnd_ctr_q     + 4'b0001;
          rnd_ctr_rem_d = rnd_ctr_rem_q - 4'b0001;

          // Are we doing the last regular round?
          if (rnd_ctr_q == num_rounds_regular) begin
            aes_cipher_ctrl_ns = FINISH;

            if (dec_key_gen_q == SP2V_HIGH) begin
              // Write decryption key.
              key_dec_we_o = SP2V_HIGH;

              // Indicate that we are done, try to perform the handshake. But we don't wait here.
              // If we don't get the handshake now, we will wait in the finish state. When using
              // masking, we only finish if the masking PRNG has been reseeded.
              out_valid_o = Masking ? (prng_reseed_done_q ? SP2V_HIGH : SP2V_LOW) : SP2V_HIGH;
              if (out_valid_o == SP2V_HIGH && out_ready == SP2V_HIGH) begin
                // Go to idle state directly.
                dec_key_gen_d      = SP2V_LOW;
                aes_cipher_ctrl_ns = IDLE;
              end
            end
          end // rnd_ctr_q
        end // SubBytes/KeyExpand REQ/ACK
      end

      FINISH: begin
        // Final round

        // Select key words for add_round_key
        key_words_sel_o = (dec_key_gen_q == SP2V_HIGH) ? KEY_WORDS_ZERO :
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
        advance = (sub_bytes_out_req == SP2V_HIGH ||
                          dec_key_gen_q == SP2V_HIGH) ? SP2V_HIGH : SP2V_LOW;
        sub_bytes_en_o = (dec_key_gen_q == SP2V_LOW)  ? SP2V_HIGH : SP2V_LOW;
        out_valid_o = (advance_chk == SP2V_HIGH &&
            Masking == prng_reseed_done_q &&
                       !mux_sel_err_i && !sp_enc_err) ? SP2V_HIGH : SP2V_LOW;
        // When using DOM S-Boxes, make the masking PRNG advance every cycle until the output is
        // ready. For other S-Boxes, make it advance once only. Updating it while being stalled
        // would cause non-DOM S-Boxes to be re-evaluated, thereby creating additional SCA leakage.
        prng_update_o = (SBoxImpl == SBoxImplDom) ? (advance_chk == SP2V_LOW) :
            Masking ? (out_valid_o == SP2V_HIGH && out_ready == SP2V_HIGH)    : 1'b0;
        if (out_valid_o == SP2V_HIGH && out_ready == SP2V_HIGH) begin
          sub_bytes_out_ack_o = (dec_key_gen_q == SP2V_LOW) ? SP2V_HIGH : SP2V_LOW;

          // Clear the state.
          state_we_o          = SP2V_HIGH;
          crypt_d             = SP2V_LOW;
          // If we were generating the decryption key and didn't get the handshake in the last
          // regular round, we should clear dec_key_gen now.
          dec_key_gen_d       = SP2V_LOW;
          aes_cipher_ctrl_ns  = IDLE;
        end
      end

      CLEAR_S: begin
        // Clear the state with pseudo-random data.
        state_we_o         = SP2V_HIGH;
        state_sel_o        = STATE_CLEAR;
        aes_cipher_ctrl_ns = CLEAR_KD;
      end

      CLEAR_KD: begin
        // Clear internal key registers and/or external data output registers.
        if (key_clear_q) begin
          key_full_sel_o = KEY_FULL_CLEAR;
          key_full_we_o  = SP2V_HIGH;
          key_dec_sel_o  = KEY_DEC_CLEAR;
          key_dec_we_o   = SP2V_HIGH;
        end
        if (data_out_clear_q) begin
          // Forward the state (previously cleared with psuedo-random data).
          add_rk_sel_o    = ADD_RK_INIT;
          key_words_sel_o = KEY_WORDS_ZERO;
          round_key_sel_o = ROUND_KEY_DIRECT;
        end
        // Indicate that we are done, wait for handshake.
        out_valid_o = SP2V_HIGH;
        if (out_ready == SP2V_HIGH) begin
          key_clear_d        = 1'b0;
          data_out_clear_d   = 1'b0;
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
    if (mux_sel_err_i || sp_enc_err || rnd_ctr_err) begin
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
      num_rounds_q       <= '0;
      key_clear_q        <= 1'b0;
      data_out_clear_q   <= 1'b0;
      prng_reseed_done_q <= 1'b0;
    end else begin
      num_rounds_q       <= num_rounds_d;
      key_clear_q        <= key_clear_d;
      data_out_clear_q   <= data_out_clear_d;
      prng_reseed_done_q <= prng_reseed_done_d;
    end
  end

  // Use separate signal for number of regular rounds.
  assign num_rounds_regular = num_rounds_q - 4'd1;

  // Use separate signal for key expand operation, forward round.
  assign key_expand_op_o    = (dec_key_gen_d == SP2V_HIGH ||
                               dec_key_gen_q == SP2V_HIGH) ? CIPH_FWD : op_i;
  assign key_expand_round_o = rnd_ctr_q;

  // Let the main controller know whate we are doing.
  assign crypt_o          = crypt_q;
  assign dec_key_gen_o    = dec_key_gen_q;
  assign key_clear_o      = key_clear_q;
  assign data_out_clear_o = data_out_clear_q;

  //////////////////////////////
  // Round Counter Protection //
  //////////////////////////////
  // To protect the round counter against fault injection, we use two counters:
  // - rnd_ctr_d/q counts the executed rounds. It is initialized to 0 and counts up.
  // - rnd_ctr_rem_d/q counts the remaining rounds. It is initialized to num_rounds_q and counts
  //   down.
  // In addition, we use one parity bit for the rnd_ctr_d/q counter.
  //
  // An alert is signaled and the FSM goes into the terminal error state if
  // i) the sum of the counters doesn't add up, i.e. rnd_ctr_q + rnd_ctr_rem_q != num_rounds_q, or
  // ii) the parity information is incorrect.

  // The following primitives are used to place size-only constraints on the
  // flops in order to prevent optimizations on the protected round counter.
  prim_flop #(
    .Width(4),
    .ResetValue('0)
  ) u_rnd_ctr_regs (
    .clk_i,
    .rst_ni,
    .d_i ( rnd_ctr_d ),
    .q_o ( rnd_ctr_q )
  );

  prim_flop #(
    .Width(4),
    .ResetValue('0)
  ) u_rnd_ctr_rem_regs (
    .clk_i,
    .rst_ni,
    .d_i ( rnd_ctr_rem_d ),
    .q_o ( rnd_ctr_rem_q )
  );

  prim_flop #(
    .Width(1),
    .ResetValue('0)
  ) u_rnd_ctr_par_reg (
    .clk_i,
    .rst_ni,
    .d_i ( rnd_ctr_parity_d ),
    .q_o ( rnd_ctr_parity_q )
  );

  // Generate parity bits and sum.
  assign rnd_ctr_parity_d = ^rnd_ctr_d;
  assign rnd_ctr_parity   = ^rnd_ctr_q;
  assign rnd_ctr_sum      = rnd_ctr_q + rnd_ctr_rem_q;

  // Detect faults.
  assign rnd_ctr_err_sum    = (rnd_ctr_sum != num_rounds_q)        ? 1'b1 : 1'b0;
  assign rnd_ctr_err_parity = (rnd_ctr_parity != rnd_ctr_parity_q) ? 1'b1 : 1'b0;

  assign rnd_ctr_err = rnd_ctr_err_sum | rnd_ctr_err_parity;

  //////////////////////////////
  // Sparsely Encoded Signals //
  //////////////////////////////

  // We use sparse encodings for various critical signals and must ensure that:
  // 1. The synthesis tool doesn't optimize away the sparse encoding.
  // 2. The sparsely encoded signal is always valid. More precisely, an alert or SVA is triggered
  //    if a sparse signal takes on an invalid value.
  // 3. The alert signal remains asserted until reset even if the sparse signal becomes valid again
  //    This is achieved by driving the control FSM into the terminal error state whenever any
  //    sparsely encoded signal becomes invalid.
  //
  // If any sparsely encoded signal becomes invalid, the cipher core further immediately de-asserts
  // the out_valid_o signal to prevent any data from being released.

  // The following primitives are used to place a size-only constraint on the
  // flops in order to prevent optimizations on these status signals.
  logic [Sp2VWidth-1:0] crypt_q_raw;
  prim_flop #(
    .Width      ( Sp2VWidth            ),
    .ResetValue ( Sp2VWidth'(SP2V_LOW) )
  ) u_crypt_regs (
    .clk_i  ( clk_i       ),
    .rst_ni ( rst_ni      ),
    .d_i    ( crypt_d     ),
    .q_o    ( crypt_q_raw )
  );

  logic [Sp2VWidth-1:0] dec_key_gen_q_raw;
  prim_flop #(
    .Width      ( Sp2VWidth            ),
    .ResetValue ( Sp2VWidth'(SP2V_LOW) )
  ) u_dec_key_gen_regs (
    .clk_i  ( clk_i             ),
    .rst_ni ( rst_ni            ),
    .d_i    ( dec_key_gen_d     ),
    .q_o    ( dec_key_gen_q_raw )
  );

  // We use vectors of sparsely encoded signals to reduce code duplication.
  localparam int unsigned NumSp2VSig = 9;
  sp2v_e [NumSp2VSig-1:0]                sp2v_sig;
  sp2v_e [NumSp2VSig-1:0]                sp2v_sig_chk;
  logic  [NumSp2VSig-1:0][Sp2VWidth-1:0] sp2v_sig_chk_raw;
  logic  [NumSp2VSig-1:0]                sp2v_sig_err;

  assign sp2v_sig[0] = in_valid_i;
  assign sp2v_sig[1] = out_ready_i;
  assign sp2v_sig[2] = crypt_i;
  assign sp2v_sig[3] = dec_key_gen_i;
  assign sp2v_sig[4] = sp2v_e'(crypt_q_raw);
  assign sp2v_sig[5] = sp2v_e'(dec_key_gen_q_raw);
  assign sp2v_sig[6] = advance;
  assign sp2v_sig[7] = sub_bytes_out_req_i;
  assign sp2v_sig[8] = key_expand_out_req_i;

  // Individually check sparsely encoded signals.
  for (genvar i = 0; i < NumSp2VSig; i++) begin : gen_sel_buf_chk
    aes_sel_buf_chk #(
      .Num   ( Sp2VNum   ),
      .Width ( Sp2VWidth )
    ) u_aes_sp2v_sig_buf_chk_i (
      .clk_i  ( clk_i               ),
      .rst_ni ( rst_ni              ),
      .sel_i  ( sp2v_sig[i]         ),
      .sel_o  ( sp2v_sig_chk_raw[i] ),
      .err_o  ( sp2v_sig_err[i]     )
    );
    assign sp2v_sig_chk[i] = sp2v_e'(sp2v_sig_chk_raw[i]);
  end

  assign in_valid           = sp2v_sig_chk[0];
  assign out_ready          = sp2v_sig_chk[1];
  assign crypt              = sp2v_sig_chk[2];
  assign dec_key_gen        = sp2v_sig_chk[3];
  assign crypt_q            = sp2v_sig_chk[4];
  assign dec_key_gen_q      = sp2v_sig_chk[5];
  assign advance_chk        = sp2v_sig_chk[6];
  assign sub_bytes_out_req  = sp2v_sig_chk[7];
  assign key_expand_out_req = sp2v_sig_chk[8];

  // Collect encoding errors.
  // We instantiate the checker modules as close as possible to where the sparsely encoded signals
  // are used. Here, we collect also encoding errors detected in other places of the cipher core.
  assign sp_enc_err = |sp2v_sig_err | sp_enc_err_i;

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
