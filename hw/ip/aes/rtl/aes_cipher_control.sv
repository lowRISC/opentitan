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

  // Signals
  logic                          [3:0] rnd_ctr_d, rnd_ctr_q;
  logic                          [3:0] rnd_ctr_rem_d, rnd_ctr_rem_q;
  logic                          [3:0] rnd_ctr_sum;
  logic                          [3:0] num_rounds_d, num_rounds_q;
  logic                                rnd_ctr_parity, rnd_ctr_parity_d, rnd_ctr_parity_q;
  logic                                rnd_ctr_err, rnd_ctr_err_sum, rnd_ctr_err_parity;
  sp2v_e                               crypt_d, crypt_q;
  sp2v_e                               dec_key_gen_d, dec_key_gen_q;
  logic                                key_clear_d, key_clear_q;
  logic                                data_out_clear_d, data_out_clear_q;
  sp2v_e                               sub_bytes_out_req;
  sp2v_e                               key_expand_out_req;
  sp2v_e                               in_valid;
  sp2v_e                               out_ready;
  sp2v_e                               crypt;
  sp2v_e                               dec_key_gen;
  logic                                mux_sel_err;
  logic                                mr_err;
  logic                                sp_enc_err;

  // Multi-rail signals. These are outputs of the single-rail FSMs and need combining.
  logic           [Sp2VWidth-1:0]      mr_alert;
  logic           [Sp2VWidth-1:0]      mr_prng_update;
  logic           [Sp2VWidth-1:0]      mr_prng_reseed_req;
  logic           [Sp2VWidth-1:0]      mr_key_expand_clear;
  logic           [Sp2VWidth-1:0]      mr_key_clear_d;
  logic           [Sp2VWidth-1:0]      mr_data_out_clear_d;

  state_sel_e     [Sp2VWidth-1:0]      mr_state_sel;
  add_rk_sel_e    [Sp2VWidth-1:0]      mr_add_rk_sel;
  key_full_sel_e  [Sp2VWidth-1:0]      mr_key_full_sel;
  key_dec_sel_e   [Sp2VWidth-1:0]      mr_key_dec_sel;
  key_words_sel_e [Sp2VWidth-1:0]      mr_key_words_sel;
  round_key_sel_e [Sp2VWidth-1:0]      mr_round_key_sel;

  logic           [Sp2VWidth-1:0][3:0] mr_rnd_ctr_d;
  logic           [Sp2VWidth-1:0][3:0] mr_rnd_ctr_rem_d;
  logic           [Sp2VWidth-1:0][3:0] mr_num_rounds_d;

  /////////
  // FSM //
  /////////
  // For every bit in the Sp2V signals, one separate rail is instantiated. The inputs and outputs
  // of every rail are buffered to prevent aggressive synthesis optimizations.
  for (genvar i = 0; i < Sp2VWidth; i++) begin : gen_fsm
    if (SP2V_HIGH[i] == 1'b1) begin : gen_fsm_p
      aes_cipher_control_fsm_p #(
        .Masking  ( Masking  ),
        .SBoxImpl ( SBoxImpl )
      ) u_aes_cipher_control_fsm_i (
        .clk_i                 ( clk_i                    ),
        .rst_ni                ( rst_ni                   ),

        .in_valid_i            ( in_valid[i]              ), // Sparsified
        .in_ready_o            ( in_ready_o[i]            ), // Sparsified

        .out_valid_o           ( out_valid_o[i]           ), // Sparsified
        .out_ready_i           ( out_ready[i]             ), // Sparsified

        .cfg_valid_i           ( cfg_valid_i              ),
        .op_i                  ( op_i                     ),
        .key_len_i             ( key_len_i                ),
        .crypt_i               ( crypt[i]                 ), // Sparsified
        .dec_key_gen_i         ( dec_key_gen[i]           ), // Sparsified
        .key_clear_i           ( key_clear_i              ),
        .data_out_clear_i      ( data_out_clear_i         ),
        .mux_sel_err_i         ( mux_sel_err              ),
        .sp_enc_err_i          ( sp_enc_err               ),
        .rnd_ctr_err_i         ( rnd_ctr_err              ),
        .alert_o               ( mr_alert[i]              ), // OR-combine

        .prng_update_o         ( mr_prng_update[i]        ), // OR-combine
        .prng_reseed_req_o     ( mr_prng_reseed_req[i]    ), // OR-combine
        .prng_reseed_ack_i     ( prng_reseed_ack_i        ),

        .state_sel_o           ( mr_state_sel[i]          ), // OR-combine
        .state_we_o            ( state_we_o[i]            ), // Sparsified
        .sub_bytes_en_o        ( sub_bytes_en_o[i]        ), // Sparsified
        .sub_bytes_out_req_i   ( sub_bytes_out_req[i]     ), // Sparsified
        .sub_bytes_out_ack_o   ( sub_bytes_out_ack_o[i]   ), // Sparsified
        .add_rk_sel_o          ( mr_add_rk_sel[i]         ), // OR-combine

        .key_full_sel_o        ( mr_key_full_sel[i]       ), // OR-combine
        .key_full_we_o         ( key_full_we_o[i]         ), // Sparsified
        .key_dec_sel_o         ( mr_key_dec_sel[i]        ), // OR-combine
        .key_dec_we_o          ( key_dec_we_o[i]          ), // Sparsified
        .key_expand_en_o       ( key_expand_en_o[i]       ), // Sparsified
        .key_expand_out_req_i  ( key_expand_out_req[i]    ), // Sparsified
        .key_expand_out_ack_o  ( key_expand_out_ack_o[i]  ), // Sparsified
        .key_expand_clear_o    ( mr_key_expand_clear[i]   ), // OR-combine
        .key_words_sel_o       ( mr_key_words_sel[i]      ), // OR-combine
        .round_key_sel_o       ( mr_round_key_sel[i]      ), // OR-combine

        .rnd_ctr_q_i           ( rnd_ctr_q                ),
        .rnd_ctr_d_o           ( mr_rnd_ctr_d[i]          ), // OR-combine
        .rnd_ctr_rem_q_i       ( rnd_ctr_rem_q            ),
        .rnd_ctr_rem_d_o       ( mr_rnd_ctr_rem_d[i]      ), // OR-combine
        .num_rounds_q_i        ( num_rounds_q             ),
        .num_rounds_d_o        ( mr_num_rounds_d[i]       ), // OR-combine
        .crypt_q_i             ( crypt_q[i]               ), // Sparsified
        .crypt_d_o             ( crypt_d[i]               ), // Sparsified
        .dec_key_gen_q_i       ( dec_key_gen_q[i]         ), // Sparsified
        .dec_key_gen_d_o       ( dec_key_gen_d[i]         ), // Sparsified
        .key_clear_q_i         ( key_clear_q              ),
        .key_clear_d_o         ( mr_key_clear_d[i]        ), // AND-combine
        .data_out_clear_q_i    ( data_out_clear_q         ),
        .data_out_clear_d_o    ( mr_data_out_clear_d[i]   )  // AND-combine
      );
    end else begin : gen_fsm_n
      aes_cipher_control_fsm_n #(
        .Masking  ( Masking  ),
        .SBoxImpl ( SBoxImpl )
      ) u_aes_cipher_control_fsm_i (
        .clk_i                 ( clk_i                    ),
        .rst_ni                ( rst_ni                   ),

        .in_valid_ni           ( in_valid[i]              ), // Sparsified
        .in_ready_no           ( in_ready_o[i]            ), // Sparsified

        .out_valid_no          ( out_valid_o[i]           ), // Sparsified
        .out_ready_ni          ( out_ready[i]             ), // Sparsified

        .cfg_valid_i           ( cfg_valid_i              ),
        .op_i                  ( op_i                     ),
        .key_len_i             ( key_len_i                ),
        .crypt_ni              ( crypt[i]                 ), // Sparsified
        .dec_key_gen_ni        ( dec_key_gen[i]           ), // Sparsified
        .key_clear_i           ( key_clear_i              ),
        .data_out_clear_i      ( data_out_clear_i         ),
        .mux_sel_err_i         ( mux_sel_err_i            ),
        .sp_enc_err_i          ( sp_enc_err               ),
        .rnd_ctr_err_i         ( rnd_ctr_err              ),
        .alert_o               ( mr_alert[i]              ), // OR-combine

        .prng_update_o         ( mr_prng_update[i]        ), // OR-combine
        .prng_reseed_req_o     ( mr_prng_reseed_req[i]    ), // OR-combine
        .prng_reseed_ack_i     ( prng_reseed_ack_i        ),

        .state_sel_o           ( mr_state_sel[i]          ), // OR-combine
        .state_we_no           ( state_we_o[i]            ), // Sparsified
        .sub_bytes_en_no       ( sub_bytes_en_o[i]        ), // Sparsified
        .sub_bytes_out_req_ni  ( sub_bytes_out_req[i]     ), // Sparsified
        .sub_bytes_out_ack_no  ( sub_bytes_out_ack_o[i]   ), // Sparsified
        .add_rk_sel_o          ( mr_add_rk_sel[i]         ), // OR-combine

        .key_full_sel_o        ( mr_key_full_sel[i]       ), // OR-combine
        .key_full_we_no        ( key_full_we_o[i]         ), // Sparsified
        .key_dec_sel_o         ( mr_key_dec_sel[i]        ), // OR-combine
        .key_dec_we_no         ( key_dec_we_o[i]          ), // Sparsified
        .key_expand_en_no      ( key_expand_en_o[i]       ), // Sparsified
        .key_expand_out_req_ni ( key_expand_out_req[i]    ), // Sparsified
        .key_expand_out_ack_no ( key_expand_out_ack_o[i]  ), // Sparsified
        .key_expand_clear_o    ( mr_key_expand_clear[i]   ), // OR-combine
        .key_words_sel_o       ( mr_key_words_sel[i]      ), // OR-combine
        .round_key_sel_o       ( mr_round_key_sel[i]      ), // OR-combine

        .rnd_ctr_q_i           ( rnd_ctr_q                ),
        .rnd_ctr_d_o           ( mr_rnd_ctr_d[i]          ), // OR-combine
        .rnd_ctr_rem_q_i       ( rnd_ctr_rem_q            ),
        .rnd_ctr_rem_d_o       ( mr_rnd_ctr_rem_d[i]      ), // OR-combine
        .num_rounds_q_i        ( num_rounds_q             ),
        .num_rounds_d_o        ( mr_num_rounds_d[i]       ), // OR-combine
        .crypt_q_ni            ( crypt_q[i]               ), // Sparsified
        .crypt_d_no            ( crypt_d[i]               ), // Sparsified
        .dec_key_gen_q_ni      ( dec_key_gen_q[i]         ), // Sparsified
        .dec_key_gen_d_no      ( dec_key_gen_d[i]         ), // Sparsified
        .key_clear_q_i         ( key_clear_q              ),
        .key_clear_d_o         ( mr_key_clear_d[i]        ), // AND-combine
        .data_out_clear_q_i    ( data_out_clear_q         ),
        .data_out_clear_d_o    ( mr_data_out_clear_d[i]   )  // AND-combine
      );
    end
  end

  // Combine single-bit FSM outputs.
  // OR: One bit is sufficient to drive the corresponding output bit high.
  assign alert_o            = |mr_alert;
  assign prng_update_o      = |mr_prng_update;
  assign prng_reseed_req_o  = |mr_prng_reseed_req;
  assign key_expand_clear_o = |mr_key_expand_clear;
  // AND: Only if all bits are high, the corresponding status is signaled which will lead to
  // the clearing of these trigger bits.
  assign key_clear_d        = &mr_key_clear_d;
  assign data_out_clear_d   = &mr_data_out_clear_d;

  // Combine multi-bit, sparse FSM outputs. We simply OR them together. If the FSMs don't provide
  // the same outputs, two cases are possible:
  // - An invalid encoding results: A downstream checker will fire, see mux_sel_err_i.
  // - A valid encoding results: The outputs are compared below to cover this case, see mr_err;
  always_comb begin : combine_sparse_signals
    state_sel_o     = state_sel_e'('0);
    add_rk_sel_o    = add_rk_sel_e'('0);
    key_full_sel_o  = key_full_sel_e'('0);
    key_dec_sel_o   = key_dec_sel_e'('0);
    key_words_sel_o = key_words_sel_e'('0);
    round_key_sel_o = round_key_sel_e'('0);
    mr_err          = 1'b0;

    for (int i = 0; i < Sp2VWidth; i++) begin
      state_sel_o     = state_sel_e'({state_sel_o}         | {mr_state_sel[i]});
      add_rk_sel_o    = add_rk_sel_e'({add_rk_sel_o}       | {mr_add_rk_sel[i]});
      key_full_sel_o  = key_full_sel_e'({key_full_sel_o}   | {mr_key_full_sel[i]});
      key_dec_sel_o   = key_dec_sel_e'({key_dec_sel_o}     | {mr_key_dec_sel[i]});
      key_words_sel_o = key_words_sel_e'({key_words_sel_o} | {mr_key_words_sel[i]});
      round_key_sel_o = round_key_sel_e'({round_key_sel_o} | {mr_round_key_sel[i]});

      if (state_sel_o     != mr_state_sel[i]     ||
          add_rk_sel_o    != mr_add_rk_sel[i]    ||
          key_full_sel_o  != mr_key_full_sel[i]  ||
          key_dec_sel_o   != mr_key_dec_sel[i]   ||
          key_words_sel_o != mr_key_words_sel[i] ||
          round_key_sel_o != mr_round_key_sel[i]) begin
        mr_err = 1'b1;
      end
    end
  end

  // Collect errors in mux selector signals.
  assign mux_sel_err = mux_sel_err_i | mr_err;

  // Combine counter signals. We simply OR them together. If the FSMs don't provide the same
  // outputs, this will be detected by the round counter protection logic below.
  always_comb begin : combine_counter_signals
    rnd_ctr_d     = '0;
    rnd_ctr_rem_d = '0;
    num_rounds_d  = '0;
    for (int i = 0; i < Sp2VWidth; i++) begin
      rnd_ctr_d     |= mr_rnd_ctr_d[i];
      rnd_ctr_rem_d |= mr_rnd_ctr_rem_d[i];
      num_rounds_d  |= mr_num_rounds_d[i];
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_fsm
    if (!rst_ni) begin
      key_clear_q        <= 1'b0;
      data_out_clear_q   <= 1'b0;
    end else begin
      key_clear_q        <= key_clear_d;
      data_out_clear_q   <= data_out_clear_d;
    end
  end

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
    .Width(4),
    .ResetValue('0)
  ) u_num_rounds_regs (
    .clk_i,
    .rst_ni,
    .d_i ( num_rounds_d ),
    .q_o ( num_rounds_q )
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
  localparam int unsigned NumSp2VSig = 8;
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
  assign sp2v_sig[6] = sub_bytes_out_req_i;
  assign sp2v_sig[7] = key_expand_out_req_i;

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
  assign sub_bytes_out_req  = sp2v_sig_chk[6];
  assign key_expand_out_req = sp2v_sig_chk[7];

  // Collect encoding errors.
  // We instantiate the checker modules as close as possible to where the sparsely encoded signals
  // are used. Here, we collect also encoding errors detected in other places of the cipher core.
  assign sp_enc_err = |sp2v_sig_err | sp_enc_err_i;

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid
  `ASSERT_KNOWN(AesCiphOpKnown, op_i)

endmodule
