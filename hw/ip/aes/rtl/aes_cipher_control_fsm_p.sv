// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES cipher core control FSM
//
// This module contains the AES cipher core control FSM operating on
// and producing the positive values of important control signals.

module aes_cipher_control_fsm_p import aes_pkg::*;
#(
  parameter bit         Masking  = 0,
  parameter sbox_impl_e SBoxImpl = SBoxImplLut
) (
  input  logic             clk_i,
  input  logic             rst_ni,

  // Input handshake signals
  input  logic             in_valid_i,            // Sparsify using multi-rail.
  output logic             in_ready_o,            // Sparsify using multi-rail.

  // Output handshake signals
  output logic             out_valid_o,           // Sparsify using multi-rail.
  input  logic             out_ready_i,           // Sparsify using multi-rail.

  // Control and sync signals
  input  logic             cfg_valid_i,           // Used for SVAs only.
  input  ciph_op_e         op_i,
  input  key_len_e         key_len_i,
  input  logic             crypt_i,               // Sparsify using multi-rail.
  input  logic             dec_key_gen_i,         // Sparsify using multi-rail.
  input  logic             key_clear_i,
  input  logic             data_out_clear_i,
  input  logic             mux_sel_err_i,
  input  logic             sp_enc_err_i,
  input  logic             rnd_ctr_err_i,
  output logic             alert_o,

  // Control signals for masking PRNG
  output logic             prng_update_o,
  output logic             prng_reseed_req_o,
  input  logic             prng_reseed_ack_i,

  // Control and sync signals for cipher data path
  output state_sel_e       state_sel_o,
  output logic             state_we_o,            // Sparsify using multi-rail.
  output logic             sub_bytes_en_o,        // Sparsify using multi-rail.
  input  logic             sub_bytes_out_req_i,   // Sparsify using multi-rail.
  output logic             sub_bytes_out_ack_o,   // Sparsify using multi-rail.
  output add_rk_sel_e      add_rk_sel_o,

  // Control and sync signals for key expand data path
  output key_full_sel_e    key_full_sel_o,
  output logic             key_full_we_o,         // Sparsify using multi-rail.
  output key_dec_sel_e     key_dec_sel_o,
  output logic             key_dec_we_o,          // Sparsify using multi-rail.
  output logic             key_expand_en_o,       // Sparsify using multi-rail.
  input  logic             key_expand_out_req_i,  // Sparsify using multi-rail.
  output logic             key_expand_out_ack_o,  // Sparsify using multi-rail.
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
  input  logic             crypt_q_i,             // Sparsify using multi-rail.
  output logic             crypt_d_o,             // Sparsify using multi-rail.
  input  logic             dec_key_gen_q_i,       // Sparsify using multi-rail.
  output logic             dec_key_gen_d_o,       // Sparsify using multi-rail.
  input  logic             key_clear_q_i,
  output logic             key_clear_d_o,
  input  logic             data_out_clear_q_i,
  output logic             data_out_clear_d_o
);

  /////////////////////
  // Input Buffering //
  /////////////////////

  localparam int NumInBufBits = $bits({
    in_valid_i,
    out_ready_i,
    cfg_valid_i,
    op_i,
    key_len_i,
    crypt_i,
    dec_key_gen_i,
    key_clear_i,
    data_out_clear_i,
    mux_sel_err_i,
    sp_enc_err_i,
    rnd_ctr_err_i,
    prng_reseed_ack_i,
    sub_bytes_out_req_i,
    key_expand_out_req_i,
    rnd_ctr_q_i,
    rnd_ctr_rem_q_i,
    num_rounds_q_i,
    crypt_q_i,
    dec_key_gen_q_i,
    key_clear_q_i,
    data_out_clear_q_i
  });

  logic [NumInBufBits-1:0] in, in_buf;

  assign in = {
    in_valid_i,
    out_ready_i,
    cfg_valid_i,
    op_i,
    key_len_i,
    crypt_i,
    dec_key_gen_i,
    key_clear_i,
    data_out_clear_i,
    mux_sel_err_i,
    sp_enc_err_i,
    rnd_ctr_err_i,
    prng_reseed_ack_i,
    sub_bytes_out_req_i,
    key_expand_out_req_i,
    rnd_ctr_q_i,
    rnd_ctr_rem_q_i,
    num_rounds_q_i,
    crypt_q_i,
    dec_key_gen_q_i,
    key_clear_q_i,
    data_out_clear_q_i
  };

  // This primitive is used to place a size-only constraint on the
  // buffers to act as a synthesis optimization barrier.
  prim_buf #(
    .Width(NumInBufBits)
  ) u_prim_buf_in (
    .in_i(in),
    .out_o(in_buf)
  );

  logic             in_valid;
  logic             out_ready;
  logic             cfg_valid;
  logic             op;
  key_len_e         key_len;
  logic             crypt;
  logic             dec_key_gen;
  logic             key_clear;
  logic             data_out_clear;
  logic             mux_sel_err;
  logic             sp_enc_err;
  logic             rnd_ctr_err;
  logic             prng_reseed_ack;
  logic             sub_bytes_out_req;
  logic             key_expand_out_req;
  logic [3:0]       rnd_ctr_q;
  logic [3:0]       rnd_ctr_rem_q;
  logic [3:0]       num_rounds_q;
  logic             crypt_q;
  logic             dec_key_gen_q;
  logic             key_clear_q;
  logic             data_out_clear_q;

  assign {in_valid,
          out_ready,
          cfg_valid,
          op,
          key_len,
          crypt,
          dec_key_gen,
          key_clear,
          data_out_clear,
          mux_sel_err,
          sp_enc_err,
          rnd_ctr_err,
          prng_reseed_ack,
          sub_bytes_out_req,
          key_expand_out_req,
          rnd_ctr_q,
          rnd_ctr_rem_q,
          num_rounds_q,
          crypt_q,
          dec_key_gen_q,
          key_clear_q,
          data_out_clear_q} = in_buf;

  // Intermediate output signals
  logic             in_ready;
  logic             out_valid;
  logic             alert;
  logic             prng_update;
  logic             prng_reseed_req;
  state_sel_e       state_sel;
  logic             state_we;
  logic             sub_bytes_en;
  logic             sub_bytes_out_ack;
  add_rk_sel_e      add_rk_sel;
  key_full_sel_e    key_full_sel;
  logic             key_full_we;
  key_dec_sel_e     key_dec_sel;
  logic             key_dec_we;
  logic             key_expand_en;
  logic             key_expand_out_ack;
  logic             key_expand_clear;
  key_words_sel_e   key_words_sel;
  round_key_sel_e   round_key_sel;
  logic [3:0]       rnd_ctr_d;
  logic [3:0]       rnd_ctr_rem_d;
  logic [3:0]       num_rounds_d;
  logic             crypt_d;
  logic             dec_key_gen_d;
  logic             key_clear_d;
  logic             data_out_clear_d;

  /////////////////
  // Regular FSM //
  /////////////////

  aes_cipher_control_fsm #(
    .Masking  ( Masking  ),
    .SBoxImpl ( SBoxImpl )
  ) u_aes_cipher_control_fsm (
    .clk_i                 ( clk_i                  ),
    .rst_ni                ( rst_ni                 ),

    .in_valid_i            ( in_valid               ),
    .in_ready_o            ( in_ready               ),

    .out_valid_o           ( out_valid              ),
    .out_ready_i           ( out_ready              ),

    .cfg_valid_i           ( cfg_valid              ),
    .op_i                  ( op                     ),
    .key_len_i             ( key_len                ),
    .crypt_i               ( crypt                  ),
    .dec_key_gen_i         ( dec_key_gen            ),
    .key_clear_i           ( key_clear              ),
    .data_out_clear_i      ( data_out_clear         ),
    .mux_sel_err_i         ( mux_sel_err            ),
    .sp_enc_err_i          ( sp_enc_err             ),
    .rnd_ctr_err_i         ( rnd_ctr_err            ),
    .alert_o               ( alert                  ),

    .prng_update_o         ( prng_update            ),
    .prng_reseed_req_o     ( prng_reseed_req        ),
    .prng_reseed_ack_i     ( prng_reseed_ack        ),

    .state_sel_o           ( state_sel              ),
    .state_we_o            ( state_we               ),
    .sub_bytes_en_o        ( sub_bytes_en           ),
    .sub_bytes_out_req_i   ( sub_bytes_out_req      ),
    .sub_bytes_out_ack_o   ( sub_bytes_out_ack      ),
    .add_rk_sel_o          ( add_rk_sel             ),

    .key_full_sel_o        ( key_full_sel           ),
    .key_full_we_o         ( key_full_we            ),
    .key_dec_sel_o         ( key_dec_sel            ),
    .key_dec_we_o          ( key_dec_we             ),
    .key_expand_en_o       ( key_expand_en          ),
    .key_expand_out_req_i  ( key_expand_out_req     ),
    .key_expand_out_ack_o  ( key_expand_out_ack     ),
    .key_expand_clear_o    ( key_expand_clear       ),
    .key_words_sel_o       ( key_words_sel          ),
    .round_key_sel_o       ( round_key_sel          ),

    .rnd_ctr_q_i           ( rnd_ctr_q              ),
    .rnd_ctr_d_o           ( rnd_ctr_d              ),
    .rnd_ctr_rem_q_i       ( rnd_ctr_rem_q          ),
    .rnd_ctr_rem_d_o       ( rnd_ctr_rem_d          ),
    .num_rounds_q_i        ( num_rounds_q           ),
    .num_rounds_d_o        ( num_rounds_d           ),
    .crypt_q_i             ( crypt_q                ),
    .crypt_d_o             ( crypt_d                ),
    .dec_key_gen_q_i       ( dec_key_gen_q          ),
    .dec_key_gen_d_o       ( dec_key_gen_d          ),
    .key_clear_q_i         ( key_clear_q            ),
    .key_clear_d_o         ( key_clear_d            ),
    .data_out_clear_q_i    ( data_out_clear_q       ),
    .data_out_clear_d_o    ( data_out_clear_d       )
  );

  //////////////////////
  // Output Buffering //
  //////////////////////

  localparam int NumOutBufBits = $bits({
    in_ready_o,
    out_valid_o,
    alert_o,
    prng_update_o,
    prng_reseed_req_o,
    state_sel_o,
    state_we_o,
    sub_bytes_en_o,
    sub_bytes_out_ack_o,
    add_rk_sel_o,
    key_full_sel_o,
    key_full_we_o,
    key_dec_sel_o,
    key_dec_we_o,
    key_expand_en_o,
    key_expand_out_ack_o,
    key_expand_clear_o,
    key_words_sel_o,
    round_key_sel_o,
    rnd_ctr_d_o,
    rnd_ctr_rem_d_o,
    num_rounds_d_o,
    crypt_d_o,
    dec_key_gen_d_o,
    key_clear_d_o,
    data_out_clear_d_o
  });

  logic [NumOutBufBits-1:0] out, out_buf;

  assign out = {
    in_ready,
    out_valid,
    alert,
    prng_update,
    prng_reseed_req,
    state_sel,
    state_we,
    sub_bytes_en,
    sub_bytes_out_ack,
    add_rk_sel,
    key_full_sel,
    key_full_we,
    key_dec_sel,
    key_dec_we,
    key_expand_en,
    key_expand_out_ack,
    key_expand_clear,
    key_words_sel,
    round_key_sel,
    rnd_ctr_d,
    rnd_ctr_rem_d,
    num_rounds_d,
    crypt_d,
    dec_key_gen_d,
    key_clear_d,
    data_out_clear_d
  };

  // This primitive is used to place a size-only constraint on the
  // buffers to act as a synthesis optimization barrier.
  prim_buf #(
    .Width(NumOutBufBits)
  ) u_prim_buf_out (
    .in_i(out),
    .out_o(out_buf)
  );

  assign {in_ready_o,
          out_valid_o,
          alert_o,
          prng_update_o,
          prng_reseed_req_o,
          state_sel_o,
          state_we_o,
          sub_bytes_en_o,
          sub_bytes_out_ack_o,
          add_rk_sel_o,
          key_full_sel_o,
          key_full_we_o,
          key_dec_sel_o,
          key_dec_we_o,
          key_expand_en_o,
          key_expand_out_ack_o,
          key_expand_clear_o,
          key_words_sel_o,
          round_key_sel_o,
          rnd_ctr_d_o,
          rnd_ctr_rem_d_o,
          num_rounds_d_o,
          crypt_d_o,
          dec_key_gen_d_o,
          key_clear_d_o,
          data_out_clear_d_o} = out_buf;

endmodule
