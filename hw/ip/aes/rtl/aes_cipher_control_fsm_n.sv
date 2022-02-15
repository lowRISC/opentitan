// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES cipher core control FSM
//
// This module contains the AES cipher core control FSM operating on and producing the negated
// values of important control signals. This is achieved by:
// - instantiating the regular AES cipher core control FSM operating on and producing the positive
//   values of these signals, and
// - inverting these signals between the regular FSM and the prim_buf synthesis barriers.
// Synthesis tools will then push the inverters into the actual FSM.

module aes_cipher_control_fsm_n import aes_pkg::*;
#(
  parameter bit         SecMasking  = 0,
  parameter sbox_impl_e SecSBoxImpl = SBoxImplDom
) (
  input  logic             clk_i,
  input  logic             rst_ni,

  // Input handshake signals
  input  logic             in_valid_ni,           // Sparsify using multi-rail.
  output logic             in_ready_no,           // Sparsify using multi-rail.

  // Output handshake signals
  output logic             out_valid_no,          // Sparsify using multi-rail.
  input  logic             out_ready_ni,          // Sparsify using multi-rail.

  // Control and sync signals
  input  logic             cfg_valid_i,           // Used for SVAs only.
  input  ciph_op_e         op_i,
  input  key_len_e         key_len_i,
  input  logic             crypt_ni,              // Sparsify using multi-rail.
  input  logic             dec_key_gen_ni,        // Sparsify using multi-rail.
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
  output logic             state_we_no,           // Sparsify using multi-rail.
  output logic             sub_bytes_en_no,       // Sparsify using multi-rail.
  input  logic             sub_bytes_out_req_ni,  // Sparsify using multi-rail.
  output logic             sub_bytes_out_ack_no,  // Sparsify using multi-rail.
  output add_rk_sel_e      add_rk_sel_o,

  // Control and sync signals for key expand data path
  output key_full_sel_e    key_full_sel_o,
  output logic             key_full_we_no,        // Sparsify using multi-rail.
  output key_dec_sel_e     key_dec_sel_o,
  output logic             key_dec_we_no,         // Sparsify using multi-rail.
  output logic             key_expand_en_no,      // Sparsify using multi-rail.
  input  logic             key_expand_out_req_ni, // Sparsify using multi-rail.
  output logic             key_expand_out_ack_no, // Sparsify using multi-rail.
  output logic             key_expand_clear_o,
  output logic [3:0]       rnd_ctr_o,
  output key_words_sel_e   key_words_sel_o,
  output round_key_sel_e   round_key_sel_o,

  // Register signals
  input  logic             crypt_q_ni,            // Sparsify using multi-rail.
  output logic             crypt_d_no,            // Sparsify using multi-rail.
  input  logic             dec_key_gen_q_ni,      // Sparsify using multi-rail.
  output logic             dec_key_gen_d_no,      // Sparsify using multi-rail.
  input  logic             prng_reseed_q_i,
  output logic             prng_reseed_d_o,
  input  logic             key_clear_q_i,
  output logic             key_clear_d_o,
  input  logic             data_out_clear_q_i,
  output logic             data_out_clear_d_o
);

  /////////////////////
  // Input Buffering //
  /////////////////////

  localparam int NumInBufBits = $bits({
    in_valid_ni,
    out_ready_ni,
    cfg_valid_i,
    op_i,
    key_len_i,
    crypt_ni,
    dec_key_gen_ni,
    prng_reseed_i,
    key_clear_i,
    data_out_clear_i,
    mux_sel_err_i,
    sp_enc_err_i,
    rnd_ctr_err_i,
    op_err_i,
    alert_fatal_i,
    prng_reseed_ack_i,
    sub_bytes_out_req_ni,
    key_expand_out_req_ni,
    crypt_q_ni,
    dec_key_gen_q_ni,
    prng_reseed_q_i,
    key_clear_q_i,
    data_out_clear_q_i
  });

  logic [NumInBufBits-1:0] in, in_buf;

  assign in = {
    in_valid_ni,
    out_ready_ni,
    cfg_valid_i,
    op_i,
    key_len_i,
    crypt_ni,
    dec_key_gen_ni,
    prng_reseed_i,
    key_clear_i,
    data_out_clear_i,
    mux_sel_err_i,
    sp_enc_err_i,
    rnd_ctr_err_i,
    op_err_i,
    alert_fatal_i,
    prng_reseed_ack_i,
    sub_bytes_out_req_ni,
    key_expand_out_req_ni,
    crypt_q_ni,
    dec_key_gen_q_ni,
    prng_reseed_q_i,
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

  logic                 in_valid_n;
  logic                 out_ready_n;
  logic                 cfg_valid;
  ciph_op_e             op;
  logic [$bits(op)-1:0] op_raw;
  key_len_e             key_len;
  logic                 crypt_n;
  logic                 dec_key_gen_n;
  logic                 prng_reseed;
  logic                 key_clear;
  logic                 data_out_clear;
  logic                 mux_sel_err;
  logic                 sp_enc_err;
  logic                 rnd_ctr_err;
  logic                 op_err;
  logic                 alert_fatal;
  logic                 prng_reseed_ack;
  logic                 sub_bytes_out_req_n;
  logic                 key_expand_out_req_n;
  logic                 crypt_q_n;
  logic                 dec_key_gen_q_n;
  logic                 prng_reseed_q;
  logic                 key_clear_q;
  logic                 data_out_clear_q;

  assign {in_valid_n,
          out_ready_n,
          cfg_valid,
          op_raw,
          key_len,
          crypt_n,
          dec_key_gen_n,
          prng_reseed,
          key_clear,
          data_out_clear,
          mux_sel_err,
          sp_enc_err,
          rnd_ctr_err,
          op_err,
          alert_fatal,
          prng_reseed_ack,
          sub_bytes_out_req_n,
          key_expand_out_req_n,
          crypt_q_n,
          dec_key_gen_q_n,
          prng_reseed_q,
          key_clear_q,
          data_out_clear_q} = in_buf;

  assign op = ciph_op_e'(op_raw);

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
  logic [3:0]       rnd_ctr;
  logic             crypt_d;
  logic             dec_key_gen_d;
  logic             prng_reseed_d;
  logic             key_clear_d;
  logic             data_out_clear_d;

  /////////////////
  // Regular FSM //
  /////////////////

  // The regular FSM operates on and produces the positive values of important control signals.
  // Invert *_n input signals here to get the positive values for the regular FSM. To obtain the
  // negated outputs, important output signals are inverted further below. Thanks to the prim_buf
  // synthesis optimization barriers, tools will push the inverters into the regular FSM.
  aes_cipher_control_fsm #(
    .SecMasking  ( SecMasking  ),
    .SecSBoxImpl ( SecSBoxImpl )
  ) u_aes_cipher_control_fsm (
    .clk_i                 ( clk_i                 ),
    .rst_ni                ( rst_ni                ),

    .in_valid_i            ( ~in_valid_n           ), // Invert for regular FSM.
    .in_ready_o            ( in_ready              ), // Invert below for negated output.

    .out_valid_o           ( out_valid             ), // Invert below for negated output.
    .out_ready_i           ( ~out_ready_n          ), // Invert for regular FSM.

    .cfg_valid_i           ( cfg_valid             ),
    .op_i                  ( op                    ),
    .key_len_i             ( key_len               ),
    .crypt_i               ( ~crypt_n              ), // Invert for regular FSM.
    .dec_key_gen_i         ( ~dec_key_gen_n        ), // Invert for regular FSM.
    .prng_reseed_i         ( prng_reseed           ),
    .key_clear_i           ( key_clear             ),
    .data_out_clear_i      ( data_out_clear        ),
    .mux_sel_err_i         ( mux_sel_err           ),
    .sp_enc_err_i          ( sp_enc_err            ),
    .rnd_ctr_err_i         ( rnd_ctr_err           ),
    .op_err_i              ( op_err                ),
    .alert_fatal_i         ( alert_fatal           ),
    .alert_o               ( alert                 ),

    .prng_update_o         ( prng_update           ),
    .prng_reseed_req_o     ( prng_reseed_req       ),
    .prng_reseed_ack_i     ( prng_reseed_ack       ),

    .state_sel_o           ( state_sel             ),
    .state_we_o            ( state_we              ), // Invert below for negated output.
    .sub_bytes_en_o        ( sub_bytes_en          ), // Invert below for negated output.
    .sub_bytes_out_req_i   ( ~sub_bytes_out_req_n  ), // Invert for regular FSM.
    .sub_bytes_out_ack_o   ( sub_bytes_out_ack     ), // Invert below for negated output.
    .add_rk_sel_o          ( add_rk_sel            ),

    .key_full_sel_o        ( key_full_sel          ),
    .key_full_we_o         ( key_full_we           ), // Invert below for negated output.
    .key_dec_sel_o         ( key_dec_sel           ),
    .key_dec_we_o          ( key_dec_we            ), // Invert below for negated output.
    .key_expand_en_o       ( key_expand_en         ), // Invert below for negated output.
    .key_expand_out_req_i  ( ~key_expand_out_req_n ), // Invert for regular FSM.
    .key_expand_out_ack_o  ( key_expand_out_ack    ), // Invert below for negated output.
    .key_expand_clear_o    ( key_expand_clear      ),
    .rnd_ctr_o             ( rnd_ctr               ),
    .key_words_sel_o       ( key_words_sel         ),
    .round_key_sel_o       ( round_key_sel         ),

    .crypt_q_i             ( ~crypt_q_n            ), // Invert for regular FSM.
    .crypt_d_o             ( crypt_d               ), // Invert below for negated output.
    .dec_key_gen_q_i       ( ~dec_key_gen_q_n      ), // Invert for regular FSM.
    .dec_key_gen_d_o       ( dec_key_gen_d         ), // Invert below for negated output.
    .key_clear_q_i         ( key_clear_q           ),
    .key_clear_d_o         ( key_clear_d           ),
    .prng_reseed_q_i       ( prng_reseed_q         ),
    .prng_reseed_d_o       ( prng_reseed_d         ),
    .data_out_clear_q_i    ( data_out_clear_q      ),
    .data_out_clear_d_o    ( data_out_clear_d      )
  );

  //////////////////////
  // Output Buffering //
  //////////////////////

  localparam int NumOutBufBits = $bits({
    in_ready_no,
    out_valid_no,
    alert_o,
    prng_update_o,
    prng_reseed_req_o,
    state_sel_o,
    state_we_no,
    sub_bytes_en_no,
    sub_bytes_out_ack_no,
    add_rk_sel_o,
    key_full_sel_o,
    key_full_we_no,
    key_dec_sel_o,
    key_dec_we_no,
    key_expand_en_no,
    key_expand_out_ack_no,
    key_expand_clear_o,
    rnd_ctr_o,
    key_words_sel_o,
    round_key_sel_o,
    crypt_d_no,
    dec_key_gen_d_no,
    key_clear_d_o,
    prng_reseed_d_o,
    data_out_clear_d_o
  });

  logic [NumOutBufBits-1:0] out, out_buf;

  // Important output control signals need to be inverted here. Synthesis tools will push the
  // inverters back into the regular FSM.
  assign out = {
    ~in_ready,
    ~out_valid,
    alert,
    prng_update,
    prng_reseed_req,
    state_sel,
    ~state_we,
    ~sub_bytes_en,
    ~sub_bytes_out_ack,
    add_rk_sel,
    key_full_sel,
    ~key_full_we,
    key_dec_sel,
    ~key_dec_we,
    ~key_expand_en,
    ~key_expand_out_ack,
    key_expand_clear,
    rnd_ctr,
    key_words_sel,
    round_key_sel,
    ~crypt_d,
    ~dec_key_gen_d,
    key_clear_d,
    prng_reseed_d,
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

  assign {in_ready_no,
          out_valid_no,
          alert_o,
          prng_update_o,
          prng_reseed_req_o,
          state_sel_o,
          state_we_no,
          sub_bytes_en_no,
          sub_bytes_out_ack_no,
          add_rk_sel_o,
          key_full_sel_o,
          key_full_we_no,
          key_dec_sel_o,
          key_dec_we_no,
          key_expand_en_no,
          key_expand_out_ack_no,
          key_expand_clear_o,
          rnd_ctr_o,
          key_words_sel_o,
          round_key_sel_o,
          crypt_d_no,
          dec_key_gen_d_no,
          key_clear_d_o,
          prng_reseed_d_o,
          data_out_clear_d_o} = out_buf;

endmodule
