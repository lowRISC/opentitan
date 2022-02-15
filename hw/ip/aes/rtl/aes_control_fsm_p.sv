// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES main control FSM
//
// This module contains the main control FSM handling the interplay of input/output registers and
// the AES cipher core. This version operates on and produces the positive values of important
// control signals.

`include "prim_assert.sv"

module aes_control_fsm_p
  import aes_pkg::*;
  import aes_reg_pkg::*;
#(
  parameter bit SecMasking = 0
) (
  input  logic                                    clk_i,
  input  logic                                    rst_ni,

  // Main control signals
  input  logic                                    ctrl_qe_i,
  output logic                                    ctrl_we_o,
  input  logic                                    ctrl_phase_i,
  input  logic                                    ctrl_err_storage_i,
  input  aes_op_e                                 op_i,
  input  aes_mode_e                               mode_i,
  input  ciph_op_e                                cipher_op_i,
  input  logic                                    sideload_i,
  input  prs_rate_e                               prng_reseed_rate_i,
  input  logic                                    manual_operation_i,
  input  logic                                    key_touch_forces_reseed_i,
  input  logic                                    start_i,
  input  logic                                    key_iv_data_in_clear_i,
  input  logic                                    data_out_clear_i,
  input  logic                                    prng_reseed_i,
  input  logic                                    mux_sel_err_i,
  input  logic                                    sp_enc_err_i,
  input  lc_ctrl_pkg::lc_tx_t                     lc_escalate_en_i,
  input  logic                                    alert_fatal_i,
  output logic                                    alert_o,

  // I/O register read/write enables
  input  logic                                    key_sideload_valid_i,
  input  logic [NumSharesKey-1:0][NumRegsKey-1:0] key_init_qe_i,
  input  logic                    [NumRegsIv-1:0] iv_qe_i,
  input  logic                  [NumRegsData-1:0] data_in_qe_i,
  input  logic                  [NumRegsData-1:0] data_out_re_i,
  output logic                                    data_in_we_o,
  output logic                                    data_out_we_o,           // Sparsify

  // Previous input data register
  output dip_sel_e                                data_in_prev_sel_o,
  output logic                                    data_in_prev_we_o,       // Sparsify

  // Cipher I/O muxes
  output si_sel_e                                 state_in_sel_o,
  output add_si_sel_e                             add_state_in_sel_o,
  output add_so_sel_e                             add_state_out_sel_o,

  // Counter
  output logic                                    ctr_incr_o,              // Sparsify
  input  logic                                    ctr_ready_i,             // Sparsify
  input  logic                 [NumSlicesCtr-1:0] ctr_we_i,                // Sparsify

  // Cipher core control and sync
  output logic                                    cipher_in_valid_o,       // Sparsify
  input  logic                                    cipher_in_ready_i,       // Sparsify
  input  logic                                    cipher_out_valid_i,      // Sparsify
  output logic                                    cipher_out_ready_o,      // Sparsify
  output logic                                    cipher_crypt_o,          // Sparsify
  input  logic                                    cipher_crypt_i,          // Sparsify
  output logic                                    cipher_dec_key_gen_o,    // Sparsify
  input  logic                                    cipher_dec_key_gen_i,    // Sparsify
  output logic                                    cipher_prng_reseed_o,
  input  logic                                    cipher_prng_reseed_i,
  output logic                                    cipher_key_clear_o,
  input  logic                                    cipher_key_clear_i,
  output logic                                    cipher_data_out_clear_o,
  input  logic                                    cipher_data_out_clear_i,

  // Initial key registers
  output key_init_sel_e                           key_init_sel_o,
  output logic [NumSharesKey-1:0][NumRegsKey-1:0] key_init_we_o,           // Sparsify

  // IV registers
  output iv_sel_e                                 iv_sel_o,
  output logic                 [NumSlicesCtr-1:0] iv_we_o,                 // Sparsify

  // Pseudo-random number generator interface
  output logic                                    prng_data_req_o,
  input  logic                                    prng_data_ack_i,
  output logic                                    prng_reseed_req_o,
  input  logic                                    prng_reseed_ack_i,

  // Trigger register
  output logic                                    start_we_o,
  output logic                                    key_iv_data_in_clear_we_o,
  output logic                                    data_out_clear_we_o,
  output logic                                    prng_reseed_o,
  output logic                                    prng_reseed_we_o,

  // Status register
  output logic                                    idle_o,
  output logic                                    idle_we_o,
  output logic                                    stall_o,
  output logic                                    stall_we_o,
  input  logic                                    output_lost_i,
  output logic                                    output_lost_o,
  output logic                                    output_lost_we_o,
  output logic                                    output_valid_o,
  output logic                                    output_valid_we_o,
  output logic                                    input_ready_o,
  output logic                                    input_ready_we_o
);

  /////////////////////
  // Input Buffering //
  /////////////////////

  localparam int NumInBufBits = $bits({
    ctrl_qe_i,
    ctrl_phase_i,
    ctrl_err_storage_i,
    op_i,
    mode_i,
    cipher_op_i,
    sideload_i,
    prng_reseed_rate_i,
    manual_operation_i,
    key_touch_forces_reseed_i,
    start_i,
    key_iv_data_in_clear_i,
    data_out_clear_i,
    prng_reseed_i,
    mux_sel_err_i,
    sp_enc_err_i,
    lc_escalate_en_i,
    alert_fatal_i,
    key_sideload_valid_i,
    key_init_qe_i,
    iv_qe_i,
    data_in_qe_i,
    data_out_re_i,
    ctr_ready_i,
    ctr_we_i,
    cipher_in_ready_i,
    cipher_out_valid_i,
    cipher_crypt_i,
    cipher_dec_key_gen_i,
    cipher_prng_reseed_i,
    cipher_key_clear_i,
    cipher_data_out_clear_i,
    prng_data_ack_i,
    prng_reseed_ack_i,
    output_lost_i
  });

  logic [NumInBufBits-1:0] in, in_buf;

  assign in = {
    ctrl_qe_i,
    ctrl_phase_i,
    ctrl_err_storage_i,
    op_i,
    mode_i,
    cipher_op_i,
    sideload_i,
    prng_reseed_rate_i,
    manual_operation_i,
    key_touch_forces_reseed_i,
    start_i,
    key_iv_data_in_clear_i,
    data_out_clear_i,
    prng_reseed_i,
    mux_sel_err_i,
    sp_enc_err_i,
    lc_escalate_en_i,
    alert_fatal_i,
    key_sideload_valid_i,
    key_init_qe_i,
    iv_qe_i,
    data_in_qe_i,
    data_out_re_i,
    ctr_ready_i,
    ctr_we_i,
    cipher_in_ready_i,
    cipher_out_valid_i,
    cipher_crypt_i,
    cipher_dec_key_gen_i,
    cipher_prng_reseed_i,
    cipher_key_clear_i,
    cipher_data_out_clear_i,
    prng_data_ack_i,
    prng_reseed_ack_i,
    output_lost_i
  };

  // This primitive is used to place a size-only constraint on the
  // buffers to act as a synthesis optimization barrier.
  prim_buf #(
    .Width(NumInBufBits)
  ) u_prim_buf_in (
    .in_i(in),
    .out_o(in_buf)
  );

  logic                                    ctrl_qe;
  logic                                    ctrl_phase;
  logic                                    ctrl_err_storage;
  aes_op_e                                 op;
  aes_mode_e                               mode;
  ciph_op_e                                cipher_op;
  logic             [$bits(cipher_op)-1:0] cipher_op_raw;
  logic                                    sideload;
  prs_rate_e                               prng_reseed_rate;
  logic                                    manual_operation;
  logic                                    key_touch_forces_reseed;
  logic                                    start;
  logic                                    key_iv_data_in_clear;
  logic                                    data_out_clear;
  logic                                    prng_reseed_in_buf;
  logic                                    mux_sel_err;
  logic                                    sp_enc_err;
  lc_ctrl_pkg::lc_tx_t                     lc_escalate_en;
  logic                                    alert_fatal;
  logic                                    key_sideload_valid;
  logic [NumSharesKey-1:0][NumRegsKey-1:0] key_init_qe;
  logic                    [NumRegsIv-1:0] iv_qe;
  logic                  [NumRegsData-1:0] data_in_qe;
  logic                  [NumRegsData-1:0] data_out_re;
  logic                                    ctr_ready;
  logic                 [NumSlicesCtr-1:0] ctr_we;
  logic                                    cipher_in_ready;
  logic                                    cipher_out_valid;
  logic                                    cipher_crypt_in_buf;
  logic                                    cipher_dec_key_gen_in_buf;
  logic                                    cipher_prng_reseed_in_buf;
  logic                                    cipher_key_clear_in_buf;
  logic                                    cipher_data_out_clear_in_buf;
  logic                                    prng_data_ack;
  logic                                    prng_reseed_ack;
  logic                                    output_lost_in_buf;

  assign {ctrl_qe,
          ctrl_phase,
          ctrl_err_storage,
          op,
          mode,
          cipher_op_raw,
          sideload,
          prng_reseed_rate,
          manual_operation,
          key_touch_forces_reseed,
          start,
          key_iv_data_in_clear,
          data_out_clear,
          prng_reseed_in_buf,
          mux_sel_err,
          sp_enc_err,
          lc_escalate_en,
          alert_fatal,
          key_sideload_valid,
          key_init_qe,
          iv_qe,
          data_in_qe,
          data_out_re,
          ctr_ready,
          ctr_we,
          cipher_in_ready,
          cipher_out_valid,
          cipher_crypt_in_buf,
          cipher_dec_key_gen_in_buf,
          cipher_prng_reseed_in_buf,
          cipher_key_clear_in_buf,
          cipher_data_out_clear_in_buf,
          prng_data_ack,
          prng_reseed_ack,
          output_lost_in_buf} = in_buf;

  assign cipher_op = ciph_op_e'(cipher_op_raw);

  // Intermediate output signals
  logic                                    ctrl_we;
  logic                                    alert;
  logic                                    data_in_we;
  logic                                    data_out_we;
  dip_sel_e                                data_in_prev_sel;
  logic                                    data_in_prev_we;
  si_sel_e                                 state_in_sel;
  add_si_sel_e                             add_state_in_sel;
  add_so_sel_e                             add_state_out_sel;
  logic                                    ctr_incr;
  logic                                    cipher_in_valid;
  logic                                    cipher_out_ready;
  logic                                    cipher_crypt_out_buf;
  logic                                    cipher_dec_key_gen_out_buf;
  logic                                    cipher_prng_reseed_out_buf;
  logic                                    cipher_key_clear_out_buf;
  logic                                    cipher_data_out_clear_out_buf;
  key_init_sel_e                           key_init_sel;
  logic [NumSharesKey-1:0][NumRegsKey-1:0] key_init_we;
  iv_sel_e                                 iv_sel;
  logic                 [NumSlicesCtr-1:0] iv_we;
  logic                                    prng_data_req;
  logic                                    prng_reseed_req;
  logic                                    start_we;
  logic                                    key_iv_data_in_clear_we;
  logic                                    data_out_clear_we;
  logic                                    prng_reseed_out_buf;
  logic                                    prng_reseed_we;
  logic                                    idle;
  logic                                    idle_we;
  logic                                    stall;
  logic                                    stall_we;
  logic                                    output_lost_out_buf;
  logic                                    output_lost_we;
  logic                                    output_valid;
  logic                                    output_valid_we;
  logic                                    input_ready;
  logic                                    input_ready_we;

  /////////////////
  // Regular FSM //
  /////////////////

  aes_control_fsm #(
    .SecMasking ( SecMasking )
  ) u_aes_control_fsm (
    .clk_i                     ( clk_i                         ),
    .rst_ni                    ( rst_ni                        ),

    .ctrl_qe_i                 ( ctrl_qe                       ),
    .ctrl_we_o                 ( ctrl_we                       ),
    .ctrl_phase_i              ( ctrl_phase                    ),
    .ctrl_err_storage_i        ( ctrl_err_storage              ),
    .op_i                      ( op                            ),
    .mode_i                    ( mode                          ),
    .cipher_op_i               ( cipher_op                     ),
    .sideload_i                ( sideload                      ),
    .prng_reseed_rate_i        ( prng_reseed_rate              ),
    .manual_operation_i        ( manual_operation              ),
    .key_touch_forces_reseed_i ( key_touch_forces_reseed       ),
    .start_i                   ( start                         ),
    .key_iv_data_in_clear_i    ( key_iv_data_in_clear          ),
    .data_out_clear_i          ( data_out_clear                ),
    .prng_reseed_i             ( prng_reseed_in_buf            ),
    .mux_sel_err_i             ( mux_sel_err                   ),
    .sp_enc_err_i              ( sp_enc_err                    ),
    .lc_escalate_en_i          ( lc_escalate_en                ),
    .alert_fatal_i             ( alert_fatal                   ),
    .alert_o                   ( alert                         ),

    .key_sideload_valid_i      ( key_sideload_valid            ),
    .key_init_qe_i             ( key_init_qe                   ),
    .iv_qe_i                   ( iv_qe                         ),
    .data_in_qe_i              ( data_in_qe                    ),
    .data_out_re_i             ( data_out_re                   ),
    .data_in_we_o              ( data_in_we                    ),
    .data_out_we_o             ( data_out_we                   ),

    .data_in_prev_sel_o        ( data_in_prev_sel              ),
    .data_in_prev_we_o         ( data_in_prev_we               ),

    .state_in_sel_o            ( state_in_sel                  ),
    .add_state_in_sel_o        ( add_state_in_sel              ),
    .add_state_out_sel_o       ( add_state_out_sel             ),

    .ctr_incr_o                ( ctr_incr                      ),
    .ctr_ready_i               ( ctr_ready                     ),
    .ctr_we_i                  ( ctr_we                        ),

    .cipher_in_valid_o         ( cipher_in_valid               ),
    .cipher_in_ready_i         ( cipher_in_ready               ),
    .cipher_out_valid_i        ( cipher_out_valid              ),
    .cipher_out_ready_o        ( cipher_out_ready              ),
    .cipher_crypt_o            ( cipher_crypt_out_buf          ),
    .cipher_crypt_i            ( cipher_crypt_in_buf           ),
    .cipher_dec_key_gen_o      ( cipher_dec_key_gen_out_buf    ),
    .cipher_dec_key_gen_i      ( cipher_dec_key_gen_in_buf     ),
    .cipher_prng_reseed_o      ( cipher_prng_reseed_out_buf    ),
    .cipher_prng_reseed_i      ( cipher_prng_reseed_in_buf     ),
    .cipher_key_clear_o        ( cipher_key_clear_out_buf      ),
    .cipher_key_clear_i        ( cipher_key_clear_in_buf       ),
    .cipher_data_out_clear_o   ( cipher_data_out_clear_out_buf ),
    .cipher_data_out_clear_i   ( cipher_data_out_clear_in_buf  ),

    .key_init_sel_o            ( key_init_sel                  ),
    .key_init_we_o             ( key_init_we                   ),

    .iv_sel_o                  ( iv_sel                        ),
    .iv_we_o                   ( iv_we                         ),

    .prng_data_req_o           ( prng_data_req                 ),
    .prng_data_ack_i           ( prng_data_ack                 ),
    .prng_reseed_req_o         ( prng_reseed_req               ),
    .prng_reseed_ack_i         ( prng_reseed_ack               ),

    .start_we_o                ( start_we                      ),
    .key_iv_data_in_clear_we_o ( key_iv_data_in_clear_we       ),
    .data_out_clear_we_o       ( data_out_clear_we             ),
    .prng_reseed_o             ( prng_reseed_out_buf           ),
    .prng_reseed_we_o          ( prng_reseed_we                ),

    .idle_o                    ( idle                          ),
    .idle_we_o                 ( idle_we                       ),
    .stall_o                   ( stall                         ),
    .stall_we_o                ( stall_we                      ),
    .output_lost_i             ( output_lost_in_buf            ),
    .output_lost_o             ( output_lost_out_buf           ),
    .output_lost_we_o          ( output_lost_we                ),
    .output_valid_o            ( output_valid                  ),
    .output_valid_we_o         ( output_valid_we               ),
    .input_ready_o             ( input_ready                   ),
    .input_ready_we_o          ( input_ready_we                )
  );

  //////////////////////
  // Output Buffering //
  //////////////////////

  localparam int NumOutBufBits = $bits({
    ctrl_we_o,
    alert_o,
    data_in_we_o,
    data_out_we_o,
    data_in_prev_sel_o,
    data_in_prev_we_o,
    state_in_sel_o,
    add_state_in_sel_o,
    add_state_out_sel_o,
    ctr_incr_o,
    cipher_in_valid_o,
    cipher_out_ready_o,
    cipher_crypt_o,
    cipher_dec_key_gen_o,
    cipher_prng_reseed_o,
    cipher_key_clear_o,
    cipher_data_out_clear_o,
    key_init_sel_o,
    key_init_we_o,
    iv_sel_o,
    iv_we_o,
    prng_data_req_o,
    prng_reseed_req_o,
    start_we_o,
    key_iv_data_in_clear_we_o,
    data_out_clear_we_o,
    prng_reseed_o,
    prng_reseed_we_o,
    idle_o,
    idle_we_o,
    stall_o,
    stall_we_o,
    output_lost_o,
    output_lost_we_o,
    output_valid_o,
    output_valid_we_o,
    input_ready_o,
    input_ready_we_o
  });

  logic [NumOutBufBits-1:0] out, out_buf;

  assign out = {
    ctrl_we,
    alert,
    data_in_we,
    data_out_we,
    data_in_prev_sel,
    data_in_prev_we,
    state_in_sel,
    add_state_in_sel,
    add_state_out_sel,
    ctr_incr,
    cipher_in_valid,
    cipher_out_ready,
    cipher_crypt_out_buf,
    cipher_dec_key_gen_out_buf,
    cipher_prng_reseed_out_buf,
    cipher_key_clear_out_buf,
    cipher_data_out_clear_out_buf,
    key_init_sel,
    key_init_we,
    iv_sel,
    iv_we,
    prng_data_req,
    prng_reseed_req,
    start_we,
    key_iv_data_in_clear_we,
    data_out_clear_we,
    prng_reseed_out_buf,
    prng_reseed_we,
    idle,
    idle_we,
    stall,
    stall_we,
    output_lost_out_buf,
    output_lost_we,
    output_valid,
    output_valid_we,
    input_ready,
    input_ready_we
  };

  // This primitive is used to place a size-only constraint on the
  // buffers to act as a synthesis optimization barrier.
  prim_buf #(
    .Width(NumOutBufBits)
  ) u_prim_buf_out (
    .in_i(out),
    .out_o(out_buf)
  );

  assign {ctrl_we_o,
          alert_o,
          data_in_we_o,
          data_out_we_o,
          data_in_prev_sel_o,
          data_in_prev_we_o,
          state_in_sel_o,
          add_state_in_sel_o,
          add_state_out_sel_o,
          ctr_incr_o,
          cipher_in_valid_o,
          cipher_out_ready_o,
          cipher_crypt_o,
          cipher_dec_key_gen_o,
          cipher_prng_reseed_o,
          cipher_key_clear_o,
          cipher_data_out_clear_o,
          key_init_sel_o,
          key_init_we_o,
          iv_sel_o,
          iv_we_o,
          prng_data_req_o,
          prng_reseed_req_o,
          start_we_o,
          key_iv_data_in_clear_we_o,
          data_out_clear_we_o,
          prng_reseed_o,
          prng_reseed_we_o,
          idle_o,
          idle_we_o,
          stall_o,
          stall_we_o,
          output_lost_o,
          output_lost_we_o,
          output_valid_o,
          output_valid_we_o,
          input_ready_o,
          input_ready_we_o} = out_buf;

endmodule
