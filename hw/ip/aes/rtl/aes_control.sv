// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES main control
//
// This module controls the interplay of input/output registers and the AES cipher core.

`include "prim_assert.sv"

module aes_control
  import aes_pkg::*;
  import aes_reg_pkg::*;
#(
  parameter bit          SecMasking           = 0,
  parameter int unsigned SecStartTriggerDelay = 0
) (
  input  logic                      clk_i,
  input  logic                      rst_ni,

  // Main control signals
  input  logic                      ctrl_qe_i,
  output logic                      ctrl_we_o,
  input  logic                      ctrl_phase_i,
  input  logic                      ctrl_err_storage_i,
  input  aes_op_e                   op_i,
  input  aes_mode_e                 mode_i,
  input  ciph_op_e                  cipher_op_i,
  input  logic                      sideload_i,
  input  prs_rate_e                 prng_reseed_rate_i,
  input  logic                      manual_operation_i,
  input  logic                      key_touch_forces_reseed_i,
  input  logic                      start_i,
  input  logic                      key_iv_data_in_clear_i,
  input  logic                      data_out_clear_i,
  input  logic                      prng_reseed_i,
  input  logic                      mux_sel_err_i,
  input  logic                      sp_enc_err_i,
  input  lc_ctrl_pkg::lc_tx_t       lc_escalate_en_i,
  input  logic                      alert_fatal_i,
  output logic                      alert_o,

  // I/O register read/write enables
  input  logic                      key_sideload_valid_i,
  input  logic     [NumRegsKey-1:0] key_init_qe_i [NumSharesKey],
  input  logic      [NumRegsIv-1:0] iv_qe_i,
  input  logic    [NumRegsData-1:0] data_in_qe_i,
  input  logic    [NumRegsData-1:0] data_out_re_i,
  output logic                      data_in_we_o,
  output sp2v_e                     data_out_we_o,

  // Previous input data register
  output dip_sel_e                  data_in_prev_sel_o,
  output sp2v_e                     data_in_prev_we_o,

  // Cipher I/O muxes
  output si_sel_e                   state_in_sel_o,
  output add_si_sel_e               add_state_in_sel_o,
  output add_so_sel_e               add_state_out_sel_o,

  // Counter
  output sp2v_e                     ctr_incr_o,
  input  sp2v_e                     ctr_ready_i,
  input  sp2v_e  [NumSlicesCtr-1:0] ctr_we_i,

  // Cipher core control and sync
  output sp2v_e                     cipher_in_valid_o,
  input  sp2v_e                     cipher_in_ready_i,
  input  sp2v_e                     cipher_out_valid_i,
  output sp2v_e                     cipher_out_ready_o,
  output sp2v_e                     cipher_crypt_o,
  input  sp2v_e                     cipher_crypt_i,
  output sp2v_e                     cipher_dec_key_gen_o,
  input  sp2v_e                     cipher_dec_key_gen_i,
  output logic                      cipher_prng_reseed_o,
  input  logic                      cipher_prng_reseed_i,
  output logic                      cipher_key_clear_o,
  input  logic                      cipher_key_clear_i,
  output logic                      cipher_data_out_clear_o,
  input  logic                      cipher_data_out_clear_i,

  // Initial key registers
  output key_init_sel_e             key_init_sel_o,
  output sp2v_e    [NumRegsKey-1:0] key_init_we_o [NumSharesKey],

  // IV registers
  output iv_sel_e                   iv_sel_o,
  output sp2v_e  [NumSlicesCtr-1:0] iv_we_o,

  // Pseudo-random number generator interface
  output logic                      prng_data_req_o,
  input  logic                      prng_data_ack_i,
  output logic                      prng_reseed_req_o,
  input  logic                      prng_reseed_ack_i,

  // Trigger register
  output logic                      start_o,
  output logic                      start_we_o,
  output logic                      key_iv_data_in_clear_o,
  output logic                      key_iv_data_in_clear_we_o,
  output logic                      data_out_clear_o,
  output logic                      data_out_clear_we_o,
  output logic                      prng_reseed_o,
  output logic                      prng_reseed_we_o,

  // Status register
  output logic                      idle_o,
  output logic                      idle_we_o,
  output logic                      stall_o,
  output logic                      stall_we_o,
  input  logic                      output_lost_i,
  output logic                      output_lost_o,
  output logic                      output_lost_we_o,
  output logic                      output_valid_o,
  output logic                      output_valid_we_o,
  output logic                      input_ready_o,
  output logic                      input_ready_we_o
);

  // Optional delay of manual start trigger
  logic start_trigger;

  // Create a lint error to reduce the risk of accidentally enabling this feature.
  `ASSERT_STATIC_LINT_ERROR(AesSecStartTriggerDelayNonDefault, SecStartTriggerDelay == 0)

  if (SecStartTriggerDelay > 0) begin : gen_start_delay
    // Delay the manual start trigger input for SCA measurements.
    localparam int unsigned WidthCounter = $clog2(SecStartTriggerDelay+1);
    logic [WidthCounter-1:0] count_d, count_q;

    // Clear counter when input goes low. Keep value if the specified delay is reached.
    assign count_d = !start_i       ? '0      :
                      start_trigger ? count_q : count_q + 1'b1;
    assign start_trigger = (count_q == SecStartTriggerDelay[WidthCounter-1:0]) ? 1'b1 : 1'b0;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        count_q <= '0;
      end else begin
        count_q <= count_d;
      end
    end

  end else begin : gen_no_start_delay
    // Directly forward the manual start trigger input.
    assign start_trigger = start_i;
  end

  // Signals
  sp2v_e                         ctr_ready;
  sp2v_e      [NumSlicesCtr-1:0] ctr_we;
  sp2v_e                         cipher_in_ready;
  sp2v_e                         cipher_out_valid;
  sp2v_e                         cipher_crypt;
  sp2v_e                         cipher_dec_key_gen;
  logic                          mux_sel_err;
  logic                          mr_err;
  logic                          sp_enc_err;

  // Sparsified FSM signals. These are needed for connecting the individual bits of the Sp2V
  // signals to the single-rail FSMs.
  logic          [Sp2VWidth-1:0] sp_data_out_we;
  logic          [Sp2VWidth-1:0] sp_data_in_prev_we;
  logic          [Sp2VWidth-1:0] sp_ctr_incr;
  logic          [Sp2VWidth-1:0] sp_ctr_ready;
  logic          [Sp2VWidth-1:0] sp_cipher_in_valid;
  logic          [Sp2VWidth-1:0] sp_cipher_in_ready;
  logic          [Sp2VWidth-1:0] sp_cipher_out_valid;
  logic          [Sp2VWidth-1:0] sp_cipher_out_ready;
  logic          [Sp2VWidth-1:0] sp_in_cipher_crypt;
  logic          [Sp2VWidth-1:0] sp_out_cipher_crypt;
  logic          [Sp2VWidth-1:0] sp_in_cipher_dec_key_gen;
  logic          [Sp2VWidth-1:0] sp_out_cipher_dec_key_gen;

  // Multi-rail signals. These are outputs of the single-rail FSMs and need combining.
  logic          [Sp2VWidth-1:0] mr_ctrl_we;
  logic          [Sp2VWidth-1:0] mr_alert;
  logic          [Sp2VWidth-1:0] mr_data_in_we;
  dip_sel_e      [Sp2VWidth-1:0] mr_data_in_prev_sel;
  si_sel_e       [Sp2VWidth-1:0] mr_state_in_sel;
  add_si_sel_e   [Sp2VWidth-1:0] mr_add_state_in_sel;
  add_so_sel_e   [Sp2VWidth-1:0] mr_add_state_out_sel;
  logic          [Sp2VWidth-1:0] mr_cipher_prng_reseed;
  logic          [Sp2VWidth-1:0] mr_cipher_key_clear;
  logic          [Sp2VWidth-1:0] mr_cipher_data_out_clear;
  key_init_sel_e [Sp2VWidth-1:0] mr_key_init_sel;
  iv_sel_e       [Sp2VWidth-1:0] mr_iv_sel;
  logic          [Sp2VWidth-1:0] mr_prng_data_req;
  logic          [Sp2VWidth-1:0] mr_prng_reseed_req;
  logic          [Sp2VWidth-1:0] mr_start_we;
  logic          [Sp2VWidth-1:0] mr_key_iv_data_in_clear_we;
  logic          [Sp2VWidth-1:0] mr_data_out_clear_we;
  logic          [Sp2VWidth-1:0] mr_prng_reseed;
  logic          [Sp2VWidth-1:0] mr_prng_reseed_we;
  logic          [Sp2VWidth-1:0] mr_idle;
  logic          [Sp2VWidth-1:0] mr_idle_we;
  logic          [Sp2VWidth-1:0] mr_stall;
  logic          [Sp2VWidth-1:0] mr_stall_we;
  logic          [Sp2VWidth-1:0] mr_output_lost;
  logic          [Sp2VWidth-1:0] mr_output_lost_we;
  logic          [Sp2VWidth-1:0] mr_output_valid;
  logic          [Sp2VWidth-1:0] mr_output_valid_we;
  logic          [Sp2VWidth-1:0] mr_input_ready;
  logic          [Sp2VWidth-1:0] mr_input_ready_we;

  // To ease interfacing with the individual FSM rails, some signals need to be converted to packed
  // arrays.
  logic [Sp2VWidth-1:0][NumSharesKey-1:0][NumRegsKey-1:0]                int_key_init_we;
  logic                [NumSharesKey-1:0][NumRegsKey-1:0][Sp2VWidth-1:0] log_key_init_we;
  logic                [NumSharesKey-1:0][NumRegsKey-1:0]                int_key_init_qe;
  for (genvar s = 0; s < NumSharesKey; s++) begin : gen_conv_key_init_wqe_shares
    for (genvar i = 0; i < NumRegsKey; i++) begin : gen_conv_key_init_wqe_regs
      assign int_key_init_qe[s][i] = key_init_qe_i[s][i];
      for (genvar j = 0; j < Sp2VWidth; j++) begin : gen_conv_key_init_wqe_log
        assign log_key_init_we[s][i][j] = int_key_init_we[j][s][i];
      end
      assign key_init_we_o[s][i] = sp2v_e'(log_key_init_we[s][i]);
    end
  end
  logic [Sp2VWidth-1:0][NumSlicesCtr-1:0]                int_ctr_we;
  logic                [NumSlicesCtr-1:0][Sp2VWidth-1:0] log_ctr_we;
  logic [Sp2VWidth-1:0][NumSlicesCtr-1:0]                int_iv_we;
  logic                [NumSlicesCtr-1:0][Sp2VWidth-1:0] log_iv_we;
  for (genvar i = 0; i < NumSlicesCtr; i++) begin : gen_conv_ctr_iv_we_slices
    assign log_ctr_we[i] = {ctr_we[i]};
    for (genvar j = 0; j < Sp2VWidth; j++) begin : gen_conv_ctr_iv_we_log
      assign int_ctr_we[j][i] = log_ctr_we[i][j];
      assign log_iv_we[i][j]  = int_iv_we[j][i];
    end
    assign iv_we_o[i] = sp2v_e'(log_iv_we[i]);
  end

  /////////
  // FSM //
  /////////

  // Convert sp2v_e signals to sparsified inputs.
  assign sp_ctr_ready             = {ctr_ready};
  assign sp_cipher_in_ready       = {cipher_in_ready};
  assign sp_cipher_out_valid      = {cipher_out_valid};
  assign sp_in_cipher_crypt       = {cipher_crypt};
  assign sp_in_cipher_dec_key_gen = {cipher_dec_key_gen};

  // SEC_CM: MAIN.FSM.REDUN
  // For every bit in the Sp2V signals, one separate rail is instantiated. The inputs and outputs
  // of every rail are buffered to prevent aggressive synthesis optimizations.
  for (genvar i = 0; i < Sp2VWidth; i++) begin : gen_fsm
    if (SP2V_LOGIC_HIGH[i] == 1'b1) begin : gen_fsm_p
      aes_control_fsm_p #(
        .SecMasking ( SecMasking )
      ) u_aes_control_fsm_i (
        .clk_i                     ( clk_i                         ),
        .rst_ni                    ( rst_ni                        ),

        .ctrl_qe_i                 ( ctrl_qe_i                     ),
        .ctrl_we_o                 ( mr_ctrl_we[i]                 ), // AND-combine
        .ctrl_phase_i              ( ctrl_phase_i                  ),
        .ctrl_err_storage_i        ( ctrl_err_storage_i            ),
        .op_i                      ( op_i                          ),
        .mode_i                    ( mode_i                        ),
        .cipher_op_i               ( cipher_op_i                   ),
        .sideload_i                ( sideload_i                    ),
        .prng_reseed_rate_i        ( prng_reseed_rate_i            ),
        .manual_operation_i        ( manual_operation_i            ),
        .key_touch_forces_reseed_i ( key_touch_forces_reseed_i     ),
        .start_i                   ( start_trigger                 ),
        .key_iv_data_in_clear_i    ( key_iv_data_in_clear_i        ),
        .data_out_clear_i          ( data_out_clear_i              ),
        .prng_reseed_i             ( prng_reseed_i                 ),
        .mux_sel_err_i             ( mux_sel_err                   ),
        .sp_enc_err_i              ( sp_enc_err                    ),
        .lc_escalate_en_i          ( lc_escalate_en_i              ),
        .alert_fatal_i             ( alert_fatal_i                 ),
        .alert_o                   ( mr_alert[i]                   ), // OR-combine

        .key_sideload_valid_i      ( key_sideload_valid_i          ),
        .key_init_qe_i             ( int_key_init_qe               ),
        .iv_qe_i                   ( iv_qe_i                       ),
        .data_in_qe_i              ( data_in_qe_i                  ),
        .data_out_re_i             ( data_out_re_i                 ),
        .data_in_we_o              ( mr_data_in_we[i]              ), // AND-combine
        .data_out_we_o             ( sp_data_out_we[i]             ), // Sparsified

        .data_in_prev_sel_o        ( mr_data_in_prev_sel[i]        ), // OR-combine
        .data_in_prev_we_o         ( sp_data_in_prev_we[i]         ), // Sparsified

        .state_in_sel_o            ( mr_state_in_sel[i]            ), // OR-combine
        .add_state_in_sel_o        ( mr_add_state_in_sel[i]        ), // OR-combine
        .add_state_out_sel_o       ( mr_add_state_out_sel[i]       ), // OR-combine

        .ctr_incr_o                ( sp_ctr_incr[i]                ), // Sparsified
        .ctr_ready_i               ( sp_ctr_ready[i]               ), // Sparsified
        .ctr_we_i                  ( int_ctr_we[i]                 ), // Sparsified

        .cipher_in_valid_o         ( sp_cipher_in_valid[i]         ), // Sparsified
        .cipher_in_ready_i         ( sp_cipher_in_ready[i]         ), // Sparsified
        .cipher_out_valid_i        ( sp_cipher_out_valid[i]        ), // Sparsified
        .cipher_out_ready_o        ( sp_cipher_out_ready[i]        ), // Sparsified
        .cipher_crypt_o            ( sp_out_cipher_crypt[i]        ), // Sparsified
        .cipher_crypt_i            ( sp_in_cipher_crypt[i]         ), // Sparsified
        .cipher_dec_key_gen_o      ( sp_out_cipher_dec_key_gen[i]  ), // Sparsified
        .cipher_dec_key_gen_i      ( sp_in_cipher_dec_key_gen[i]   ), // Sparsified
        .cipher_prng_reseed_o      ( mr_cipher_prng_reseed[i]      ), // OR-combine
        .cipher_prng_reseed_i      ( cipher_prng_reseed_i          ),
        .cipher_key_clear_o        ( mr_cipher_key_clear[i]        ), // OR-combine
        .cipher_key_clear_i        ( cipher_key_clear_i            ),
        .cipher_data_out_clear_o   ( mr_cipher_data_out_clear[i]   ), // OR-combine
        .cipher_data_out_clear_i   ( cipher_data_out_clear_i       ),

        .key_init_sel_o            ( mr_key_init_sel[i]            ), // OR-combine
        .key_init_we_o             ( int_key_init_we[i]            ), // Sparsified

        .iv_sel_o                  ( mr_iv_sel[i]                  ), // OR-combine
        .iv_we_o                   ( int_iv_we[i]                  ), // Sparsified

        .prng_data_req_o           ( mr_prng_data_req[i]           ), // OR-combine
        .prng_data_ack_i           ( prng_data_ack_i               ),
        .prng_reseed_req_o         ( mr_prng_reseed_req[i]         ), // OR-combine
        .prng_reseed_ack_i         ( prng_reseed_ack_i             ),

        .start_we_o                ( mr_start_we[i]                ), // OR-combine
        .key_iv_data_in_clear_we_o ( mr_key_iv_data_in_clear_we[i] ), // AND-combine
        .data_out_clear_we_o       ( mr_data_out_clear_we[i]       ), // AND-combine
        .prng_reseed_o             ( mr_prng_reseed[i]             ), // OR-combine
        .prng_reseed_we_o          ( mr_prng_reseed_we[i]          ), // OR-combine

        .idle_o                    ( mr_idle[i]                    ), // AND-combine
        .idle_we_o                 ( mr_idle_we[i]                 ), // AND-combine
        .stall_o                   ( mr_stall[i]                   ), // AND-combine
        .stall_we_o                ( mr_stall_we[i]                ), // AND-combine
        .output_lost_i             ( output_lost_i                 ), // AND-combine
        .output_lost_o             ( mr_output_lost[i]             ), // AND-combine
        .output_lost_we_o          ( mr_output_lost_we[i]          ), // AND-combine
        .output_valid_o            ( mr_output_valid[i]            ), // AND-combine
        .output_valid_we_o         ( mr_output_valid_we[i]         ), // AND-combine
        .input_ready_o             ( mr_input_ready[i]             ), // AND-combine
        .input_ready_we_o          ( mr_input_ready_we[i]          )  // AND-combine
      );
    end else begin : gen_fsm_n
      aes_control_fsm_n #(
        .SecMasking ( SecMasking )
      ) u_aes_control_fsm_i (
        .clk_i                     ( clk_i                         ),
        .rst_ni                    ( rst_ni                        ),

        .ctrl_qe_i                 ( ctrl_qe_i                     ),
        .ctrl_we_o                 ( mr_ctrl_we[i]                 ), // AND-combine
        .ctrl_phase_i              ( ctrl_phase_i                  ),
        .ctrl_err_storage_i        ( ctrl_err_storage_i            ),
        .op_i                      ( op_i                          ),
        .mode_i                    ( mode_i                        ),
        .cipher_op_i               ( cipher_op_i                   ),
        .sideload_i                ( sideload_i                    ),
        .prng_reseed_rate_i        ( prng_reseed_rate_i            ),
        .manual_operation_i        ( manual_operation_i            ),
        .key_touch_forces_reseed_i ( key_touch_forces_reseed_i     ),
        .start_i                   ( start_trigger                 ),
        .key_iv_data_in_clear_i    ( key_iv_data_in_clear_i        ),
        .data_out_clear_i          ( data_out_clear_i              ),
        .prng_reseed_i             ( prng_reseed_i                 ),
        .mux_sel_err_i             ( mux_sel_err                   ),
        .sp_enc_err_i              ( sp_enc_err                    ),
        .lc_escalate_en_i          ( lc_escalate_en_i              ),
        .alert_fatal_i             ( alert_fatal_i                 ),
        .alert_o                   ( mr_alert[i]                   ), // OR-combine

        .key_sideload_valid_i      ( key_sideload_valid_i          ),
        .key_init_qe_i             ( int_key_init_qe               ),
        .iv_qe_i                   ( iv_qe_i                       ),
        .data_in_qe_i              ( data_in_qe_i                  ),
        .data_out_re_i             ( data_out_re_i                 ),
        .data_in_we_o              ( mr_data_in_we[i]              ), // AND-combine
        .data_out_we_no            ( sp_data_out_we[i]             ), // Sparsified

        .data_in_prev_sel_o        ( mr_data_in_prev_sel[i]        ), // OR-combine
        .data_in_prev_we_no        ( sp_data_in_prev_we[i]         ), // Sparsified

        .state_in_sel_o            ( mr_state_in_sel[i]            ), // OR-combine
        .add_state_in_sel_o        ( mr_add_state_in_sel[i]        ), // OR-combine
        .add_state_out_sel_o       ( mr_add_state_out_sel[i]       ), // OR-combine

        .ctr_incr_no               ( sp_ctr_incr[i]                ), // Sparsified
        .ctr_ready_ni              ( sp_ctr_ready[i]               ), // Sparsified
        .ctr_we_ni                 ( int_ctr_we[i]                 ), // Sparsified

        .cipher_in_valid_no        ( sp_cipher_in_valid[i]         ), // Sparsified
        .cipher_in_ready_ni        ( sp_cipher_in_ready[i]         ), // Sparsified
        .cipher_out_valid_ni       ( sp_cipher_out_valid[i]        ), // Sparsified
        .cipher_out_ready_no       ( sp_cipher_out_ready[i]        ), // Sparsified
        .cipher_crypt_no           ( sp_out_cipher_crypt[i]        ), // Sparsified
        .cipher_crypt_ni           ( sp_in_cipher_crypt[i]         ), // Sparsified
        .cipher_dec_key_gen_no     ( sp_out_cipher_dec_key_gen[i]  ), // Sparsified
        .cipher_dec_key_gen_ni     ( sp_in_cipher_dec_key_gen[i]   ), // Sparsified
        .cipher_prng_reseed_o      ( mr_cipher_prng_reseed[i]      ), // OR-combine
        .cipher_prng_reseed_i      ( cipher_prng_reseed_i          ),
        .cipher_key_clear_o        ( mr_cipher_key_clear[i]        ), // OR-combine
        .cipher_key_clear_i        ( cipher_key_clear_i            ),
        .cipher_data_out_clear_o   ( mr_cipher_data_out_clear[i]   ), // OR-combine
        .cipher_data_out_clear_i   ( cipher_data_out_clear_i       ),

        .key_init_sel_o            ( mr_key_init_sel[i]            ), // OR-combine
        .key_init_we_no            ( int_key_init_we[i]            ), // Sparsified

        .iv_sel_o                  ( mr_iv_sel[i]                  ), // OR-combine
        .iv_we_no                  ( int_iv_we[i]                  ), // Sparsified

        .prng_data_req_o           ( mr_prng_data_req[i]           ), // OR-combine
        .prng_data_ack_i           ( prng_data_ack_i               ),
        .prng_reseed_req_o         ( mr_prng_reseed_req[i]         ), // OR-combine
        .prng_reseed_ack_i         ( prng_reseed_ack_i             ),

        .start_we_o                ( mr_start_we[i]                ), // OR-combine
        .key_iv_data_in_clear_we_o ( mr_key_iv_data_in_clear_we[i] ), // AND-combine
        .data_out_clear_we_o       ( mr_data_out_clear_we[i]       ), // AND-combine
        .prng_reseed_o             ( mr_prng_reseed[i]             ), // OR-combine
        .prng_reseed_we_o          ( mr_prng_reseed_we[i]          ), // OR-combine

        .idle_o                    ( mr_idle[i]                    ), // AND-combine
        .idle_we_o                 ( mr_idle_we[i]                 ), // AND-combine
        .stall_o                   ( mr_stall[i]                   ), // AND-combine
        .stall_we_o                ( mr_stall_we[i]                ), // AND-combine
        .output_lost_i             ( output_lost_i                 ), // AND-combine
        .output_lost_o             ( mr_output_lost[i]             ), // AND-combine
        .output_lost_we_o          ( mr_output_lost_we[i]          ), // AND-combine
        .output_valid_o            ( mr_output_valid[i]            ), // AND-combine
        .output_valid_we_o         ( mr_output_valid_we[i]         ), // AND-combine
        .input_ready_o             ( mr_input_ready[i]             ), // AND-combine
        .input_ready_we_o          ( mr_input_ready_we[i]          )  // AND-combine
      );
    end
  end

  // Convert sparsified outputs to sp2v_e type.
  assign data_out_we_o        = sp2v_e'(sp_data_out_we);
  assign data_in_prev_we_o    = sp2v_e'(sp_data_in_prev_we);
  assign ctr_incr_o           = sp2v_e'(sp_ctr_incr);
  assign cipher_in_valid_o    = sp2v_e'(sp_cipher_in_valid);
  assign cipher_out_ready_o   = sp2v_e'(sp_cipher_out_ready);
  assign cipher_crypt_o       = sp2v_e'(sp_out_cipher_crypt);
  assign cipher_dec_key_gen_o = sp2v_e'(sp_out_cipher_dec_key_gen);

  // Combine single-bit FSM outputs.
  // OR: One bit is sufficient to drive the corresponding output bit high.
  assign alert_o                   = |mr_alert;
  assign cipher_prng_reseed_o      = |mr_cipher_prng_reseed;
  assign cipher_key_clear_o        = |mr_cipher_key_clear;
  assign cipher_data_out_clear_o   = |mr_cipher_data_out_clear;
  assign prng_data_req_o           = |mr_prng_data_req;
  assign prng_reseed_req_o         = |mr_prng_reseed_req;
  assign start_we_o                = |mr_start_we;
  assign prng_reseed_o             = |mr_prng_reseed;
  assign prng_reseed_we_o          = |mr_prng_reseed_we;

  // AND: Only if all bits are high, the corresponding action should be triggered.
  assign ctrl_we_o                 = &mr_ctrl_we;
  assign data_in_we_o              = &mr_data_in_we;
  assign key_iv_data_in_clear_we_o = &mr_key_iv_data_in_clear_we;
  assign data_out_clear_we_o       = &mr_data_out_clear_we;
  assign idle_o                    = &mr_idle;
  assign idle_we_o                 = &mr_idle_we;
  assign stall_o                   = &mr_stall;
  assign stall_we_o                = &mr_stall_we;
  assign output_lost_o             = &mr_output_lost;
  assign output_lost_we_o          = &mr_output_lost_we;
  assign output_valid_o            = &mr_output_valid;
  assign output_valid_we_o         = &mr_output_valid_we;
  assign input_ready_o             = &mr_input_ready;
  assign input_ready_we_o          = &mr_input_ready_we;

  // Combine multi-bit, sparse FSM outputs. We simply OR them together. If the FSMs don't provide
  // the same outputs, two cases are possible:
  // - An invalid encoding results: A downstream checker will fire, see mux_sel_err_i.
  // - A valid encoding results: The outputs are compared below to cover this case, see mr_err;
  always_comb begin : combine_sparse_signals
    data_in_prev_sel_o  = dip_sel_e'({DIPSelWidth{1'b0}});
    state_in_sel_o      = si_sel_e'({SISelWidth{1'b0}});
    add_state_in_sel_o  = add_si_sel_e'({AddSISelWidth{1'b0}});
    add_state_out_sel_o = add_so_sel_e'({AddSOSelWidth{1'b0}});
    key_init_sel_o      = key_init_sel_e'({KeyInitSelWidth{1'b0}});
    iv_sel_o            = iv_sel_e'({IVSelWidth{1'b0}});
    mr_err              = 1'b0;

    for (int i = 0; i < Sp2VWidth; i++) begin
      data_in_prev_sel_o  = dip_sel_e'({data_in_prev_sel_o}     | {mr_data_in_prev_sel[i]});
      state_in_sel_o      = si_sel_e'({state_in_sel_o}          | {mr_state_in_sel[i]});
      add_state_in_sel_o  = add_si_sel_e'({add_state_in_sel_o}  | {mr_add_state_in_sel[i]});
      add_state_out_sel_o = add_so_sel_e'({add_state_out_sel_o} | {mr_add_state_out_sel[i]});
      key_init_sel_o      = key_init_sel_e'({key_init_sel_o}    | {mr_key_init_sel[i]});
      iv_sel_o            = iv_sel_e'({iv_sel_o}                | {mr_iv_sel[i]});
    end

    for (int i = 0; i < Sp2VWidth; i++) begin
      if (data_in_prev_sel_o  != mr_data_in_prev_sel[i]  ||
          state_in_sel_o      != mr_state_in_sel[i]      ||
          add_state_in_sel_o  != mr_add_state_in_sel[i]  ||
          add_state_out_sel_o != mr_add_state_out_sel[i] ||
          key_init_sel_o      != mr_key_init_sel[i]      ||
          iv_sel_o            != mr_iv_sel[i]) begin
        mr_err = 1'b1;
      end
    end
  end

  // Collect errors in mux selector signals.
  assign mux_sel_err = mux_sel_err_i | mr_err;

  //////////////////////////////
  // Sparsely Encoded Signals //
  //////////////////////////////

  // SEC_CM: CTRL.SPARSE
  // We use sparse encodings for various critical signals and must ensure that:
  // 1. The synthesis tool doesn't optimize away the sparse encoding.
  // 2. The sparsely encoded signal is always valid. More precisely, an alert or SVA is triggered
  //    if a sparse signal takes on an invalid value.
  // 3. The alert signal remains asserted until reset even if the sparse signal becomes valid again
  //    This is achieved by driving the control FSM into the terminal error state whenever any
  //    sparsely encoded signal becomes invalid.
  //
  // If any sparsely encoded signal becomes invalid, the controller further immediately de-asserts
  // data_out_we_o and other write-enable signals to prevent any data from being released.

  // We use vectors of sparsely encoded signals to reduce code duplication.
  localparam int unsigned NumSp2VSig = 5 + NumSlicesCtr;
  sp2v_e [NumSp2VSig-1:0]                sp2v_sig;
  sp2v_e [NumSp2VSig-1:0]                sp2v_sig_chk;
  logic  [NumSp2VSig-1:0][Sp2VWidth-1:0] sp2v_sig_chk_raw;
  logic  [NumSp2VSig-1:0]                sp2v_sig_err;

  assign sp2v_sig[0] = cipher_in_ready_i;
  assign sp2v_sig[1] = cipher_out_valid_i;
  assign sp2v_sig[2] = cipher_crypt_i;
  assign sp2v_sig[3] = cipher_dec_key_gen_i;
  assign sp2v_sig[4] = ctr_ready_i;
  for (genvar i = 0; i < NumSlicesCtr; i++) begin : gen_use_ctr_we_i
    assign sp2v_sig[5+i] = ctr_we_i[i];
  end

  // All signals inside sp2v_sig are driven and consumed by multi-rail FSMs.
  localparam bit [NumSp2VSig-1:0] Sp2VEnSecBuf = '0;

  // Individually check sparsely encoded signals.
  for (genvar i = 0; i < NumSp2VSig; i++) begin : gen_sel_buf_chk
    aes_sel_buf_chk #(
      .Num      ( Sp2VNum         ),
      .Width    ( Sp2VWidth       ),
      .EnSecBuf ( Sp2VEnSecBuf[i] )
    ) u_aes_sp2v_sig_buf_chk_i (
      .clk_i  ( clk_i               ),
      .rst_ni ( rst_ni              ),
      .sel_i  ( sp2v_sig[i]         ),
      .sel_o  ( sp2v_sig_chk_raw[i] ),
      .err_o  ( sp2v_sig_err[i]     )
    );
    assign sp2v_sig_chk[i] = sp2v_e'(sp2v_sig_chk_raw[i]);
  end

  assign cipher_in_ready    = sp2v_sig_chk[0];
  assign cipher_out_valid   = sp2v_sig_chk[1];
  assign cipher_crypt       = sp2v_sig_chk[2];
  assign cipher_dec_key_gen = sp2v_sig_chk[3];
  assign ctr_ready          = sp2v_sig_chk[4];
  for (genvar i = 0; i < NumSlicesCtr; i++) begin : gen_ctr_we
    assign ctr_we[i]        = sp2v_sig_chk[5+i];
  end

  // Collect encoding errors.
  // We instantiate the checker modules as close as possible to where the sparsely encoded signals
  // are used. Here, we collect also encoding errors detected in other places of the core.
  assign sp_enc_err = |sp2v_sig_err | sp_enc_err_i;

  //////////////////////
  // Trigger Register //
  //////////////////////
  // Most triggers are only ever cleared by control.
  assign start_o                   = 1'b0;
  assign key_iv_data_in_clear_o    = 1'b0;
  assign data_out_clear_o          = 1'b0;

endmodule
