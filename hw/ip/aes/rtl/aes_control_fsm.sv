// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES main control FSM
//
// This module contains the main control FSM handling the interplay of input/output registers and
// the AES cipher core.

`include "prim_assert.sv"

module aes_control_fsm
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

  // Signals
  aes_ctrl_e                aes_ctrl_ns, aes_ctrl_cs;
  logic                     prng_reseed_done_d, prng_reseed_done_q;

  logic                     key_init_clear;
  logic                     key_init_new;
  logic                     key_init_new_pulse;
  logic                     key_init_load;
  logic                     key_init_arm;
  logic                     key_init_ready;
  logic                     key_sideload;

  logic  [NumSlicesCtr-1:0] iv_qe;
  logic                     iv_clear;
  logic                     iv_load;
  logic                     iv_arm;
  logic                     iv_ready;

  logic   [NumRegsData-1:0] data_in_new_d, data_in_new_q;
  logic                     data_in_new;
  logic                     data_in_load;

  logic   [NumRegsData-1:0] data_out_read_d, data_out_read_q;
  logic                     data_out_read;
  logic                     output_valid_q;

  logic                     cfg_valid;
  logic                     no_alert;
  logic                     cipher_op_err;
  logic                     start_common, start_ecb, start_cbc, start_cfb, start_ofb, start_ctr;
  logic                     start;
  logic                     start_core;
  logic                     finish;
  logic                     crypt;
  logic                     cipher_out_done;
  logic                     doing_cbc_enc, doing_cbc_dec;
  logic                     doing_cfb_enc, doing_cfb_dec;
  logic                     doing_ofb;
  logic                     doing_ctr;
  logic                     ctrl_we_q;
  logic                     clear_in_out_status;
  logic                     clear_on_fatal;

  logic                     start_we;
  logic                     key_iv_data_in_clear_we;
  logic                     data_out_clear_we;
  logic                     prng_reseed_we;

  logic                     idle;
  logic                     idle_we;
  logic                     stall;
  logic                     stall_we;
  logic                     output_lost;
  logic                     output_lost_we;
  logic                     output_valid;
  logic                     output_valid_we;
  logic                     input_ready;
  logic                     input_ready_we;

  logic                     block_ctr_expr;
  logic                     block_ctr_decr;

  // Software updates IV in chunks of 32 bits, the counter updates SliceSizeCtr bits at a time.
  // Convert word write enable to internal half-word write enable.
  assign iv_qe = {iv_qe_i[3], iv_qe_i[3], iv_qe_i[2], iv_qe_i[2],
                  iv_qe_i[1], iv_qe_i[1], iv_qe_i[0], iv_qe_i[0]};

  // The cipher core is only ever allowed to start or finish if the control register holds a valid
  // configuration and if no fatal alert condition occured.
  assign cfg_valid = ~((mode_i == AES_NONE) | ctrl_err_storage_i);
  assign no_alert  = ~alert_fatal_i;

  // cipher_op_i is obtained from the configuration of the control register with additional logic.
  assign cipher_op_err = ~(cipher_op_i == CIPH_FWD || cipher_op_i == CIPH_INV);

  // Check common start conditions. These are needed for any mode, unless we are running in
  // manual mode.
  assign start_common = key_init_ready & data_in_new &
      // If key sideload is enabled, we only start if the key is valid.
      (sideload_i ? key_sideload_valid_i : 1'b1);

  // Check mode-specific start conditions. If the IV (and counter) is needed, we only start if
  // also the IV (and counter) is ready.
  assign start_ecb = (mode_i == AES_ECB);
  assign start_cbc = (mode_i == AES_CBC) & iv_ready;
  assign start_cfb = (mode_i == AES_CFB) & iv_ready;
  assign start_ofb = (mode_i == AES_OFB) & iv_ready;
  assign start_ctr = (mode_i == AES_CTR) & iv_ready & ctr_ready_i;

  // If set to start manually, we just wait for the trigger. Otherwise, check common as well as
  // mode-specific start conditions.
  assign start = cfg_valid & no_alert &
      // Manual operation has priority.
      (manual_operation_i ? start_i  :
          // Check start conditions for automatic operation.
          ((start_ecb |
            start_cbc |
            start_cfb |
            start_ofb |
            start_ctr) & start_common));

  // If not set to overwrite data, we wait for any previous output data to be read. data_out_read
  // synchronously clears output_valid_q, unless new output data is written in the exact same
  // clock cycle.
  assign finish = cfg_valid & no_alert &
      // Manual operation has priority.
      (manual_operation_i ? 1'b1 :
          // Make sure previous output data has been read.
          (~output_valid_q | data_out_read));

  // Helper signals for FSM
  assign crypt = cipher_crypt_o | cipher_crypt_i;

  assign doing_cbc_enc = (mode_i == AES_CBC && op_i == AES_ENC) & crypt;
  assign doing_cbc_dec = (mode_i == AES_CBC && op_i == AES_DEC) & crypt;
  assign doing_cfb_enc = (mode_i == AES_CFB && op_i == AES_ENC) & crypt;
  assign doing_cfb_dec = (mode_i == AES_CFB && op_i == AES_DEC) & crypt;
  assign doing_ofb     = (mode_i == AES_OFB)                    & crypt;
  assign doing_ctr     = (mode_i == AES_CTR)                    & crypt;

  // FSM
  always_comb begin : aes_ctrl_fsm

    // Previous input data register control
    data_in_prev_sel_o = DIP_CLEAR;
    data_in_prev_we_o  = 1'b0;

    // Cipher I/O mux control
    state_in_sel_o      = SI_DATA;
    add_state_in_sel_o  = ADD_SI_ZERO;
    add_state_out_sel_o = ADD_SO_ZERO;

    // Counter control
    ctr_incr_o = 1'b0;

    // Cipher core control
    cipher_in_valid_o       = 1'b0;
    cipher_out_ready_o      = 1'b0;
    cipher_out_done         = 1'b0;
    cipher_crypt_o          = 1'b0;
    cipher_dec_key_gen_o    = 1'b0;
    cipher_prng_reseed_o    = 1'b0;
    cipher_key_clear_o      = 1'b0;
    cipher_data_out_clear_o = 1'b0;

    // Initial key registers
    key_init_sel_o = sideload_i ? KEY_INIT_KEYMGR : KEY_INIT_INPUT;
    key_init_we_o = {NumSharesKey * NumRegsKey{1'b0}};

    // IV registers
    iv_sel_o = IV_INPUT;
    iv_we_o  = {NumSlicesCtr{1'b0}};

    // Control register
    ctrl_we_o = 1'b0;

    // Alert
    alert_o = 1'b0;

    // Pseudo-random number generator control
    prng_data_req_o   = 1'b0;
    prng_reseed_req_o = 1'b0;

    // Trigger register control
    start_we                = 1'b0;
    key_iv_data_in_clear_we = 1'b0;
    data_out_clear_we       = 1'b0;
    prng_reseed_we          = 1'b0;

    // Status register
    idle     = 1'b0;
    idle_we  = 1'b0;
    stall    = 1'b0;
    stall_we = 1'b0;

    // Key, data I/O register control
    data_in_load  = 1'b0;
    data_in_we_o  = 1'b0;
    data_out_we_o = 1'b0;

    // Register status tracker control
    key_init_clear = 1'b0;
    key_init_load  = 1'b0;
    key_init_arm   = 1'b0;
    iv_clear       = 1'b0;
    iv_load        = 1'b0;
    iv_arm         = 1'b0;

    // Block counter
    block_ctr_decr = 1'b0;

    // FSM
    aes_ctrl_ns        = aes_ctrl_cs;
    start_core         = 1'b0;
    prng_reseed_done_d = prng_reseed_done_q | prng_reseed_ack_i;

    unique case (aes_ctrl_cs)

      CTRL_IDLE: begin
        // The core is about to start encryption/decryption or another action.
        start_core = start | key_iv_data_in_clear_i | data_out_clear_i | prng_reseed_i;

        // Update status register. A write to the main control register (if sideload is enabled)
        // or writing the last key register can initiate a PRNG reseed operation via trigger
        // register. To avoid that subsequent writes to the main control, key or IV registers
        // collide with the start of the reseed operation, de-assert the idle bit.
        idle    = ~(start_core | (prng_reseed_o & prng_reseed_we_o));
        idle_we = 1'b1;

        // Clear the start trigger when seeing invalid configurations or performing automatic
        // operation.
        start_we = start_i & ((mode_i == AES_NONE) | ~manual_operation_i);

        if (!start_core) begin
          // Initial key and IV updates are ignored if the core is about to start. If key sideload
          // is enabled, software writes to the initial key registers are ignored.
          key_init_we_o = sideload_i ? {NumSharesKey * NumRegsKey{key_sideload}} : key_init_qe_i;
          iv_we_o       = iv_qe;

          // Updates to the control register are only allowed if the core is not about to start and
          // there isn't a storage error. A storage error is unrecoverable and requires a reset.
          ctrl_we_o      = !ctrl_err_storage_i ? ctrl_qe_i : 1'b0;

          // Control register updates clear all register status trackers.
          key_init_clear = ctrl_we_o;
          iv_clear       = ctrl_we_o;
        end

        if (prng_reseed_i) begin
          // PRNG reseeding has highest priority.
          if (!SecMasking) begin
            prng_reseed_done_d = 1'b0;
            aes_ctrl_ns        = CTRL_PRNG_RESEED;
          end else begin
            // In case masking is enabled, also the masking PRNG inside the cipher core needs to
            // be reseeded.
            cipher_prng_reseed_o = 1'b1;

            // Perform handshake.
            cipher_in_valid_o = 1'b1;
            if (cipher_in_ready_i) begin
              prng_reseed_done_d = 1'b0;
              aes_ctrl_ns        = CTRL_PRNG_RESEED;
            end
          end

        end else if (key_iv_data_in_clear_i || data_out_clear_i) begin
          // To clear registers, we must first request fresh pseudo-random data.
          aes_ctrl_ns = CTRL_PRNG_UPDATE;

        end else if (start) begin
          // Signal that we want to start encryption/decryption.
          cipher_crypt_o = 1'b1;

          // Signal if the cipher core shall reseed the masking PRNG.
          cipher_prng_reseed_o = block_ctr_expr;

          // We got a new initial key, but want to do decryption. The cipher core must first
          // generate the start key for decryption.
          cipher_dec_key_gen_o = (cipher_op_i == CIPH_INV) ? key_init_new : 1'b0;

          // Previous input data register control
          data_in_prev_sel_o = doing_cbc_dec ? DIP_DATA_IN :
                               doing_cfb_enc ? DIP_DATA_IN :
                               doing_cfb_dec ? DIP_DATA_IN :
                               doing_ofb     ? DIP_DATA_IN :
                               doing_ctr     ? DIP_DATA_IN : DIP_CLEAR;
          data_in_prev_we_o  = doing_cbc_dec |
                               doing_cfb_enc |
                               doing_cfb_dec |
                               doing_ofb     |
                               doing_ctr;

          // State input mux control
          state_in_sel_o     = doing_cfb_enc ? SI_ZERO :
                               doing_cfb_dec ? SI_ZERO :
                               doing_ofb     ? SI_ZERO :
                               doing_ctr     ? SI_ZERO : SI_DATA;

          // State input additon mux control
          add_state_in_sel_o = doing_cbc_enc ? ADD_SI_IV :
                               doing_cfb_enc ? ADD_SI_IV :
                               doing_cfb_dec ? ADD_SI_IV :
                               doing_ofb     ? ADD_SI_IV :
                               doing_ctr     ? ADD_SI_IV : ADD_SI_ZERO;

          // We have work for the cipher core, perform handshake.
          cipher_in_valid_o = 1'b1;
          if (cipher_in_ready_i) begin
            // Do not yet clear a possible start trigger if we are just starting the generation of
            // the start key for decryption.
            start_we    = ~cipher_dec_key_gen_o;
            aes_ctrl_ns = CTRL_LOAD;
          end
        end
      end

      CTRL_LOAD: begin
        // Signal that we have used the current key, IV, data input to register status tracking.
        key_init_load =  cipher_dec_key_gen_i; // This key is no longer "new", but still clean.
        key_init_arm  = ~cipher_dec_key_gen_i; // The key is still "new", prevent partial updates.
        iv_load       = ~cipher_dec_key_gen_i & (doing_cbc_enc |
                                                 doing_cbc_dec |
                                                 doing_cfb_enc |
                                                 doing_cfb_dec |
                                                 doing_ofb     |
                                                 doing_ctr);
        data_in_load  = ~cipher_dec_key_gen_i;

        // Trigger counter increment.
        ctr_incr_o   = doing_ctr;

        // Unless we are just generating the start key for decryption, we must update the PRNG.
        aes_ctrl_ns  = !cipher_dec_key_gen_i ? CTRL_PRNG_UPDATE : CTRL_FINISH;
      end

      CTRL_PRNG_UPDATE: begin
        // Fresh pseudo-random data is used to:
        // - clear the state in the final cipher round,
        // - clear any other registers in the CLEAR_I/CO states.

        // IV control in case of ongoing encryption/decryption
        // - CTR: IV registers are updated by counter during cipher operation
        iv_sel_o = doing_ctr ? IV_CTR   : IV_INPUT;
        iv_we_o  = doing_ctr ? ctr_we_i : {NumSlicesCtr{1'b0}};

        // Request fresh pseudo-random data, perform handshake.
        prng_data_req_o = 1'b1;
        if (prng_data_ack_i) begin

          // Ongoing encryption/decryption operations have the highest priority. The clear triggers
          // might have become asserted after the handshake with the cipher core.
          if (cipher_crypt_i) begin
            aes_ctrl_ns = CTRL_FINISH;

          end else if (key_iv_data_in_clear_i || data_out_clear_i) begin
            // To clear the output data registers, we re-use the muxing resources of the cipher
            // core. To clear all key material, some key registers inside the cipher core need to
            // be cleared.
            cipher_key_clear_o      = key_iv_data_in_clear_i;
            cipher_data_out_clear_o = data_out_clear_i;

            // We have work for the cipher core, perform handshake.
            cipher_in_valid_o = 1'b1;
            if (cipher_in_ready_i) begin
              aes_ctrl_ns = CTRL_CLEAR_I;
            end
          end else begin
            // Another write to the trigger register must have overwritten the trigger bits that
            // actually caused us to enter this state. Just return.
            aes_ctrl_ns = CTRL_IDLE;
          end // cipher_crypt_i
        end // prng_data_ack_i
      end

      CTRL_PRNG_RESEED: begin
        // Request a reseed of the clearing PRNG.
        prng_reseed_req_o = ~prng_reseed_done_q;

        if (!SecMasking) begin
          if (prng_reseed_done_q) begin
            // Clear the trigger and return.
            prng_reseed_we     = 1'b1;
            prng_reseed_done_d = 1'b0;
            aes_ctrl_ns        = CTRL_IDLE;
          end

        end else begin
          // In case masking is used, we must also wait for the cipher core to reseed the internal
          // masking PRNG. Perform handshake.
          cipher_out_ready_o = prng_reseed_done_q;
          if (cipher_out_ready_o && cipher_out_valid_i) begin
            // Clear the trigger and return.
            prng_reseed_we     = 1'b1;
            prng_reseed_done_d = 1'b0;
            aes_ctrl_ns        = CTRL_IDLE;
          end
        end
      end

      CTRL_FINISH: begin
        // Wait for cipher core to finish.

        if (cipher_dec_key_gen_i) begin
          // We are ready.
          cipher_out_ready_o = 1'b1;
          if (cipher_out_valid_i) begin
            block_ctr_decr = 1'b1;
            aes_ctrl_ns    = CTRL_IDLE;
          end
        end else begin
          // Handshake signals: We are ready once the output data registers can be written. Don't
          // let data propagate in case of mux selector or sparsely encoded signals taking on
          // invalid values.
          cipher_out_ready_o = finish;
          cipher_out_done    = finish & cipher_out_valid_i &
              ~mux_sel_err_i & ~sp_enc_err_i & ~cipher_op_err;

          // Signal if the cipher core is stalled (because previous output has not yet been read).
          stall    = ~finish & cipher_out_valid_i;
          stall_we = 1'b1;

          // State out addition mux control
          add_state_out_sel_o = doing_cbc_dec ? ADD_SO_IV  :
                                doing_cfb_enc ? ADD_SO_DIP :
                                doing_cfb_dec ? ADD_SO_DIP :
                                doing_ofb     ? ADD_SO_DIP :
                                doing_ctr     ? ADD_SO_DIP : ADD_SO_ZERO;

          // IV control
          // - CBC/CFB/OFB: IV registers are only updated when cipher finishes.
          // - CTR: IV registers are updated by counter during cipher operation.
          iv_sel_o = doing_cbc_enc ? IV_DATA_OUT     :
                     doing_cbc_dec ? IV_DATA_IN_PREV :
                     doing_cfb_enc ? IV_DATA_OUT     :
                     doing_cfb_dec ? IV_DATA_IN_PREV :
                     doing_ofb     ? IV_DATA_OUT_RAW :
                     doing_ctr     ? IV_CTR          : IV_INPUT;
          iv_we_o  = doing_cbc_enc ||
                     doing_cbc_dec ||
                     doing_cfb_enc ||
                     doing_cfb_dec ||
                     doing_ofb     ? {NumSlicesCtr{cipher_out_done}} :
                     doing_ctr     ? ctr_we_i                        : {NumSlicesCtr{1'b0}};

          // Arm the IV status tracker: After finishing, the IV registers can be written again
          // by software. We need to make sure software does not partially update the IV.
          iv_arm = (doing_cbc_enc |
                    doing_cbc_dec |
                    doing_cfb_enc |
                    doing_cfb_dec |
                    doing_ofb     |
                    doing_ctr) & cipher_out_done;

          // Proceed upon successful handshake.
          if (cipher_out_done) begin
            block_ctr_decr = 1'b1;
            data_out_we_o  = 1'b1;
            aes_ctrl_ns    = CTRL_IDLE;
          end
        end
      end

      CTRL_CLEAR_I: begin
        // Clear input registers such as Initial Key, IV and input data registers.
        if (key_iv_data_in_clear_i) begin
          // Initial Key
          key_init_sel_o = KEY_INIT_CLEAR;
          key_init_we_o  = {NumSharesKey * NumRegsKey{1'b1}};
          key_init_clear = 1'b1;

          // IV
          iv_sel_o = IV_CLEAR;
          iv_we_o  = {NumSlicesCtr{1'b1}};
          iv_clear = 1'b1;

          // Input data
          data_in_we_o       = 1'b1;
          data_in_prev_sel_o = DIP_CLEAR;
          data_in_prev_we_o  = 1'b1;
        end
        aes_ctrl_ns = CTRL_CLEAR_CO;
      end

      CTRL_CLEAR_CO: begin
        // Wait for cipher core to clear internal Full Key and Decryption Key registers and/or
        // the state register and clear output data registers afterwards.

        // Perform handshake with cipher core.
        cipher_out_ready_o = 1'b1;
        if (cipher_out_valid_i) begin

          // Full Key and Decryption Key registers are cleared by the cipher core.
          // key_iv_data_in_clear_i is acknowledged by the cipher core with cipher_key_clear_i.
          if (cipher_key_clear_i) begin
            // Clear the trigger bit.
            key_iv_data_in_clear_we = 1'b1;
          end

          // To clear the output data registers, we re-use the muxing resources of the cipher core.
          // data_out_clear_i is acknowledged by the cipher core with cipher_data_out_clear_i.
          if (cipher_data_out_clear_i) begin
            // Clear output data and the trigger bit. Don't release data from cipher core in case
            // of mux selector or sparsely encoded signals taking on invalid values.
            data_out_we_o     = ~mux_sel_err_i & ~sp_enc_err_i & ~cipher_op_err;
            data_out_clear_we = 1'b1;
          end

          aes_ctrl_ns = CTRL_IDLE;
        end
      end

      CTRL_ERROR: begin
        // SEC_CM: MAIN.FSM.GLOBAL_ESC
        // SEC_CM: MAIN.FSM.LOCAL_ESC
        // Terminal error state
        alert_o = 1'b1;
      end

      // We should never get here. If we do (e.g. via a malicious glitch), error out immediately.
      default: begin
        aes_ctrl_ns = CTRL_ERROR;
        alert_o = 1'b1;
      end
    endcase

    // Unconditionally jump into the terminal error state in case a mux selector or a sparsely
    // encoded signal becomes invalid, or if the life cycle controller triggers an escalation.
    if (mux_sel_err_i || sp_enc_err_i || cipher_op_err ||
            lc_escalate_en_i != lc_ctrl_pkg::Off) begin
      aes_ctrl_ns = CTRL_ERROR;
    end
  end

  // SEC_CM: MAIN.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, aes_ctrl_ns, aes_ctrl_cs, aes_ctrl_e, CTRL_IDLE)

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_fsm
    if (!rst_ni) begin
      prng_reseed_done_q <= 1'b0;
    end else begin
      prng_reseed_done_q <= prng_reseed_done_d;
    end
  end

  /////////////////////
  // Status Tracking //
  /////////////////////

  // We only take a new sideload key if sideload is enabled, if the provided sideload key is marked
  // as valid, and after the control register has been written for the second time. After that
  // point we don't update the key anymore, as we don't have a notion of when it actually changes.
  // This would be required to trigger decryption key generation for ECB/CBC decryption.
  // To update the sideload key, software has to:
  // 1) wait unitl AES is idle,
  // 2) wait for the key manager to provide the new key,
  // 3) start a new message by writing the control register and providing the IV (if needed).
  assign key_sideload = sideload_i & key_sideload_valid_i & ctrl_we_q & ~ctrl_phase_i;

  // We only use clean initial keys. Either software/counter has updated
  // - all initial key registers, or
  // - none of the initial key registers but the registers were updated in the past.
  aes_reg_status #(
    .Width ( $bits(key_init_we_o) )
  ) u_reg_status_key_init (
    .clk_i       ( clk_i              ),
    .rst_ni      ( rst_ni             ),
    .we_i        ( key_init_we_o      ),
    .use_i       ( key_init_load      ),
    .clear_i     ( key_init_clear     ),
    .arm_i       ( key_init_arm       ),
    .new_o       ( key_init_new       ),
    .new_pulse_o ( key_init_new_pulse ),
    .clean_o     ( key_init_ready     )
  );

  // We only use clean and unused IVs. Either software/counter has updated
  // - all IV registers, or
  // - none of the IV registers but the registers were updated in the past
  // and this particular IV has not yet been used.
  aes_reg_status #(
    .Width ( $bits(iv_we_o) )
  ) u_reg_status_iv (
    .clk_i       ( clk_i    ),
    .rst_ni      ( rst_ni   ),
    .we_i        ( iv_we_o  ),
    .use_i       ( iv_load  ),
    .clear_i     ( iv_clear ),
    .arm_i       ( iv_arm   ),
    .new_o       ( iv_ready ),
    .new_pulse_o (          ),
    .clean_o     (          )
  );

  // Input and output data register status tracking detects if:
  // - A complete new data input block is available, and
  // - An output data block has been read completely.
  // The status tracking needs to be cleared upon writes to the control register. The clearing is
  // applied one cycle later here to avoid zero-latency loops. This additional delay is not
  // relevant as if we are about to start encryption/decryption, we anyway don't allow writes
  // to the control register.
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_ctrl_we
    if (!rst_ni) begin
      ctrl_we_q <= 1'b0;
    end else begin
      ctrl_we_q <= ctrl_we_o;
    end
  end
  assign clear_in_out_status = ctrl_we_q;

  // Collect writes to data input registers. Cleared if:
  // - data is loaded into cipher core,
  // - clearing data input registers with random data (all data_in_qe_i bits high in next cycle),
  // - clearing the status tracking.
  assign data_in_new_d = data_in_load || &data_in_qe_i || clear_in_out_status ? '0 :
      data_in_new_q | data_in_qe_i;
  assign data_in_new   = &data_in_new_d;

  // Collect reads of data output registers. data_out_read is high for one clock cycle only and
  // clears output_valid_q unless new output is written in the exact same cycle. Cleared if:
  // - clearing data ouput registers with random data,
  // - clearing the status tracking.
  assign data_out_read_d = &data_out_read_q || clear_in_out_status ? '0 :
      data_out_read_q | data_out_re_i;
  assign data_out_read   = &data_out_read_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_edge_detection
    if (!rst_ni) begin
      data_in_new_q   <= '0;
      data_out_read_q <= '0;
    end else begin
      data_in_new_q   <= data_in_new_d;
      data_out_read_q <= data_out_read_d;
    end
  end

  // Status register bits for data input and output
  // Cleared to 1 if:
  // - data is loaded into cipher core,
  // - clearing data input registers with random data,
  // - clearing the status tracking.
  assign input_ready    = ~data_in_new;
  assign input_ready_we =  data_in_new | data_in_load | data_in_we_o | clear_in_out_status;

  // Cleared if:
  // - all data output registers have been read (unless new output is written in the same cycle),
  // - clearing data ouput registers with random data,
  // - clearing the status tracking.
  assign output_valid    = data_out_we_o & ~data_out_clear_we;
  assign output_valid_we = data_out_we_o | data_out_read | data_out_clear_we |
      clear_in_out_status;

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_output_valid
    if (!rst_ni) begin
      output_valid_q <= '0;
    end else if (output_valid_we) begin
      output_valid_q <= output_valid;
    end
  end

  // Output lost status register bit
  // Cleared when updating the Control Register. Set when overwriting previous output data that has
  // not yet been read.
  assign output_lost    = ctrl_we_o     ? 1'b0 :
                          output_lost_i ? 1'b1 : output_valid_q & ~data_out_read;
  assign output_lost_we = ctrl_we_o | data_out_we_o;

  // Should fatal alerts clear the status and trigger register?
  assign clear_on_fatal = ClearStatusOnFatalAlert ? alert_fatal_i : 1'b0;

  /////////////////////
  // Status Register //
  /////////////////////
  assign idle_o            = clear_on_fatal ? 1'b0 : idle;
  assign idle_we_o         = clear_on_fatal ? 1'b1 : idle_we;
  assign stall_o           = clear_on_fatal ? 1'b0 : stall;
  assign stall_we_o        = clear_on_fatal ? 1'b1 : stall_we;
  assign output_lost_o     = clear_on_fatal ? 1'b0 : output_lost;
  assign output_lost_we_o  = clear_on_fatal ? 1'b1 : output_lost_we;
  assign output_valid_o    = clear_on_fatal ? 1'b0 : output_valid;
  assign output_valid_we_o = clear_on_fatal ? 1'b1 : output_valid_we;
  assign input_ready_o     = clear_on_fatal ? 1'b0 : input_ready;
  assign input_ready_we_o  = clear_on_fatal ? 1'b1 : input_ready_we;

  //////////////////////
  // Trigger Register //
  //////////////////////
  // Most triggers are only ever cleared by control. Fatal alerts clear all bits in the trigger
  // register.
  assign start_we_o                = clear_on_fatal ? 1'b1 : start_we;
  assign key_iv_data_in_clear_we_o = clear_on_fatal ? 1'b1 : key_iv_data_in_clear_we;
  assign data_out_clear_we_o       = clear_on_fatal ? 1'b1 : data_out_clear_we;

  // If configured, trigger the reseeding of the PRNGs used for clearing and masking purposes after
  // the key has been updated.
  assign prng_reseed_o    = clear_on_fatal     ? 1'b0 :
                            key_init_new_pulse ? 1'b1 : 1'b0;
  assign prng_reseed_we_o = clear_on_fatal     ? 1'b1                      :
                            key_init_new_pulse ? key_touch_forces_reseed_i : prng_reseed_we;

  ////////////////////////////
  // PRNG Reseeding Counter //
  ////////////////////////////
  // Count the number of blocks since the start of the message to determine when the masking PRNG
  // inside the cipher core needs to be reseeded.
  if (SecMasking) begin : gen_block_ctr
    logic                     block_ctr_set;
    logic [BlockCtrWidth-1:0] block_ctr_d, block_ctr_q;
    logic [BlockCtrWidth-1:0] block_ctr_set_val, block_ctr_decr_val;

    assign block_ctr_expr = block_ctr_q == '0;
    assign block_ctr_set  = ctrl_we_q | (block_ctr_decr & (block_ctr_expr | cipher_prng_reseed_i));

    assign block_ctr_set_val  = prng_reseed_rate_i == PER_1  ? '0                   :
                                prng_reseed_rate_i == PER_64 ? BlockCtrWidth'(63)   :
                                prng_reseed_rate_i == PER_8K ? BlockCtrWidth'(8191) : '0;

    assign block_ctr_decr_val = block_ctr_q - BlockCtrWidth'(1);

    assign block_ctr_d = block_ctr_set  ? block_ctr_set_val  :
                         block_ctr_decr ? block_ctr_decr_val : block_ctr_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin : reg_block_ctr
      if (!rst_ni) begin
        block_ctr_q <= '0;
      end else begin
        block_ctr_q <= block_ctr_d;
      end
    end

  end else begin : gen_no_block_ctr
    assign block_ctr_expr = 1'b0;

    // Tie off unused signals.
    logic      unused_block_ctr_decr;
    prs_rate_e unused_prng_reseed_rate;
    logic      unused_cipher_prng_reseed;
    assign unused_block_ctr_decr     = block_ctr_decr;
    assign unused_prng_reseed_rate   = prng_reseed_rate_i;
    assign unused_cipher_prng_reseed = cipher_prng_reseed_i;
  end

  ////////////////
  // Assertions //
  ////////////////

  // Create a lint error to reduce the risk of accidentally disabling the masking.
  `ASSERT_STATIC_LINT_ERROR(AesControlFsmSecMaskingNonDefault, SecMasking == 1)

  // Selectors must be known/valid
  `ASSERT(AesModeValid, !ctrl_err_storage_i |-> mode_i inside {
      AES_ECB,
      AES_CBC,
      AES_CFB,
      AES_OFB,
      AES_CTR,
      AES_NONE
      })
  `ASSERT(AesOpValid, !ctrl_err_storage_i |-> op_i inside {
      AES_ENC,
      AES_DEC
      })
  `ASSERT(AesCiphOpValid, !cipher_op_err |-> cipher_op_i inside {
      CIPH_FWD,
      CIPH_INV
      })
  `ASSERT(AesControlStateValid, !alert_o |-> aes_ctrl_cs inside {
      CTRL_IDLE,
      CTRL_LOAD,
      CTRL_PRNG_UPDATE,
      CTRL_PRNG_RESEED,
      CTRL_FINISH,
      CTRL_CLEAR_I,
      CTRL_CLEAR_CO
      })

  // Check parameters
  `ASSERT_INIT(AesNumSlicesCtr, NumSlicesCtr == 8)

endmodule
