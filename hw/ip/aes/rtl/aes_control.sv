// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES main control
//
// This module controls the interplay of input/output registers and the AES cipher core.

`include "prim_assert.sv"

module aes_control import aes_pkg::*;
#(
  parameter int unsigned SecStartTriggerDelay = 0
) (
  input  logic                    clk_i,
  input  logic                    rst_ni,

  // Main control signals
  input  logic                    ctrl_qe_i,
  output logic                    ctrl_we_o,
  input  logic                    ctrl_err_storage_i,
  input  aes_op_e                 op_i,
  input  aes_mode_e               mode_i,
  input  ciph_op_e                cipher_op_i,
  input  logic                    manual_operation_i,
  input  logic                    start_i,
  input  logic                    key_iv_data_in_clear_i,
  input  logic                    data_out_clear_i,
  input  logic                    prng_reseed_i,
  input  logic                    mux_sel_err_i,
  input  logic                    sp_enc_err_i,
  input  lc_ctrl_pkg::lc_tx_t     lc_escalate_en_i,
  input  logic                    alert_fatal_i,
  output logic                    alert_o,

  // I/O register read/write enables
  input  logic [7:0]              key_init_qe_i [2],
  input  logic [3:0]              iv_qe_i,
  input  logic [3:0]              data_in_qe_i,
  input  logic [3:0]              data_out_re_i,
  output logic                    data_in_we_o,
  output sp2v_e                   data_out_we_o,

  // Previous input data register
  output dip_sel_e                data_in_prev_sel_o,
  output sp2v_e                   data_in_prev_we_o,

  // Cipher I/O muxes
  output si_sel_e                 state_in_sel_o,
  output add_si_sel_e             add_state_in_sel_o,
  output add_so_sel_e             add_state_out_sel_o,

  // Counter
  output sp2v_e                   ctr_incr_o,
  input  sp2v_e                   ctr_ready_i,
  input  sp2v_e [7:0]             ctr_we_i,

  // Cipher core control and sync
  output sp2v_e                   cipher_in_valid_o,
  input  sp2v_e                   cipher_in_ready_i,
  input  sp2v_e                   cipher_out_valid_i,
  output sp2v_e                   cipher_out_ready_o,
  output sp2v_e                   cipher_crypt_o,
  input  sp2v_e                   cipher_crypt_i,
  output sp2v_e                   cipher_dec_key_gen_o,
  input  sp2v_e                   cipher_dec_key_gen_i,
  output logic                    cipher_key_clear_o,
  input  logic                    cipher_key_clear_i,
  output logic                    cipher_data_out_clear_o,
  input  logic                    cipher_data_out_clear_i,

  // Initial key registers
  output key_init_sel_e           key_init_sel_o,
  output sp2v_e [7:0]             key_init_we_o [2],

  // IV registers
  output iv_sel_e                 iv_sel_o,
  output sp2v_e [7:0]             iv_we_o,

  // Pseudo-random number generator interface
  output logic                    prng_data_req_o,
  input  logic                    prng_data_ack_i,
  output logic                    prng_reseed_req_o,
  input  logic                    prng_reseed_ack_i,

  // Trigger register
  output logic                    start_o,
  output logic                    start_we_o,
  output logic                    key_iv_data_in_clear_o,
  output logic                    key_iv_data_in_clear_we_o,
  output logic                    data_out_clear_o,
  output logic                    data_out_clear_we_o,
  output logic                    prng_reseed_o,
  output logic                    prng_reseed_we_o,

  // Status register
  output logic                    output_valid_o,
  output logic                    output_valid_we_o,
  output logic                    input_ready_o,
  output logic                    input_ready_we_o,
  output logic                    idle_o,
  output logic                    idle_we_o,
  output logic                    stall_o,
  output logic                    stall_we_o,
  input  logic                    output_lost_i,
  output logic                    output_lost_o,
  output logic                    output_lost_we_o
);

  import aes_pkg::*;

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 7 -n 6 \
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
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 5
  //
  localparam int StateWidth = 6;
  typedef enum logic [StateWidth-1:0] {
    IDLE        = 6'b111100,
    LOAD        = 6'b101001,
    PRNG_UPDATE = 6'b010000,
    PRNG_RESEED = 6'b100010,
    FINISH      = 6'b011011,
    CLEAR       = 6'b110111,
    ERROR       = 6'b001110
  } aes_ctrl_e;

  aes_ctrl_e aes_ctrl_ns, aes_ctrl_cs;

  // Signals
  aes_mode_e   mode;
  logic        key_init_clear;
  sp2v_e       key_init_new, key_init_new_chk;
  logic        key_init_load;
  logic        key_init_arm;
  sp2v_e       key_init_ready, key_init_ready_chk;

  logic  [7:0] iv_qe;
  logic        iv_clear;
  logic        iv_load;
  logic        iv_arm;
  sp2v_e       iv_ready, iv_ready_chk;

  logic  [3:0] data_in_new_d, data_in_new_q;
  sp2v_e       data_in_new, data_in_new_chk;
  logic        data_in_load;

  logic  [3:0] data_out_read_d, data_out_read_q;
  sp2v_e       data_out_read, data_out_read_chk;
  sp2v_e       output_valid_d, output_valid_q;

  logic        start_trigger;
  logic        cfg_valid;
  logic        no_alert;
  sp2v_e       start_common, start_ecb, start_cbc, start_cfb, start_ofb, start_ctr;
  sp2v_e       start, start_chk;
  sp2v_e       finish, finish_chk;
  sp2v_e       crypt, crypt_chk;
  sp2v_e       cipher_out_done, cipher_out_done_chk;
  logic        cipher_out_done_err_d, cipher_out_done_err_q;
  sp2v_e       doing_cbc_enc, doing_cbc_enc_chk, doing_cbc_dec, doing_cbc_dec_chk;
  sp2v_e       doing_cfb_enc, doing_cfb_enc_chk, doing_cfb_dec, doing_cfb_dec_chk;
  sp2v_e       doing_ofb, doing_ofb_chk;
  sp2v_e       doing_ctr, doing_ctr_chk;
  logic        ctrl_we_q;
  sp2v_e       ctr_ready;
  sp2v_e [7:0] ctr_we;
  logic        clear_in_out_status;
  sp2v_e       cipher_in_ready;
  sp2v_e       cipher_out_valid;
  sp2v_e       cipher_crypt;
  sp2v_e       cipher_dec_key_gen;
  logic        sp_enc_err;

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

  // Software updates IV in chunks of 32 bits, the counter updates 16 bits at a time.
  // Convert word write enable to internal half-word write enable.
  assign iv_qe = {iv_qe_i[3], iv_qe_i[3], iv_qe_i[2], iv_qe_i[2],
                  iv_qe_i[1], iv_qe_i[1], iv_qe_i[0], iv_qe_i[0]};

  // The cipher core is only ever allowed to start or finish if the control register holds a valid
  // configuration and if no fatal alert condition occured.
  assign cfg_valid = ~((mode == AES_NONE) | ctrl_err_storage_i);
  assign no_alert  = ~alert_fatal_i;

  // Check common start conditions. These are needed for any mode, unless we are running in
  // manual mode.
  assign start_common = (key_init_ready_chk == SP2V_HIGH) ? data_in_new_chk : SP2V_LOW;

  // Check mode-specific start conditions. If the IV (and counter) is needed, we only start if
  // also the IV (and counter) is ready.
  assign start_ecb = (mode == AES_ECB)                                ? SP2V_HIGH : SP2V_LOW;
  assign start_cbc = (mode == AES_CBC && iv_ready_chk == SP2V_HIGH)   ? SP2V_HIGH : SP2V_LOW;
  assign start_cfb = (mode == AES_CFB && iv_ready_chk == SP2V_HIGH)   ? SP2V_HIGH : SP2V_LOW;
  assign start_ofb = (mode == AES_OFB && iv_ready_chk == SP2V_HIGH)   ? SP2V_HIGH : SP2V_LOW;
  assign start_ctr = (mode == AES_CTR && iv_ready_chk == SP2V_HIGH &&
                                              ctr_ready == SP2V_HIGH) ? SP2V_HIGH : SP2V_LOW;

  // If set to start manually, we just wait for the trigger. Otherwise, check common as well as
  // mode-specific start conditions.
  assign start =
      (cfg_valid && no_alert && (SP2V_HIGH ==
          // Manual operation has priority.
          (manual_operation_i      ? (start_trigger ? SP2V_HIGH : SP2V_LOW) :
          // Check start conditions for automatic operation.
          (start_ecb == SP2V_HIGH ||
           start_cbc == SP2V_HIGH ||
           start_cfb == SP2V_HIGH ||
           start_ofb == SP2V_HIGH ||
           start_ctr == SP2V_HIGH) ? start_common                           : SP2V_LOW))
      ) ? SP2V_HIGH : SP2V_LOW;

  // If not set to overwrite data, we wait for any previous output data to be read. data_out_read
  // synchronously clears output_valid_q, unless new output data is written in the exact same
  // clock cycle.
  assign finish =
      (cfg_valid && no_alert && (SP2V_HIGH ==
          // Manual operation has priority.
          (manual_operation_i              ? SP2V_HIGH :
          // Make sure previous output data has been read.
          (output_valid_q    == SP2V_LOW ||
           data_out_read_chk == SP2V_HIGH) ? SP2V_HIGH : SP2V_LOW))
      ) ? SP2V_HIGH : SP2V_LOW;

  // Helper signals for FSM
  assign crypt = (cipher_crypt_o == SP2V_HIGH ||
                  cipher_crypt_i == SP2V_HIGH) ? SP2V_HIGH : SP2V_LOW;

  assign doing_cbc_enc = (mode == AES_CBC && op_i == AES_ENC) ? crypt_chk : SP2V_LOW;
  assign doing_cbc_dec = (mode == AES_CBC && op_i == AES_DEC) ? crypt_chk : SP2V_LOW;
  assign doing_cfb_enc = (mode == AES_CFB && op_i == AES_ENC) ? crypt_chk : SP2V_LOW;
  assign doing_cfb_dec = (mode == AES_CFB && op_i == AES_DEC) ? crypt_chk : SP2V_LOW;
  assign doing_ofb     = (mode == AES_OFB)                    ? crypt_chk : SP2V_LOW;
  assign doing_ctr     = (mode == AES_CTR)                    ? crypt_chk : SP2V_LOW;

  // FSM
  always_comb begin : aes_ctrl_fsm

    // Previous input data register control
    data_in_prev_sel_o = DIP_CLEAR;
    data_in_prev_we_o  = SP2V_LOW;

    // Cipher I/O mux control
    state_in_sel_o      = SI_DATA;
    add_state_in_sel_o  = ADD_SI_ZERO;
    add_state_out_sel_o = ADD_SO_ZERO;

    // Counter control
    ctr_incr_o = SP2V_LOW;

    // Cipher core control
    cipher_in_valid_o       = SP2V_LOW;
    cipher_out_ready_o      = SP2V_LOW;
    cipher_out_done         = SP2V_LOW;
    cipher_crypt_o          = SP2V_LOW;
    cipher_dec_key_gen_o    = SP2V_LOW;
    cipher_key_clear_o      = 1'b0;
    cipher_data_out_clear_o = 1'b0;

    // Initial key registers
    key_init_sel_o = KEY_INIT_INPUT;
    key_init_we_o  = '{{8{SP2V_LOW}}, {8{SP2V_LOW}}};

    // IV registers
    iv_sel_o = IV_INPUT;
    iv_we_o  = {8{SP2V_LOW}};

    // Control register
    ctrl_we_o = 1'b0;

    // Alert
    alert_o = 1'b0;

    // Pseudo-random number generator control
    prng_data_req_o   = 1'b0;
    prng_reseed_req_o = 1'b0;

    // Trigger register control
    start_we_o                = 1'b0;
    key_iv_data_in_clear_we_o = 1'b0;
    data_out_clear_we_o       = 1'b0;
    prng_reseed_we_o          = 1'b0;

    // Status register
    idle_o     = 1'b0;
    idle_we_o  = 1'b0;
    stall_o    = 1'b0;
    stall_we_o = 1'b0;

    // Key, data I/O register control
    data_in_load  = 1'b0;
    data_in_we_o  = 1'b0;
    data_out_we_o = SP2V_LOW;

    // Register status tracker control
    key_init_clear = 1'b0;
    key_init_load  = 1'b0;
    key_init_arm   = 1'b0;
    iv_clear       = 1'b0;
    iv_load        = 1'b0;
    iv_arm         = 1'b0;

    // FSM
    aes_ctrl_ns = aes_ctrl_cs;

    unique case (aes_ctrl_cs)

      IDLE: begin
        idle_o    = (start_chk == SP2V_HIGH || key_iv_data_in_clear_i || data_out_clear_i ||
                    prng_reseed_i) ? 1'b0 : 1'b1;
        idle_we_o = 1'b1;

        if (idle_o) begin
          // Initial key and IV updates are ignored if we are not idle.
          for (int s = 0; s < 2; s++) begin
            for (int i = 0; i < 8; i++) begin
              key_init_we_o[s][i] = key_init_qe_i[s][i] ? SP2V_HIGH : SP2V_LOW;
            end
          end
          for (int i = 0; i < 8; i++) begin
            iv_we_o[i] = iv_qe[i] ? SP2V_HIGH : SP2V_LOW;
          end

          // Updates to the control register are only allowed if we are idle and we don't have a
          // storage error. A storage error is unrecoverable and requires a reset.
          ctrl_we_o      = !ctrl_err_storage_i ? ctrl_qe_i : 1'b0;

          // Control register updates clear all register status trackers.
          key_init_clear = ctrl_we_o;
          iv_clear       = ctrl_we_o;
        end

        if (prng_reseed_i) begin
          // PRNG reseeding has highest priority.
          aes_ctrl_ns = PRNG_RESEED;

        end else if (key_iv_data_in_clear_i || data_out_clear_i) begin
          // To clear registers, we must first request fresh pseudo-random data.
          aes_ctrl_ns = PRNG_UPDATE;

        end else if (start_chk == SP2V_HIGH) begin
          // Signal that we want to start encryption/decryption.
          cipher_crypt_o = SP2V_HIGH;

          // We got a new initial key, but want to do decryption. The cipher core must first
          // generate the start key for decryption.
          cipher_dec_key_gen_o = (cipher_op_i == CIPH_INV) ? key_init_new_chk : SP2V_LOW;

          // Previous input data register control
          data_in_prev_sel_o = (doing_cbc_dec_chk == SP2V_HIGH) ? DIP_DATA_IN :
                               (doing_cfb_enc_chk == SP2V_HIGH) ? DIP_DATA_IN :
                               (doing_cfb_dec_chk == SP2V_HIGH) ? DIP_DATA_IN :
                               (doing_ofb         == SP2V_HIGH) ? DIP_DATA_IN :
                               (doing_ctr         == SP2V_HIGH) ? DIP_DATA_IN : DIP_CLEAR;
          data_in_prev_we_o  = (doing_cbc_dec_chk == SP2V_HIGH) ? SP2V_HIGH :
                               (doing_cfb_enc_chk == SP2V_HIGH) ? SP2V_HIGH :
                               (doing_cfb_dec_chk == SP2V_HIGH) ? SP2V_HIGH :
                               (doing_ofb_chk     == SP2V_HIGH) ? SP2V_HIGH :
                               (doing_ctr_chk     == SP2V_HIGH) ? SP2V_HIGH : SP2V_LOW;

          // State input mux control
          state_in_sel_o     = (doing_cfb_enc_chk == SP2V_HIGH) ? SI_ZERO :
                               (doing_cfb_dec_chk == SP2V_HIGH) ? SI_ZERO :
                               (doing_ofb_chk     == SP2V_HIGH) ? SI_ZERO :
                               (doing_ctr_chk     == SP2V_HIGH) ? SI_ZERO : SI_DATA;

          // State input additon mux control
          add_state_in_sel_o = (doing_cbc_enc_chk == SP2V_HIGH) ? ADD_SI_IV :
                               (doing_cfb_enc_chk == SP2V_HIGH) ? ADD_SI_IV :
                               (doing_cfb_dec_chk == SP2V_HIGH) ? ADD_SI_IV :
                               (doing_ofb_chk     == SP2V_HIGH) ? ADD_SI_IV :
                               (doing_ctr_chk     == SP2V_HIGH) ? ADD_SI_IV : ADD_SI_ZERO;

          // We have work for the cipher core, perform handshake.
          cipher_in_valid_o = SP2V_HIGH;
          if (cipher_in_ready == SP2V_HIGH) begin
            // Do not yet clear a possible start trigger if we are just starting the generation of
            // the start key for decryption.
            start_we_o  = (cipher_dec_key_gen_o == SP2V_LOW);
            aes_ctrl_ns = LOAD;
          end
        end
      end

      LOAD: begin
        // Signal that we have used the current key, IV, data input to register status tracking.
        key_init_load = (cipher_dec_key_gen == SP2V_HIGH); // This key is no longer "new", but
                                                           // still clean.
        key_init_arm  = (cipher_dec_key_gen == SP2V_LOW);  // The key is still "new", prevent
                                                           // partial updates.
        iv_load       = (cipher_dec_key_gen == SP2V_HIGH) &
                            (doing_cbc_enc_chk == SP2V_HIGH | doing_cbc_dec_chk == SP2V_HIGH |
                             doing_cfb_enc_chk == SP2V_HIGH | doing_cfb_dec_chk == SP2V_HIGH |
                             doing_ofb_chk     == SP2V_HIGH | doing_ctr_chk     == SP2V_HIGH);
        data_in_load  = (cipher_dec_key_gen == SP2V_LOW);

        // Trigger counter increment.
        ctr_incr_o   = doing_ctr_chk;

        // Unless we are just generating the start key for decryption, we must update the PRNG.
        aes_ctrl_ns  = (cipher_dec_key_gen == SP2V_LOW) ? PRNG_UPDATE : FINISH;
      end

      PRNG_UPDATE: begin
        // Fresh pseudo-random data is used to:
        // - clear the state in the final cipher round,
        // - clear any other registers in the CLEAR state.

        // IV control in case of ongoing encryption/decryption
        // - CTR: IV registers are updated by counter during cipher operation
        iv_sel_o = (doing_ctr_chk == SP2V_HIGH) ? IV_CTR : IV_INPUT;
        iv_we_o  = (doing_ctr_chk == SP2V_HIGH) ? ctr_we : {8{SP2V_LOW}};

        // Request fresh pseudo-random data, perform handshake.
        prng_data_req_o = 1'b1;
        if (prng_data_ack_i) begin

          // Ongoing encryption/decryption operations have the highest priority. The clear triggers
          // might have become asserted after the handshake with the cipher core.
          if (cipher_crypt == SP2V_HIGH) begin
            aes_ctrl_ns = FINISH;

          end else begin // (key_iv_data_in_clear_i || data_out_clear_i)
            // To clear the output data registers, we re-use the muxing resources of the cipher
            // core. To clear all key material, some key registers inside the cipher core need to
            // be cleared.
            cipher_key_clear_o      = key_iv_data_in_clear_i;
            cipher_data_out_clear_o = data_out_clear_i;

            // We have work for the cipher core, perform handshake.
            cipher_in_valid_o = SP2V_HIGH;
            if (cipher_in_ready == SP2V_HIGH) begin
              aes_ctrl_ns = CLEAR;
            end
          end // cipher_crypt
        end // prng_data_ack_i
      end

      PRNG_RESEED: begin
        // Request a reseed of the PRNG, perform handshake.
        prng_reseed_req_o = 1'b1;
        if (prng_reseed_ack_i) begin
          // Clear the trigger and return.
          prng_reseed_we_o = 1'b1;
          aes_ctrl_ns      = IDLE;
        end
      end

      FINISH: begin
        // Wait for cipher core to finish.

        if (cipher_dec_key_gen == SP2V_HIGH) begin
          // We are ready.
          cipher_out_ready_o = SP2V_HIGH;
          if (cipher_out_valid == SP2V_HIGH) begin
            aes_ctrl_ns = IDLE;
          end
        end else begin
          // Handshake signals: We are ready once the output data registers can be written. Don't
          // let data propagate in case of mux selector or sparsely encoded signals taking on
          // invalid values.
          cipher_out_ready_o = finish_chk;
          cipher_out_done    = (finish_chk == SP2V_HIGH && cipher_out_valid == SP2V_HIGH &&
              !mux_sel_err_i && !sp_enc_err) ? SP2V_HIGH : SP2V_LOW;

          // Signal if the cipher core is stalled (because previous output has not yet been read).
          stall_o    = (finish_chk == SP2V_LOW) & (cipher_out_valid == SP2V_HIGH);
          stall_we_o = 1'b1;

          // State out addition mux control
          add_state_out_sel_o = (doing_cbc_dec_chk == SP2V_HIGH) ? ADD_SO_IV  :
                                (doing_cfb_enc_chk == SP2V_HIGH) ? ADD_SO_DIP :
                                (doing_cfb_dec_chk == SP2V_HIGH) ? ADD_SO_DIP :
                                (doing_ofb_chk     == SP2V_HIGH) ? ADD_SO_DIP :
                                (doing_ctr_chk     == SP2V_HIGH) ? ADD_SO_DIP : ADD_SO_ZERO;

          // IV control
          // - CBC/CFB/OFB: IV registers are only updated when cipher finishes.
          // - CTR: IV registers are updated by counter during cipher operation.
          iv_sel_o = (doing_cbc_enc_chk == SP2V_HIGH)  ? IV_DATA_OUT     :
                     (doing_cbc_dec_chk == SP2V_HIGH)  ? IV_DATA_IN_PREV :
                     (doing_cfb_enc_chk == SP2V_HIGH)  ? IV_DATA_OUT     :
                     (doing_cfb_dec_chk == SP2V_HIGH)  ? IV_DATA_IN_PREV :
                     (doing_ofb_chk     == SP2V_HIGH)  ? IV_DATA_OUT_RAW :
                     (doing_ctr_chk     == SP2V_HIGH)  ? IV_CTR          : IV_INPUT;
          iv_we_o  = (doing_cbc_enc_chk == SP2V_HIGH) ||
                     (doing_cbc_dec_chk == SP2V_HIGH) ||
                     (doing_cfb_enc_chk == SP2V_HIGH) ||
                     (doing_cfb_dec_chk == SP2V_HIGH) ||
                     (doing_ofb_chk     == SP2V_HIGH) ? {8{cipher_out_done_chk}} :
                     (doing_ctr_chk     == SP2V_HIGH) ? ctr_we                   : {8{SP2V_LOW}};

          // Arm the IV status tracker: After finishing, the IV registers can be written again
          // by software. We need to make sure software does not partially update the IV.
          iv_arm = (doing_cbc_enc_chk == SP2V_HIGH) ||
                   (doing_cbc_dec_chk == SP2V_HIGH) ||
                   (doing_cfb_enc_chk == SP2V_HIGH) ||
                   (doing_cfb_dec_chk == SP2V_HIGH) ||
                   (doing_ofb_chk     == SP2V_HIGH) ||
                   (doing_ctr_chk     == SP2V_HIGH) ? (cipher_out_done_chk == SP2V_HIGH) : 1'b0;

          // Proceed upon successful handshake.
          if (cipher_out_done_chk == SP2V_HIGH) begin
            data_out_we_o = SP2V_HIGH;
            aes_ctrl_ns   = IDLE;
          end
        end
      end

      CLEAR: begin
        // Initial Key, IV and input data registers can be cleared right away.
        if (key_iv_data_in_clear_i) begin
          // Initial Key
          key_init_sel_o = KEY_INIT_CLEAR;
          key_init_we_o  = '{{8{SP2V_HIGH}}, {8{SP2V_HIGH}}};
          key_init_clear = 1'b1;

          // IV
          iv_sel_o = IV_CLEAR;
          iv_we_o  = {8{SP2V_HIGH}};
          iv_clear = 1'b1;

          // Input data
          data_in_we_o       = 1'b1;
          data_in_prev_sel_o = DIP_CLEAR;
          data_in_prev_we_o  = SP2V_HIGH;
        end

        // Perform handshake with cipher core.
        cipher_out_ready_o = SP2V_HIGH;
        if (cipher_out_valid == SP2V_HIGH) begin

          // Full Key and Decryption Key registers are cleared by the cipher core.
          // key_iv_data_in_clear_i is acknowledged by the cipher core with cipher_key_clear_i.
          if (cipher_key_clear_i) begin
            // Clear the trigger bit.
            key_iv_data_in_clear_we_o = 1'b1;
          end

          // To clear the output data registers, we re-use the muxing resources of the cipher core.
          // data_out_clear_i is acknowledged by the cipher core with cipher_data_out_clear_i.
          if (cipher_data_out_clear_i) begin
            // Clear output data and the trigger bit. Don't release data from cipher core in case
            // of mux selector or sparsely encoded signals taking on invalid values.
            data_out_we_o       = (!mux_sel_err_i && !sp_enc_err) ? SP2V_HIGH : SP2V_LOW;
            data_out_clear_we_o = 1'b1;
          end

          aes_ctrl_ns = IDLE;
        end
      end

      ERROR: begin
        // Terminal error state
        alert_o = 1'b1;
      end

      // We should never get here. If we do (e.g. via a malicious glitch), error out immediately.
      default: begin
        aes_ctrl_ns = ERROR;
      end
    endcase

    // Unconditionally jump into the terminal error state in case a mux selector or a sparsely
    // encoded signal becomes invalid, or if the life cycle controller triggers an escalation.
    if (mux_sel_err_i || sp_enc_err || lc_escalate_en_i != lc_ctrl_pkg::Off) begin
      aes_ctrl_ns = ERROR;
    end
  end

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  logic [StateWidth-1:0] aes_ctrl_cs_raw;
  assign aes_ctrl_cs = aes_ctrl_e'(aes_ctrl_cs_raw);
  prim_flop #(
    .Width(StateWidth),
    .ResetValue(StateWidth'(IDLE))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .d_i ( aes_ctrl_ns     ),
    .q_o ( aes_ctrl_cs_raw )
  );

  /////////////////////
  // Status Tracking //
  /////////////////////

  // We only use clean initial keys. Either software/counter has updated
  // - all initial key registers, or
  // - none of the initial key registers but the registers were updated in the past.
  logic [7:0] key_init_we [2];
  for (genvar s = 0; s < 2; s++) begin : gen_status_key_init_we_shares
    for (genvar i = 0; i < 8; i++) begin : gen_status_key_init_we
      assign key_init_we[s][i] = (key_init_we_o[s][i] == SP2V_HIGH);
    end
  end
  aes_reg_status #(
    .Width ( $bits(key_init_we) )
  ) u_reg_status_key_init (
    .clk_i   ( clk_i                            ),
    .rst_ni  ( rst_ni                           ),
    .we_i    ( {key_init_we[1], key_init_we[0]} ),
    .use_i   ( key_init_load                    ),
    .clear_i ( key_init_clear                   ),
    .arm_i   ( key_init_arm                     ),
    .new_o   ( key_init_new                     ),
    .clean_o ( key_init_ready                   )
  );

  // We only use clean and unused IVs. Either software/counter has updated
  // - all IV registers, or
  // - none of the IV registers but the registers were updated in the past
  // and this particular IV has not yet been used.
  logic [7:0] iv_we;
  for (genvar i = 0; i < 8; i++) begin : gen_status_iv_we
    assign iv_we[i] = (iv_we_o[i] == SP2V_HIGH);
  end
  aes_reg_status #(
    .Width ( $bits(iv_we) )
  ) u_reg_status_iv (
    .clk_i   ( clk_i    ),
    .rst_ni  ( rst_ni   ),
    .we_i    ( iv_we    ),
    .use_i   ( iv_load  ),
    .clear_i ( iv_clear ),
    .arm_i   ( iv_arm   ),
    .new_o   ( iv_ready ),
    .clean_o (          )
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
  // - clearing data input registers with random data,
  // - clearing the status tracking.
  assign data_in_new_d = data_in_load || data_in_we_o || clear_in_out_status ? '0 :
      data_in_new_q | data_in_qe_i;
  assign data_in_new   = &data_in_new_d ? SP2V_HIGH : SP2V_LOW;

  // Collect reads of data output registers. data_out_read is high for one clock cycle only and
  // clears output_valid_q unless new output is written in the exact same cycle. Cleared if:
  // - clearing data ouput registers with random data,
  // - clearing the status tracking.
  assign data_out_read_d = &data_out_read_q || clear_in_out_status ? '0 :
      data_out_read_q | data_out_re_i;
  assign data_out_read   = &data_out_read_d ? SP2V_HIGH : SP2V_LOW;

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
  assign input_ready_o    = (data_in_new == SP2V_LOW);
  assign input_ready_we_o = (data_in_new == SP2V_HIGH) | data_in_load | data_in_we_o |
      clear_in_out_status;

  // Cleared if:
  // - all data output registers have been read (unless new output is written in the same cycle),
  // - clearing data ouput registers with random data,
  // - clearing the status tracking.
  assign output_valid_o    = (data_out_we_o == SP2V_HIGH) & ~data_out_clear_we_o;
  assign output_valid_we_o = (data_out_we_o == SP2V_HIGH) | (data_out_read_chk == SP2V_HIGH) |
      data_out_clear_we_o | clear_in_out_status;

  assign output_valid_d    = !output_valid_we_o ? output_valid_q :
                                 output_valid_o ? SP2V_HIGH      : SP2V_LOW;

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent optimizations on this status signal.
  logic [Sp2VWidth-1:0] output_valid_q_raw;
  prim_flop #(
    .Width      ( Sp2VWidth            ),
    .ResetValue ( Sp2VWidth'(SP2V_LOW) )
  ) u_crypt_regs (
    .clk_i  ( clk_i              ),
    .rst_ni ( rst_ni             ),
    .d_i    ( output_valid_d     ),
    .q_o    ( output_valid_q_raw )
  );

  // Output lost status register bit
  // Cleared when updating the Control Register. Set when overwriting previous output data that has
  // not yet been read.
  assign output_lost_o    = ctrl_we_o     ? 1'b0 :
                            output_lost_i ? 1'b1 :
                                (output_valid_q == SP2V_HIGH) & (data_out_read_chk == SP2V_LOW);
  assign output_lost_we_o = ctrl_we_o | (data_out_we_o == SP2V_HIGH);

  // Trigger register, the control only ever clears these
  assign start_o                = 1'b0;
  assign key_iv_data_in_clear_o = 1'b0;
  assign data_out_clear_o       = 1'b0;
  assign prng_reseed_o          = 1'b0;

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
  // If any sparsely encoded signal becomes invalid, the controller further immediately de-asserts
  // data_out_we_o and other write-enable signals to prevent any data from being released.

  // We use vectors of sparsely encoded signals to reduce code duplication.
  localparam int unsigned NumSp2VSig = 29;
  sp2v_e [NumSp2VSig-1:0]                sp2v_sig;
  sp2v_e [NumSp2VSig-1:0]                sp2v_sig_chk;
  logic  [NumSp2VSig-1:0][Sp2VWidth-1:0] sp2v_sig_chk_raw;
  logic  [NumSp2VSig-1:0]                sp2v_sig_err;

  assign sp2v_sig[0]  = cipher_in_ready_i;
  assign sp2v_sig[1]  = cipher_out_valid_i;
  assign sp2v_sig[2]  = cipher_crypt_i;
  assign sp2v_sig[3]  = cipher_dec_key_gen_i;
  assign sp2v_sig[4]  = crypt;
  assign sp2v_sig[5]  = doing_cbc_enc;
  assign sp2v_sig[6]  = doing_cbc_dec;
  assign sp2v_sig[7]  = doing_cfb_enc;
  assign sp2v_sig[8]  = doing_cfb_dec;
  assign sp2v_sig[9]  = doing_ofb;
  assign sp2v_sig[10] = doing_ctr;
  assign sp2v_sig[11] = key_init_new;
  assign sp2v_sig[12] = key_init_ready;
  assign sp2v_sig[13] = iv_ready;
  assign sp2v_sig[14] = data_in_new;
  assign sp2v_sig[15] = data_out_read;
  assign sp2v_sig[16] = sp2v_e'(output_valid_q_raw);
  assign sp2v_sig[17] = ctr_ready_i;
  assign sp2v_sig[18] = start;
  assign sp2v_sig[19] = finish;
  for (genvar i = 0; i < 8; i++) begin : gen_use_ctr_we_i
    assign sp2v_sig[20+i] = ctr_we_i[i];
  end
  assign sp2v_sig[28] = cipher_out_done;

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

  assign cipher_in_ready       = sp2v_sig_chk[0];
  assign cipher_out_valid      = sp2v_sig_chk[1];
  assign cipher_crypt          = sp2v_sig_chk[2];
  assign cipher_dec_key_gen    = sp2v_sig_chk[3];
  assign crypt_chk             = sp2v_sig_chk[4];
  assign doing_cbc_enc_chk     = sp2v_sig_chk[5];
  assign doing_cbc_dec_chk     = sp2v_sig_chk[6];
  assign doing_cfb_enc_chk     = sp2v_sig_chk[7];
  assign doing_cfb_dec_chk     = sp2v_sig_chk[8];
  assign doing_ofb_chk         = sp2v_sig_chk[9];
  assign doing_ctr_chk         = sp2v_sig_chk[10];
  assign key_init_new_chk      = sp2v_sig_chk[11];
  assign key_init_ready_chk    = sp2v_sig_chk[12];
  assign iv_ready_chk          = sp2v_sig_chk[13];
  assign data_in_new_chk       = sp2v_sig_chk[14];
  assign data_out_read_chk     = sp2v_sig_chk[15];
  assign output_valid_q        = sp2v_sig_chk[16];
  assign ctr_ready             = sp2v_sig_chk[17];
  assign start_chk             = sp2v_sig_chk[18];
  assign finish_chk            = sp2v_sig_chk[19];
  for (genvar i = 0; i < 8; i++) begin : gen_ctr_we
    assign ctr_we[i]           = sp2v_sig_chk[20+i];
  end
  assign cipher_out_done_chk   = sp2v_sig_chk[28];
  assign cipher_out_done_err_d = sp2v_sig_err[28];

  // We need to register the error signal for cipher_out_done to avoid circular loops in the FSM.
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_sp_enc_err
    if (!rst_ni) begin
      cipher_out_done_err_q <= 1'b0;
    end else if (cipher_out_done_err_d) begin
      cipher_out_done_err_q <= 1'b1;
    end
  end

  // Collect encoding errors.
  // We instantiate the checker modules as close as possible to where the sparsely encoded signals
  // are used. Here, we collect also encoding errors detected in other places of the core.
  assign sp_enc_err = |sp2v_sig_err[NumSp2VSig-2:0] | cipher_out_done_err_q | sp_enc_err_i;

  // Prevent synthesis optimizations on the mode signal.
  logic [$bits(aes_mode_e)-1:0] mode_in_raw, mode_buf_raw;
  assign mode_in_raw = {mode_i};
  for (genvar i = 0; i < $bits(mode_i); i++) begin : gen_mode_buf
    prim_buf u_prim_buf_sel_i (
      .in_i  ( mode_in_raw[i]  ),
      .out_o ( mode_buf_raw[i] )
    );
  end
  assign mode = aes_mode_e'(mode_buf_raw);

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid
  `ASSERT(AesModeValid, !ctrl_err_storage_i |-> mode inside {
      AES_ECB,
      AES_CBC,
      AES_CFB,
      AES_OFB,
      AES_CTR,
      AES_NONE
      })
  `ASSERT_KNOWN(AesOpKnown, op_i)
  `ASSERT_KNOWN(AesCiphOpKnown, cipher_op_i)
  `ASSERT(AesControlStateValid, !alert_o |-> aes_ctrl_cs inside {
      IDLE,
      LOAD,
      PRNG_UPDATE,
      PRNG_RESEED,
      FINISH,
      CLEAR
      })

endmodule
