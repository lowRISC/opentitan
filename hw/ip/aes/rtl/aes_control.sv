// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES main control
//
// This module controls the interplay of input/output registers and the AES cipher core.

`include "prim_assert.sv"

module aes_control
#(
  parameter int unsigned SecStartTriggerDelay = 0
) (
  input  logic                    clk_i,
  input  logic                    rst_ni,

  // Main control signals
  input  logic                    ctrl_qe_i,
  output logic                    ctrl_we_o,
  input  logic                    ctrl_err_storage_i,
  input  aes_pkg::aes_op_e        op_i,
  input  aes_pkg::aes_mode_e      mode_i,
  input  aes_pkg::ciph_op_e       cipher_op_i,
  input  logic                    manual_operation_i,
  input  logic                    start_i,
  input  logic                    key_iv_data_in_clear_i,
  input  logic                    data_out_clear_i,
  input  logic                    prng_reseed_i,
  input  logic                    mux_sel_err_i,
  input  logic                    alert_fatal_i,
  output logic                    alert_o,

  // I/O register read/write enables
  input  logic [7:0]              key_init_qe_i [2],
  input  logic [3:0]              iv_qe_i,
  input  logic [3:0]              data_in_qe_i,
  input  logic [3:0]              data_out_re_i,
  output logic                    data_in_we_o,
  output logic                    data_out_we_o,

  // Previous input data register
  output aes_pkg::dip_sel_e       data_in_prev_sel_o,
  output logic                    data_in_prev_we_o,

  // Cipher I/O muxes
  output aes_pkg::si_sel_e        state_in_sel_o,
  output aes_pkg::add_si_sel_e    add_state_in_sel_o,
  output aes_pkg::add_so_sel_e    add_state_out_sel_o,

  // Counter
  output logic                    ctr_incr_o,
  input  logic                    ctr_ready_i,
  input  logic [7:0]              ctr_we_i,

  // Cipher core control and sync
  output logic                    cipher_in_valid_o,
  input  logic                    cipher_in_ready_i,
  input  logic                    cipher_out_valid_i,
  output logic                    cipher_out_ready_o,
  output logic                    cipher_crypt_o,
  input  logic                    cipher_crypt_i,
  output logic                    cipher_dec_key_gen_o,
  input  logic                    cipher_dec_key_gen_i,
  output logic                    cipher_key_clear_o,
  input  logic                    cipher_key_clear_i,
  output logic                    cipher_data_out_clear_o,
  input  logic                    cipher_data_out_clear_i,

  // Initial key registers
  output aes_pkg::key_init_sel_e  key_init_sel_o,
  output logic [7:0]              key_init_we_o [2],

  // IV registers
  output aes_pkg::iv_sel_e        iv_sel_o,
  output logic [7:0]              iv_we_o,

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

  // Types
  // $ ./sparse-fsm-encode.py -d 3 -m 6 -n 6 \
  //      -s 31468618 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (53.33%)
  //  4: ||||||||||||||| (40.00%)
  //  5: || (6.67%)
  //  6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 5
  //
  localparam int StateWidth = 6;
  typedef enum logic [StateWidth-1:0] {
    IDLE        = 6'b011101,
    LOAD        = 6'b110000,
    UPDATE_PRNG = 6'b001000,
    FINISH      = 6'b000011,
    CLEAR       = 6'b111110,
    ERROR       = 6'b100101
  } aes_ctrl_e;

  aes_ctrl_e aes_ctrl_ns, aes_ctrl_cs;

  // Signals
  logic       key_init_clear;
  logic       key_init_new;
  logic       key_init_load;
  logic       key_init_arm;
  logic       key_init_ready;

  logic [7:0] iv_qe;
  logic       iv_clear;
  logic       iv_load;
  logic       iv_arm;
  logic       iv_ready;

  logic [3:0] data_in_new_d, data_in_new_q;
  logic       data_in_new;
  logic       data_in_load;

  logic [3:0] data_out_read_d, data_out_read_q;
  logic       data_out_read;
  logic       output_valid_q;

  logic       start_trigger;
  logic       cfg_valid;
  logic       no_alert;
  logic       start, finish;
  logic       cipher_crypt;
  logic       cipher_out_done;
  logic       doing_cbc_enc, doing_cbc_dec;
  logic       doing_cfb_enc, doing_cfb_dec;
  logic       doing_ofb;
  logic       doing_ctr;
  logic       ctrl_we_q;
  logic       clear_in_out_status;

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
  assign cfg_valid = ~((mode_i == AES_NONE) | ctrl_err_storage_i);
  assign no_alert  = ~alert_fatal_i;

  // If set to start manually, we just wait for the trigger. Otherwise, we start once we have valid
  // data available. If the IV (and counter) is needed, we only start if also the IV (and counter)
  // is ready.
  assign start = cfg_valid & no_alert &
      ( manual_operation_i ? start_trigger                                           :
       (mode_i == AES_ECB) ? (key_init_ready & data_in_new)                          :
       (mode_i == AES_CBC) ? (key_init_ready & data_in_new & iv_ready)               :
       (mode_i == AES_CFB) ? (key_init_ready & data_in_new & iv_ready)               :
       (mode_i == AES_OFB) ? (key_init_ready & data_in_new & iv_ready)               :
       (mode_i == AES_CTR) ? (key_init_ready & data_in_new & iv_ready & ctr_ready_i) : 1'b0);

  // If not set to overwrite data, we wait for any previous output data to be read. data_out_read
  // synchronously clears output_valid_q, unless new output data is written in the exact same
  // clock cycle.
  assign finish = cfg_valid & no_alert &
      (manual_operation_i ? 1'b1 : (~output_valid_q | data_out_read));

  // Helper signals for FSM
  assign cipher_crypt  = cipher_crypt_o | cipher_crypt_i;
  assign doing_cbc_enc = cipher_crypt & (mode_i == AES_CBC) & (op_i == AES_ENC);
  assign doing_cbc_dec = cipher_crypt & (mode_i == AES_CBC) & (op_i == AES_DEC);
  assign doing_cfb_enc = cipher_crypt & (mode_i == AES_CFB) & (op_i == AES_ENC);
  assign doing_cfb_dec = cipher_crypt & (mode_i == AES_CFB) & (op_i == AES_DEC);
  assign doing_ofb     = cipher_crypt & (mode_i == AES_OFB);
  assign doing_ctr     = cipher_crypt & (mode_i == AES_CTR);

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
    cipher_key_clear_o      = 1'b0;
    cipher_data_out_clear_o = 1'b0;

    // Initial key registers
    key_init_sel_o = KEY_INIT_INPUT;
    key_init_we_o  = '{8'h00, 8'h00};

    // IV registers
    iv_sel_o = IV_INPUT;
    iv_we_o  = 8'h00;

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
    data_out_we_o = 1'b0;

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
        idle_o    = (start || key_iv_data_in_clear_i || data_out_clear_i ||
                    prng_reseed_i) ? 1'b0 : 1'b1;
        idle_we_o = 1'b1;

        if (idle_o) begin
          // Initial key and IV updates are ignored if we are not idle.
          key_init_we_o  = key_init_qe_i;
          iv_we_o        = iv_qe;

          // Updates to the control register are only allowed if we are idle and we don't have a
          // storage error. A storage error is unrecoverable and requires a reset.
          ctrl_we_o      = !ctrl_err_storage_i ? ctrl_qe_i : 1'b0;

          // Control register updates clear all register status trackers.
          key_init_clear = ctrl_we_o;
          iv_clear       = ctrl_we_o;
        end

        if (prng_reseed_i) begin
          // Request a reseed of the PRNG, perform handshake.
          prng_reseed_req_o = 1'b1;
          if (prng_reseed_ack_i) begin
            // Clear the trigger.
            prng_reseed_we_o = 1'b1;
          end

        end else if (key_iv_data_in_clear_i || data_out_clear_i) begin
          // To clear registers, we must first request fresh pseudo-random data.
          aes_ctrl_ns = UPDATE_PRNG;

        end else if (start) begin
          // Signal that we want to start encryption/decryption.
          cipher_crypt_o = 1'b1;

          // We got a new initial key, but want to do decryption. The cipher core must first
          // generate the start key for decryption.
          cipher_dec_key_gen_o = key_init_new & (cipher_op_i == CIPH_INV);

          // Previous input data register control
          data_in_prev_sel_o = doing_cbc_dec ? DIP_DATA_IN :
                               doing_cfb_enc ? DIP_DATA_IN :
                               doing_cfb_dec ? DIP_DATA_IN :
                               doing_ofb     ? DIP_DATA_IN :
                               doing_ctr     ? DIP_DATA_IN : DIP_CLEAR;
          data_in_prev_we_o  = doing_cbc_dec ? 1'b1 :
                               doing_cfb_enc ? 1'b1 :
                               doing_cfb_dec ? 1'b1 :
                               doing_ofb     ? 1'b1 :
                               doing_ctr     ? 1'b1 : 1'b0;

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
            start_we_o  = ~cipher_dec_key_gen_o;
            aes_ctrl_ns = LOAD;
          end
        end
      end

      LOAD: begin
        // Signal that we have used the current key, IV, data input to register status tracking.
        key_init_load =  cipher_dec_key_gen_i; // This key is no longer "new", but still clean.
        key_init_arm  = ~cipher_dec_key_gen_i; // The key is still "new", prevent partial updates.
        iv_load       = ~cipher_dec_key_gen_i & (doing_cbc_enc | doing_cbc_dec |
                                                 doing_cfb_enc | doing_cfb_dec |
                                                 doing_ofb | doing_ctr);
        data_in_load  = ~cipher_dec_key_gen_i;

        // Trigger counter increment.
        ctr_incr_o   = doing_ctr ? 1'b1 : 1'b0;

        // Unless we are just generating the start key for decryption, we must update the PRNG.
        aes_ctrl_ns  = ~cipher_dec_key_gen_i ? UPDATE_PRNG : FINISH;
      end

      UPDATE_PRNG: begin
        // Fresh pseudo-random data is used to:
        // - clear the state in the final cipher round,
        // - clear any other registers in the CLEAR state.

        // IV control in case of ongoing encryption/decryption
        // - CTR: IV registers are updated by counter during cipher operation
        iv_sel_o = doing_ctr ? IV_CTR   : IV_INPUT;
        iv_we_o  = doing_ctr ? ctr_we_i : 8'h00;

        // Request fresh pseudo-random data, perform handshake.
        prng_data_req_o = 1'b1;
        if (prng_data_ack_i) begin

          // Ongoing encryption/decryption operations have the highest priority. The clear triggers
          // might have become asserted after the handshake with the cipher core.
          if (cipher_crypt_i) begin
            aes_ctrl_ns = FINISH;

          end else begin // (key_iv_data_in_clear_i || data_out_clear_i)
            // To clear the output data registers, we re-use the muxing resources of the cipher
            // core. To clear all key material, some key registers inside the cipher core need to
            // be cleared.
            cipher_key_clear_o      = key_iv_data_in_clear_i;
            cipher_data_out_clear_o = data_out_clear_i;

            // We have work for the cipher core, perform handshake.
            cipher_in_valid_o = 1'b1;
            if (cipher_in_ready_i) begin
              aes_ctrl_ns = CLEAR;
            end
          end // cipher_crypt_i
        end // prng_data_ack_i
      end

      FINISH: begin
        // Wait for cipher core to finish.

        if (cipher_dec_key_gen_i) begin
          // We are ready.
          cipher_out_ready_o = 1'b1;
          if (cipher_out_valid_i) begin
            aes_ctrl_ns = IDLE;
          end
        end else begin
          // Handshake signals: We are ready once the output data registers can be written.
          cipher_out_ready_o = finish;
          cipher_out_done    = finish & cipher_out_valid_i;

          // Signal if the cipher core is stalled (because previous output has not yet been read).
          stall_o    = ~finish & cipher_out_valid_i;
          stall_we_o = 1'b1;

          // State out addition mux control
          add_state_out_sel_o = doing_cbc_dec ? ADD_SO_IV  :
                                doing_cfb_enc ? ADD_SO_DIP :
                                doing_cfb_dec ? ADD_SO_DIP :
                                doing_ofb     ? ADD_SO_DIP :
                                doing_ctr     ? ADD_SO_DIP : ADD_SO_ZERO;

          // IV control
          // - CBC/CFB/OFB: IV registers are only updated when cipher finishes.
          // - CTR: IV registers are updated by counter during cipher operation.
          iv_sel_o = doing_cbc_enc  ? IV_DATA_OUT     :
                     doing_cbc_dec  ? IV_DATA_IN_PREV :
                     doing_cfb_enc  ? IV_DATA_OUT     :
                     doing_cfb_dec  ? IV_DATA_IN_PREV :
                     doing_ofb      ? IV_DATA_OUT_RAW :
                     doing_ctr      ? IV_CTR          : IV_INPUT;
          iv_we_o  = doing_cbc_enc ||
                     doing_cbc_dec ||
                     doing_cfb_enc ||
                     doing_cfb_dec ||
                     doing_ofb     ? {8{cipher_out_done}} :
                     doing_ctr     ? ctr_we_i             : 8'h00;

          // Arm the IV status tracker: After finishing, the IV registers can be written again
          // by software. We need to make sure software does not partially update the IV.
          iv_arm = doing_cbc_enc ||
                   doing_cbc_dec ||
                   doing_cfb_enc ||
                   doing_cfb_dec ||
                   doing_ofb     ||
                   doing_ctr     ? cipher_out_done : 1'b0;

          // Proceed upon successful handshake.
          if (cipher_out_done) begin
            // Don't release data from cipher core in case of invalid mux selector signals.
            data_out_we_o = ~mux_sel_err_i;
            aes_ctrl_ns   = IDLE;
          end
        end
      end

      CLEAR: begin
        // Initial Key, IV and input data registers can be cleared right away.
        if (key_iv_data_in_clear_i) begin
          // Initial Key
          key_init_sel_o = KEY_INIT_CLEAR;
          key_init_we_o  = '{8'hFF, 8'hFF};
          key_init_clear = 1'b1;

          // IV
          iv_sel_o = IV_CLEAR;
          iv_we_o  = 8'hFF;
          iv_clear = 1'b1;

          // Input data
          data_in_we_o       = 1'b1;
          data_in_prev_sel_o = DIP_CLEAR;
          data_in_prev_we_o  = 1'b1;
        end

        // Perform handshake with cipher core.
        cipher_out_ready_o = 1'b1;
        if (cipher_out_valid_i) begin

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
            // of invalid mux selector signals.
            data_out_we_o       = ~mux_sel_err_i;
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

    // Unconditionally jump into the terminal error state in case a mux selector signal becomes
    // invalid.
    if (mux_sel_err_i) begin
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
  aes_reg_status #(
    .Width ( $bits(key_init_we_o) )
  ) u_reg_status_key_init (
    .clk_i   ( clk_i                                ),
    .rst_ni  ( rst_ni                               ),
    .we_i    ( {key_init_we_o[1], key_init_we_o[0]} ),
    .use_i   ( key_init_load                        ),
    .clear_i ( key_init_clear                       ),
    .arm_i   ( key_init_arm                         ),
    .new_o   ( key_init_new                         ),
    .clean_o ( key_init_ready                       )
  );

  // We only use clean and unused IVs. Either software/counter has updated
  // - all IV registers, or
  // - none of the IV registers but the registers were updated in the past
  // and this particular IV has not yet been used.
  aes_reg_status #(
    .Width ( $bits(iv_we_o) )
  ) u_reg_status_iv (
    .clk_i   ( clk_i    ),
    .rst_ni  ( rst_ni   ),
    .we_i    ( iv_we_o  ),
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
  assign input_ready_o    = ~data_in_new;
  assign input_ready_we_o =  data_in_new | data_in_load | data_in_we_o | clear_in_out_status;

  // Cleared if:
  // - all data output registers have been read (unless new output is written in the same cycle),
  // - clearing data ouput registers with random data,
  // - clearing the status tracking.
  assign output_valid_o    = data_out_we_o & ~data_out_clear_we_o;
  assign output_valid_we_o = data_out_we_o | data_out_read | data_out_clear_we_o |
      clear_in_out_status;

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_output_valid
    if (!rst_ni) begin
      output_valid_q <= '0;
    end else if (output_valid_we_o) begin
      output_valid_q <= output_valid_o;
    end
  end

  // Output lost status register bit
  // Cleared when updating the Control Register. Set when overwriting previous output data that has
  // not yet been read.
  assign output_lost_o    = ctrl_we_o     ? 1'b0 :
                            output_lost_i ? 1'b1 : output_valid_q & ~data_out_read;
  assign output_lost_we_o = ctrl_we_o | data_out_we_o;

  // Trigger register, the control only ever clears these
  assign start_o                = 1'b0;
  assign key_iv_data_in_clear_o = 1'b0;
  assign data_out_clear_o       = 1'b0;
  assign prng_reseed_o          = 1'b0;

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid
  `ASSERT(AesModeValid, !ctrl_err_storage_i |-> mode_i inside {
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
      UPDATE_PRNG,
      FINISH,
      CLEAR
      })

endmodule
