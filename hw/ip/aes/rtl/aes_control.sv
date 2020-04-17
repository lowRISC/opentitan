// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES main control
//
// This module controls the interplay of input/output registers and the AES cipher core.

`include "prim_assert.sv"

module aes_control (
  input  logic                    clk_i,
  input  logic                    rst_ni,

  // Main control inputs
  input  aes_pkg::aes_op_e        op_i,
  input  aes_pkg::aes_mode_e      mode_i,
  input  aes_pkg::ciph_op_e       cipher_op_i,
  input  logic                    manual_operation_i,
  input  logic                    start_i,
  input  logic                    key_clear_i,
  input  logic                    iv_clear_i,
  input  logic                    data_in_clear_i,
  input  logic                    data_out_clear_i,
  input  logic                    prng_reseed_i,

  // I/O register read/write enables
  input  logic [7:0]              key_init_qe_i,
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
  output logic [7:0]              key_init_we_o,

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
  output logic                    key_clear_o,
  output logic                    key_clear_we_o,
  output logic                    iv_clear_o,
  output logic                    iv_clear_we_o,
  output logic                    data_in_clear_o,
  output logic                    data_in_clear_we_o,
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
  output logic                    stall_we_o
);

  import aes_pkg::*;

  // Types
  typedef enum logic [2:0] {
    IDLE, LOAD, UPDATE_PRNG, FINISH, CLEAR
  } aes_ctrl_e;

  aes_ctrl_e aes_ctrl_ns, aes_ctrl_cs;

  // Signals
  logic       key_init_clear;
  logic [7:0] key_init_new_d, key_init_new_q;
  logic       key_init_new;
  logic       dec_key_gen;

  logic [7:0] iv_qe;
  logic       iv_clear;
  logic [7:0] iv_new_d, iv_new_q;
  logic       iv_new;
  logic       iv_clean;
  logic       iv_load;
  logic       iv_ready_d, iv_ready_q;

  logic [3:0] data_in_new_d, data_in_new_q;
  logic       data_in_new;
  logic       data_in_load;

  logic [3:0] data_out_read_d, data_out_read_q;
  logic       data_out_read;
  logic       output_valid_q;

  logic       start, finish;
  logic       cipher_crypt;
  logic       doing_cbc_enc, doing_cbc_dec;
  logic       doing_ctr;

  // Software updates IV in chunks of 32 bits, the counter updates 16 bits at a time.
  // Convert word write enable to internal half-word write enable.
  assign iv_qe = {iv_qe_i[3], iv_qe_i[3], iv_qe_i[2], iv_qe_i[2],
                  iv_qe_i[1], iv_qe_i[1], iv_qe_i[0], iv_qe_i[0]};

  // If set to start manually, we just wait for the trigger. Otherwise, we start once we have valid
  // data available. If the IV (and counter) is needed, we only start if also the IV (and counter)
  // is ready.
  assign start = manual_operation_i ? start_i                                  :
                (mode_i == AES_ECB) ? data_in_new                              :
                (mode_i == AES_CBC) ? (data_in_new & iv_ready_q)               :
                (mode_i == AES_CTR) ? (data_in_new & iv_ready_q & ctr_ready_i) : 1'b0;

  // If not set to overwrite data, we wait for any previous output data to be read. data_out_read
  // synchronously clears output_valid_q, unless new output data is written in the exact same
  // clock cycle.
  assign finish = manual_operation_i ? 1'b1 : ~output_valid_q | data_out_read;

  // Helper signals for FSM
  assign cipher_crypt  = cipher_crypt_o | cipher_crypt_i;
  assign doing_cbc_enc = cipher_crypt & (mode_i == AES_CBC) & (op_i == AES_ENC);
  assign doing_cbc_dec = cipher_crypt & (mode_i == AES_CBC) & (op_i == AES_DEC);
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
    cipher_crypt_o          = 1'b0;
    cipher_dec_key_gen_o    = 1'b0;
    cipher_key_clear_o      = 1'b0;
    cipher_data_out_clear_o = 1'b0;

    // Initial key registers
    key_init_sel_o = KEY_INIT_INPUT;
    key_init_we_o  = 8'h00;

    // IV registers
    iv_sel_o    = IV_INPUT;
    iv_we_o     = 8'h00;
    iv_load     = 1'b0;

    // Pseudo-random number generator control
    prng_data_req_o   = 1'b0;
    prng_reseed_req_o = 1'b0;

    // Trigger register control
    start_we_o          = 1'b0;
    key_clear_we_o      = 1'b0;
    iv_clear_we_o       = 1'b0;
    data_in_clear_we_o  = 1'b0;
    data_out_clear_we_o = 1'b0;
    prng_reseed_we_o    = 1'b0;

    // Status register
    idle_o     = 1'b0;
    idle_we_o  = 1'b0;
    stall_o    = 1'b0;
    stall_we_o = 1'b0;

    // Key, data I/O register control
    dec_key_gen   = 1'b0;
    data_in_load  = 1'b0;
    data_in_we_o  = 1'b0;
    data_out_we_o = 1'b0;

    // Edge detector control
    key_init_clear = 1'b0;
    iv_clear       = 1'b0;

    // FSM
    aes_ctrl_ns = aes_ctrl_cs;

    unique case (aes_ctrl_cs)

      IDLE: begin
        idle_o    = (start || key_clear_i || iv_clear_i ||
                    data_in_clear_i || data_out_clear_i || prng_reseed_i) ? 1'b0 : 1'b1;
        idle_we_o = 1'b1;

        // Initial key and IV updates are ignored if we are not idle.
        key_init_we_o = idle_o ? key_init_qe_i : 8'h00;
        iv_we_o       = idle_o ? iv_qe         : 8'h00;

        if (prng_reseed_i) begin
          // Request a reseed of the PRNG, perform handshake.
          prng_reseed_req_o = 1'b1;
          if (prng_reseed_ack_i) begin
            // Clear the trigger.
            prng_reseed_we_o = 1'b1;
          end

        end else if (key_clear_i || data_out_clear_i || iv_clear_i || data_in_clear_i) begin
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
                               doing_ctr     ? DIP_DATA_IN : DIP_CLEAR;
          data_in_prev_we_o  = doing_cbc_dec ? 1'b1 :
                               doing_ctr     ? 1'b1 : 1'b0;

          // State input mux control
          state_in_sel_o     = doing_ctr     ? SI_ZERO : SI_DATA;

          // State input additon mux control
          add_state_in_sel_o = doing_cbc_enc ? ADD_SI_IV :
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
        // Clear key_init_new, iv_new, data_in_new
        dec_key_gen  =  cipher_dec_key_gen_i;
        iv_load      = ~cipher_dec_key_gen_i;
        data_in_load = ~cipher_dec_key_gen_i;

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

          end else if (key_clear_i || data_out_clear_i) begin
            // To clear the output data registers, we re-use the muxing resources of the cipher
            // core. To clear all key material, some key registers inside the cipher core need to
            // be cleared.
            cipher_key_clear_o      = key_clear_i;
            cipher_data_out_clear_o = data_out_clear_i;

            // We have work for the cipher core, perform handshake.
            cipher_in_valid_o = 1'b1;
            if (cipher_in_ready_i) begin
              aes_ctrl_ns = CLEAR;
            end
          end else begin // (iv_clear_i || data_in_clear_i)
            // To clear the IV or input data registers, no handshake with the cipher core is
            // needed.
            aes_ctrl_ns = CLEAR;
          end
        end
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
          // Signal if the cipher core is stalled (because previous output has not yet been read).
          stall_o    = ~finish & cipher_out_valid_i;
          stall_we_o = 1'b1;

          // State out addition mux control
          add_state_out_sel_o = doing_cbc_dec ? ADD_SO_IV  :
                                doing_ctr     ? ADD_SO_DIP : ADD_SO_ZERO;

          // IV control
          // - CBC: IV registers can only be updated when cipher finishes
          // - CTR: IV registers are updated by counter during cipher operation
          iv_sel_o =  doing_cbc_enc                   ? IV_DATA_OUT     :
                      doing_cbc_dec                   ? IV_DATA_IN_PREV :
                      doing_ctr                       ? IV_CTR          : IV_INPUT;
          iv_we_o  = (doing_cbc_enc || doing_cbc_dec) ? {8{finish & cipher_out_valid_i}} :
                      doing_ctr                       ? ctr_we_i                         : 8'h00;

          // We are ready once the output data registers can be written.
          cipher_out_ready_o = finish;
          if (finish & cipher_out_valid_i) begin
            data_out_we_o = 1'b1;
            aes_ctrl_ns   = IDLE;
          end
        end
      end

      CLEAR: begin
        // The IV and input data registers can be cleared independently of the cipher core.
        if (iv_clear_i) begin
          iv_sel_o      = IV_CLEAR;
          iv_we_o       = 8'hFF;
          iv_clear_we_o = 1'b1;
          iv_clear      = 1'b1;
        end
        if (data_in_clear_i) begin
          data_in_we_o       = 1'b1;
          data_in_clear_we_o = 1'b1;
          data_in_prev_sel_o = DIP_CLEAR;
          data_in_prev_we_o  = 1'b1;
        end

        // To clear the output data registers, we re-use the muxing resources of the cipher core.
        // To clear all key material, some key registers inside the cipher core need to be cleared.
        if (cipher_key_clear_i || cipher_data_out_clear_i) begin

          // Perform handshake.
          cipher_out_ready_o = 1'b1;
          if (cipher_out_valid_i) begin

            if (cipher_key_clear_i) begin
              key_init_sel_o      = KEY_INIT_CLEAR;
              key_init_we_o       = 8'hFF;
              key_clear_we_o      = 1'b1;
              key_init_clear      = 1'b1;
            end

            if (cipher_data_out_clear_i) begin
              data_out_we_o       = 1'b1;
              data_out_clear_we_o = 1'b1;
            end
            aes_ctrl_ns = IDLE;
          end

        end else begin
          aes_ctrl_ns = IDLE;
        end
      end

      default: aes_ctrl_ns = IDLE;
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_fsm
    if (!rst_ni) begin
      aes_ctrl_cs <= IDLE;
    end else begin
      aes_ctrl_cs <= aes_ctrl_ns;
    end
  end

  // Detect new key, new IV, new input, output read.
  // Edge detectors are cleared by the FSM.
  assign key_init_new_d = (dec_key_gen || key_init_clear) ? '0 : (key_init_new_q | key_init_we_o);
  assign key_init_new   = &key_init_new_d;

  // The IV regs can be updated by both software or the counter.
  assign iv_new_d = (iv_load || iv_clear) ? '0 : (iv_new_q | iv_we_o);
  assign iv_new   = &iv_new_d; // All of the IV regs have been updated.
  assign iv_clean = ~(|iv_new_d); // None of the IV regs have been updated.

  assign data_in_new_d = (data_in_load || data_in_we_o) ? '0 : (data_in_new_q | data_in_qe_i);
  assign data_in_new   = &data_in_new_d;

  // data_out_read is high for one clock cycle only. It clears output_valid_q unless new output
  // data is written in the exact same cycle.
  assign data_out_read_d = &data_out_read_q ? '0 : data_out_read_q | data_out_re_i;
  assign data_out_read   = &data_out_read_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_edge_detection
    if (!rst_ni) begin
      key_init_new_q  <= '0;
      iv_new_q        <= '0;
      data_in_new_q   <= '0;
      data_out_read_q <= '0;
    end else begin
      key_init_new_q  <= key_init_new_d;
      iv_new_q        <= iv_new_d;
      data_in_new_q   <= data_in_new_d;
      data_out_read_q <= data_out_read_d;
    end
  end

  // We only use complete IVs. Either software/counter has updated
  // - all IV registers (iv_new), or
  // - none of the IV registers (iv_clean), but the registers were updated in the past.
  assign iv_ready_d = (iv_load || iv_clear) ? 1'b0 : iv_new | (iv_clean & iv_ready_q);

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_iv_ready
    if (!rst_ni) begin
      iv_ready_q <= 1'b0;
    end else begin
      iv_ready_q <= iv_ready_d;
    end
  end

  // Clear once all output regs have been read, or when output is cleared
  assign output_valid_o    = data_out_we_o & ~data_out_clear_we_o;
  assign output_valid_we_o = data_out_we_o | data_out_read | data_out_clear_we_o;

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_output_valid
    if (!rst_ni) begin
      output_valid_q <= '0;
    end else if (output_valid_we_o) begin
      output_valid_q <= output_valid_o;
    end
  end

  // Clear once all input regs have been written, or when input clear is requested
  assign input_ready_o    = ~data_in_new;
  assign input_ready_we_o =  data_in_new | data_in_load | data_in_we_o;

  // Trigger register, the control only ever clears these
  assign start_o          = 1'b0;
  assign key_clear_o      = 1'b0;
  assign iv_clear_o       = 1'b0;
  assign data_in_clear_o  = 1'b0;
  assign data_out_clear_o = 1'b0;
  assign prng_reseed_o    = 1'b0;

  // Selectors must be known/valid
  `ASSERT(AesModeValid, mode_i inside {
      AES_ECB,
      AES_CBC,
      AES_CTR
      })
  `ASSERT_KNOWN(AesOpKnown, op_i)
  `ASSERT_KNOWN(AesCiphOpKnown, cipher_op_i)
  `ASSERT_KNOWN(AesControlStateValid, aes_ctrl_cs)

endmodule
