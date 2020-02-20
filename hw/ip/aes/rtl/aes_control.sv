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
  input  aes_pkg::ciph_op_e       cipher_op_i,
  input  logic                    manual_operation_i,
  input  logic                    start_i,
  input  logic                    key_clear_i,
  input  logic                    data_in_clear_i,
  input  logic                    data_out_clear_i,

  // I/O register read/write enables
  input  logic [3:0]              data_in_qe_i,
  input  logic [7:0]              key_init_qe_i,
  input  logic [3:0]              data_out_re_i,
  output logic                    data_in_we_o,
  output logic                    data_out_we_o,

  // Cipher core control and sync
  output logic                    cipher_in_valid_o,
  input  logic                    cipher_in_ready_i,
  input  logic                    cipher_out_valid_i,
  output logic                    cipher_out_ready_o,
  output logic                    cipher_start_o,
  output logic                    cipher_dec_key_gen_o,
  input  logic                    cipher_dec_key_gen_i,
  output logic                    cipher_key_clear_o,
  input  logic                    cipher_key_clear_i,
  output logic                    cipher_data_out_clear_o,
  input  logic                    cipher_data_out_clear_i,

  // Initial key registers
  output aes_pkg::key_init_sel_e  key_init_sel_o,
  output logic [7:0]              key_init_we_o,

  // Trigger register
  output logic                    start_o,
  output logic                    start_we_o,
  output logic                    key_clear_o,
  output logic                    key_clear_we_o,
  output logic                    data_in_clear_o,
  output logic                    data_in_clear_we_o,
  output logic                    data_out_clear_o,
  output logic                    data_out_clear_we_o,

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
  typedef enum logic [1:0] {
    IDLE, LOAD, WAIT, CLEAR
  } aes_ctrl_e;

  aes_ctrl_e aes_ctrl_ns, aes_ctrl_cs;

  // Signals
  logic [3:0] data_in_new_d, data_in_new_q;
  logic       data_in_new;
  logic       data_in_load;

  logic       key_init_clear;
  logic [7:0] key_init_new_d, key_init_new_q;
  logic       key_init_new;
  logic       dec_key_gen;

  logic [3:0] data_out_read_d, data_out_read_q;
  logic       data_out_read;
  logic       output_valid_q;

  logic       start, finish;

  // If not set to manually start, we start once we have valid data available.
  assign start = manual_operation_i ? start_i : data_in_new;

  // If not set to overwrite data, we wait for any previous output data to be read. data_out_read
  // synchronously clears output_valid_q, unless new output data is written in the exact same
  // clock cycle.
  assign finish = manual_operation_i ? 1'b1 : ~output_valid_q | data_out_read;

  // FSM
  always_comb begin : aes_ctrl_fsm

    // Cipher core control
    cipher_in_valid_o       = 1'b0;
    cipher_out_ready_o      = 1'b0;
    cipher_start_o          = 1'b0;
    cipher_dec_key_gen_o    = 1'b0;
    cipher_key_clear_o      = 1'b0;
    cipher_data_out_clear_o = 1'b0;

    // Initial key registers
    key_init_sel_o = KEY_INIT_INPUT;
    key_init_we_o  = 8'h00;

    // Trigger register control
    start_we_o          = 1'b0;
    key_clear_we_o      = 1'b0;
    data_in_clear_we_o  = 1'b0;
    data_out_clear_we_o = 1'b0;

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

    // FSM
    aes_ctrl_ns   = aes_ctrl_cs;

    unique case (aes_ctrl_cs)

      IDLE: begin
        idle_o        = 1'b1;
        idle_we_o     = 1'b1;
        stall_o       = 1'b0;
        stall_we_o    = 1'b1;

        if (start) begin
          cipher_start_o = 1'b1;
          // We got a new initial key, but want to do decryption. The cipher core must first
          // generate the start key for decryption.
          cipher_dec_key_gen_o = key_init_new & (cipher_op_i == CIPH_INV);

          // We have work for the cipher core, perform handshake.
          cipher_in_valid_o = 1'b1;
          if (cipher_in_ready_i) begin
            idle_o      = 1'b0;
            idle_we_o   = 1'b1;
            start_we_o  = ~cipher_dec_key_gen_o;

            aes_ctrl_ns = LOAD;
          end
         end else if (key_clear_i || data_out_clear_i) begin
          // To clear the output data registers, we re-use the muxing resources of the cipher core.
          // To clear all key material, some key registers inside the cipher core need to be
          // cleared.
          cipher_key_clear_o      = key_clear_i;
          cipher_data_out_clear_o = data_out_clear_i;

          // We have work for the cipher core, perform handshake.
          cipher_in_valid_o = 1'b1;
          if (cipher_in_ready_i) begin
            idle_o      = 1'b0;
            idle_we_o   = 1'b1;

            aes_ctrl_ns = CLEAR;
          end
        end else if (data_in_clear_i) begin
          // To clear the input data registers, no handshake with the cipher core is needed.
          idle_o      = 1'b0;
          idle_we_o   = 1'b1;

          aes_ctrl_ns = CLEAR;
        end

        key_init_we_o = idle_o ? key_init_qe_i : 8'h00;
      end

      LOAD: begin
        // Clear data_in_new, key_init_new
        data_in_load = ~cipher_dec_key_gen_i;
        dec_key_gen  =  cipher_dec_key_gen_i;

        aes_ctrl_ns = WAIT;
      end

      WAIT: begin
        // Wait for cipher core to finish.

        if (cipher_dec_key_gen_i) begin
          // We are ready.
          cipher_out_ready_o = 1'b1;
          if (cipher_out_valid_i) begin
            aes_ctrl_ns      = IDLE;
          end
        end else begin
          // We are ready once the output data registers can be written.
          stall_o            = !finish & cipher_out_valid_i;
          stall_we_o         = 1'b1;
          cipher_out_ready_o = finish;
          if (finish & cipher_out_valid_i) begin
            data_out_we_o    = 1'b1;
            aes_ctrl_ns      = IDLE;
          end
        end
      end

      CLEAR: begin
        // The input data registers can be cleared independently of the cipher core.
        if (data_in_clear_i) begin
          data_in_we_o       = 1'b1;
          data_in_clear_we_o = 1'b1;
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

  // Detect new key, new input, output read
  // Edge detectors are cleared by the FSM
  assign key_init_clear = (key_init_sel_o == KEY_INIT_CLEAR) & (&key_init_we_o);
  assign key_init_new_d = (dec_key_gen | key_init_clear) ? '0 : (key_init_new_q | key_init_qe_i);
  assign key_init_new   = &key_init_new_d;

  assign data_in_new_d = (data_in_load | data_in_we_o) ? '0 : (data_in_new_q | data_in_qe_i);
  assign data_in_new   = &data_in_new_d;

  // data_out_read is high for one clock cycle only. It clears output_valid_q unless new output
  // data is written in the exact same cycle.
  assign data_out_read_d = &data_out_read_q ? '0 : data_out_read_q | data_out_re_i;
  assign data_out_read   = &data_out_read_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_edge_detection
    if (!rst_ni) begin
      key_init_new_q  <= '0;
      data_in_new_q   <= '0;
      data_out_read_q <= '0;
    end else begin
      key_init_new_q  <= key_init_new_d;
      data_in_new_q   <= data_in_new_d;
      data_out_read_q <= data_out_read_d;
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
  assign input_ready_o     = ~data_in_new;
  assign input_ready_we_o  =  data_in_new | data_in_load | data_in_we_o;

  // Trigger register, the control only ever clears these
  assign start_o             = 1'b0;
  assign key_clear_o         = 1'b0;
  assign data_in_clear_o     = 1'b0;
  assign data_out_clear_o    = 1'b0;

  // Selectors must be known/valid
  `ASSERT_KNOWN(AesCiphOpKnown, cipher_op_i)
  `ASSERT_KNOWN(AesControlStateValid, aes_ctrl_cs)

endmodule
