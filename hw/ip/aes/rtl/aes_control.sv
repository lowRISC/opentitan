// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES control

module aes_control #(
  parameter bit AES192Enable = 1
) (
  input  logic                    clk_i,
  input  logic                    rst_ni,

  // Main control inputs
  input  aes_pkg::mode_e          mode_i,
  input  aes_pkg::key_len_e       key_len_i,
  input  logic                    force_data_overwrite_i,
  input  logic                    manual_start_trigger_i,
  input  logic                    start_i,

  // I/O register read/write enables
  input  logic [3:0]              data_in_qe_i,
  input  logic [7:0]              key_init_qe_i,
  input  logic [3:0]              data_out_re_i,

  // Control ouptuts cipher data path
  output aes_pkg::state_sel_e     state_sel_o,
  output logic                    state_we_o,
  output aes_pkg::add_rk_sel_e    add_rk_sel_o,

  // Control outputs key expand data path
  output aes_pkg::key_full_sel_e  key_full_sel_o,
  output logic                    key_full_we_o,
  output aes_pkg::key_dec_sel_e   key_dec_sel_o,
  output logic                    key_dec_we_o,
  output logic                    key_expand_clear_o,
  output aes_pkg::key_words_sel_e key_words_sel_o,

  // Output registers control
  output logic                    data_out_we_o,

  // To I/O registers
  output logic                    trigger_o,
  output logic                    trigger_we_o,
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

  // Signals
  logic [3:0] data_in_new_d, data_in_new_q;
  logic       data_in_new;
  logic       data_in_load;

  logic [7:0] key_init_new_d, key_init_new_q;
  logic       key_init_new;
  logic       dec_key_gen;

  logic [3:0] data_out_read_d, data_out_read_q;
  logic       data_out_read;

  assign data_in_load = (state_sel_o == STATE_INIT);

  // Placeholders
  mode_e    unused_mode;
  key_len_e unused_key_len;
  logic     unused_force_data_overwrite;
  logic     unused_manual_start_trigger;
  logic     unused_start;
  logic     unused_key_init_new;
  assign    unused_mode                 = mode_i;
  assign    unused_key_len              = key_len_i;
  assign    unused_force_data_overwrite = force_data_overwrite_i;
  assign    unused_manual_start_trigger = manual_start_trigger_i;
  assign    unused_start                = start_i;
  assign    unused_key_init_new  = key_init_new;

  assign state_sel_o        = STATE_ROUND;
  assign state_we_o         = 1'b0;
  assign add_rk_sel_o       = ADD_RK_ROUND;

  assign key_full_sel_o     = KEY_FULL_ROUND;
  assign key_full_we_o      = 1'b0;
  assign key_dec_sel_o      = KEY_DEC_EXPAND;
  assign key_dec_we_o       = 1'b0;
  assign key_expand_clear_o = 1'b0;
  assign key_words_sel_o    = KEY_WORDS_0123;

  assign dec_key_gen   = 1'b0;

  assign data_out_we_o = 1'b0;

  assign trigger_o     = 1'b0;
  assign trigger_we_o  = 1'b1;
  assign idle_o        = 1'b0;
  assign idle_we_o     = 1'b1;
  assign stall_o       = 1'b0;
  assign stall_we_o    = 1'b1;

  // Detect new key, new input, output read
  // Edge detectors are cleared by the FSM
  assign key_init_new_d = dec_key_gen ? '0 : key_init_new_q | key_init_qe_i;
  assign key_init_new   = &key_init_new_d;

  assign data_in_new_d = data_in_load ? '0 : data_in_new_q | data_in_qe_i;
  assign data_in_new   = &data_in_new_d;

  assign data_out_read_d = data_out_we_o ? '0 : data_out_read_q | data_out_re_i;
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

  // clear once all output regs have been read
  assign output_valid_o    = data_out_we_o;
  assign output_valid_we_o = data_out_we_o | data_out_read;

  // clear once all input regs have been written
  assign input_ready_o     = ~data_in_new;
  assign input_ready_we_o  =  data_in_new | data_in_load;

endmodule
