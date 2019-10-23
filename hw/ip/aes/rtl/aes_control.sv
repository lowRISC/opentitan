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
  input  logic                    key_clear_i,
  input  logic                    data_out_clear_i,

  // I/O register read/write enables
  input  logic [3:0]              data_in_qe_i,
  input  logic [7:0]              key_init_qe_i,
  input  logic [3:0]              data_out_re_i,

  // Control ouptuts cipher data path
  output aes_pkg::state_sel_e     state_sel_o,
  output logic                    state_we_o,
  output aes_pkg::add_rk_sel_e    add_rk_sel_o,

  // Control outputs key expand data path
  output aes_pkg::mode_e          key_expand_mode_o,
  output aes_pkg::key_full_sel_e  key_full_sel_o,
  output logic                    key_full_we_o,
  output aes_pkg::key_dec_sel_e   key_dec_sel_o,
  output logic                    key_dec_we_o,
  output logic                    key_expand_step_o,
  output logic                    key_expand_clear_o,
  output logic [3:0]              key_expand_round_o,
  output aes_pkg::key_words_sel_e key_words_sel_o,
  output aes_pkg::round_key_sel_e round_key_sel_o,

  // Output registers control
  output logic                    data_out_we_o,

  // To I/O registers
  output logic                    start_o,
  output logic                    start_we_o,
  output logic                    key_clear_o,
  output logic                    key_clear_we_o,
  output logic                    data_out_clear_o,
  output logic                    data_out_clear_we_o,
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
    IDLE, INIT, ROUND, FINISH
  } aes_ctrl_e;

  aes_ctrl_e aes_ctrl_ns, aes_ctrl_cs;

  // Signals
  logic [3:0] data_in_new_d, data_in_new_q;
  logic       data_in_new;
  logic       data_in_load;

  logic [7:0] key_init_new_d, key_init_new_q;
  logic       key_init_new;
  logic       dec_key_gen;

  logic [3:0] data_out_read_d, data_out_read_q;
  logic       data_out_read;
  logic       output_valid_q;

  logic [3:0] round_d, round_q;
  logic [3:0] num_rounds_d, num_rounds_q;
  logic [3:0] num_rounds_regular;
  logic       dec_key_gen_d, dec_key_gen_q;

  logic       start, finish;

  // If not set to manually start, we start once we have valid data available.
  assign start = manual_start_trigger_i ? start_i : data_in_new;

  // If not set to overwrite data, we wait for previous output data to be read.
  assign finish = force_data_overwrite_i ? 1'b1 : ~output_valid_q;

  // FSM
  always_comb begin : aes_ctrl_fsm

    // Cipher data path
    state_sel_o  = STATE_ROUND;
    state_we_o   = 1'b0;
    add_rk_sel_o = ADD_RK_ROUND;

    // Key expand data path
    key_full_sel_o     = KEY_FULL_ROUND;
    key_full_we_o      = 1'b0;
    key_dec_sel_o      = KEY_DEC_EXPAND;
    key_dec_we_o       = 1'b0;
    key_expand_step_o  = 1'b0;
    key_expand_clear_o = 1'b0;
    key_words_sel_o    = KEY_WORDS_ZERO;
    round_key_sel_o    = ROUND_KEY_DIRECT;

    // Trigger register control
    start_we_o          = 1'b0;
    key_clear_we_o      = 1'b0;
    data_out_clear_we_o = 1'b0;

    // Status register
    idle_o     = 1'b0;
    idle_we_o  = 1'b0;
    stall_o    = 1'b0;
    stall_we_o = 1'b0;

    // Key, data I/O register control
    dec_key_gen   = 1'b0;
    data_in_load  = 1'b0;
    data_out_we_o = 1'b0;

    // FSM
    aes_ctrl_ns   = aes_ctrl_cs;
    round_d       = round_q;
    num_rounds_d  = num_rounds_q;
    dec_key_gen_d = dec_key_gen_q;

    unique case (aes_ctrl_cs)

      IDLE: begin
        idle_o        = 1'b1;
        idle_we_o     = 1'b1;
        stall_o       = 1'b0;
        stall_we_o    = 1'b1;

        dec_key_gen_d = 1'b0;

        if (start) begin
          // We got a new initial key, but want to do decryption.
          // We first must get the start key for decryption.
          dec_key_gen_d = key_init_new & (mode_i == AES_DEC);

          // Load input data to state
          state_sel_o = dec_key_gen_d ? STATE_CLEAR : STATE_INIT;
          state_we_o  = 1'b1;

          // Init key expand
          key_expand_clear_o = 1'b1;

          // Load full key
          key_full_sel_o = dec_key_gen_d ? KEY_FULL_ENC_INIT :
                     (mode_i == AES_ENC) ? KEY_FULL_ENC_INIT :
                                           KEY_FULL_DEC_INIT;
          key_full_we_o  = 1'b1;

          // Load num_rounds, round
          round_d      = '0;
          num_rounds_d = (key_len_i == AES_128) ? 4'd10 :
                         (key_len_i == AES_192) ? 4'd12 :
                                                  4'd14;

          idle_o      = 1'b0;
          idle_we_o   = 1'b1;
          start_we_o  = 1'b1;

          aes_ctrl_ns = INIT;
        end else begin
          if (key_clear_i) begin
            key_full_sel_o = KEY_FULL_CLEAR;
            key_full_we_o  = 1'b1;
            key_dec_sel_o  = KEY_DEC_CLEAR;
            key_dec_we_o   = 1'b1;
            key_clear_we_o = 1'b1;
          end
          if (data_out_clear_i) begin
            add_rk_sel_o        = ADD_RK_INIT;
            key_words_sel_o     = KEY_WORDS_ZERO;
            round_key_sel_o     = ROUND_KEY_DIRECT;
            data_out_we_o       = 1'b1;
            data_out_clear_we_o = 1'b1;
          end
        end
      end

      INIT: begin
        // Initial round: just add key to state
        state_we_o   = ~dec_key_gen_q;
        add_rk_sel_o = ADD_RK_INIT;

        // Select key words for initial add_round_key
        if (dec_key_gen_q) begin
          key_words_sel_o = KEY_WORDS_ZERO;
        end else begin
          unique case (key_len_i)
            AES_128:       key_words_sel_o = KEY_WORDS_0123;

            AES_192: begin
              if (AES192Enable) begin
                unique case (mode_i)
                  AES_ENC: key_words_sel_o = KEY_WORDS_0123;
                  AES_DEC: key_words_sel_o = KEY_WORDS_2345;
                  default: key_words_sel_o = key_words_sel_e'(1'bX);
                endcase
              end else begin
                key_words_sel_o = key_words_sel_e'(1'bX);
              end
            end

            AES_256: begin
              unique case (mode_i)
                AES_ENC:   key_words_sel_o = KEY_WORDS_0123;
                AES_DEC:   key_words_sel_o = KEY_WORDS_4567;
                default:   key_words_sel_o = key_words_sel_e'(1'bX);
              endcase
            end

            default: key_words_sel_o = key_words_sel_e'(1'bX);
          endcase
        end

        // Make key expand advance - AES-256 has two round keys available right from beginning
        if (key_len_i != AES_256) begin
          key_expand_step_o = 1'b1;
          key_full_we_o     = 1'b1;
        end

        // Clear data_in_new, key_init_new
        data_in_load = ~dec_key_gen_q;
        dec_key_gen  =  dec_key_gen_q;

        aes_ctrl_ns = ROUND;
      end

      ROUND: begin
        // Normal rounds
        state_we_o = ~dec_key_gen_q;

        // Select key words for add_round_key
        if (dec_key_gen_q) begin
          key_words_sel_o = KEY_WORDS_ZERO;
        end else begin
          unique case (key_len_i)
            AES_128:       key_words_sel_o = KEY_WORDS_0123;

            AES_192: begin
              if (AES192Enable) begin
                unique case (mode_i)
                  AES_ENC: key_words_sel_o = KEY_WORDS_2345;
                  AES_DEC: key_words_sel_o = KEY_WORDS_0123;
                  default: key_words_sel_o = key_words_sel_e'(1'bX);
                endcase
              end else begin
                key_words_sel_o = key_words_sel_e'(1'bX);
              end
            end

            AES_256: begin
              unique case (mode_i)
                AES_ENC:   key_words_sel_o = KEY_WORDS_4567;
                AES_DEC:   key_words_sel_o = KEY_WORDS_0123;
                default:   key_words_sel_o = key_words_sel_e'(1'bX);
              endcase
            end

            default: key_words_sel_o = key_words_sel_e'(1'bX);
          endcase
        end

        // Make key expand advance
        key_expand_step_o = 1'b1;
        key_full_we_o     = 1'b1;

        // Select round key: direct or mixed (equivalent inverse cipher)
        round_key_sel_o = (mode_i == AES_ENC) ? ROUND_KEY_DIRECT : ROUND_KEY_MIXED;

        // Update round
        round_d = round_q+1;

        // Are we doing the last regular round?
        if (round_q == num_rounds_regular) begin
          if (dec_key_gen_q) begin
            // Write decryption key and finish
            key_dec_we_o  = 1'b1;
            dec_key_gen_d = 1'b0;
            aes_ctrl_ns   = IDLE;
          end else begin
            aes_ctrl_ns   = FINISH;
          end
        end
      end

      FINISH: begin
        // Final round

        // Select key words for add_round_key
        if (dec_key_gen_q) begin
          key_words_sel_o = KEY_WORDS_ZERO;
        end else begin
          unique case (key_len_i)
            AES_128:       key_words_sel_o = KEY_WORDS_0123;

            AES_192: begin
              if (AES192Enable) begin
                unique case (mode_i)
                  AES_ENC: key_words_sel_o = KEY_WORDS_2345;
                  AES_DEC: key_words_sel_o = KEY_WORDS_0123;
                  default: key_words_sel_o = key_words_sel_e'(1'bX);
                endcase
              end else begin
                key_words_sel_o = key_words_sel_e'(1'bX);
              end
            end

            AES_256: begin
              unique case (mode_i)
                AES_ENC:   key_words_sel_o = KEY_WORDS_4567;
                AES_DEC:   key_words_sel_o = KEY_WORDS_0123;
                default:   key_words_sel_o = key_words_sel_e'(1'bX);
              endcase
            end

            default: key_words_sel_o = key_words_sel_e'(1'bX);
          endcase
        end

        // Skip mix_columns
        add_rk_sel_o = ADD_RK_FINAL;

        // Write ouput register and clear internal state
        if (!finish) begin
          stall_o       = 1'b1;
          stall_we_o    = 1'b1;
        end else begin
          stall_o       = 1'b0;
          stall_we_o    = 1'b1;
          data_out_we_o = 1'b1;
          aes_ctrl_ns   = IDLE;
          state_we_o    = 1'b1;
          state_sel_o   = STATE_CLEAR;
        end
      end

      default: aes_ctrl_ns = aes_ctrl_e'(1'bX);
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_fsm
    if (!rst_ni) begin
      aes_ctrl_cs   <= IDLE;
      round_q       <= '0;
      num_rounds_q  <= '0;
      dec_key_gen_q <= 1'b0;
    end else begin
      aes_ctrl_cs   <= aes_ctrl_ns;
      round_q       <= round_d;
      num_rounds_q  <= num_rounds_d;
      dec_key_gen_q <= dec_key_gen_d;
    end
  end

  // Use separate signal for number of regular rounds
  assign num_rounds_regular = num_rounds_q - 4'd2;

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

  // Clear once all input regs have been written
  assign input_ready_o     = ~data_in_new;
  assign input_ready_we_o  =  data_in_new | data_in_load;

  assign key_expand_mode_o  = (dec_key_gen_d || dec_key_gen_q) ? AES_ENC : mode_i;
  assign key_expand_round_o = round_d;

  // Trigger register, the control only ever clears these
  assign start_o             = 1'b0;
  assign key_clear_o         = 1'b0;
  assign data_out_clear_o    = 1'b0;

endmodule
