// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES cipher core implementation
//
// This module contains the AES cipher core including, state register, full key and decryption key
// registers as well as key expand module and control unit.

`include "prim_assert.sv"

module aes_cipher_core #(
  parameter bit AES192Enable = 1,
  parameter     SBoxImpl     = "lut"
) (
  input  logic                 clk_i,
  input  logic                 rst_ni,

  // Input handshake signals
  input  logic                 in_valid_i,
  output logic                 in_ready_o,

  // Output handshake signals
  output logic                 out_valid_o,
  input  logic                 out_ready_i,

  // Control and sync signals
  input  aes_pkg::ciph_op_e    op_i,
  input  aes_pkg::key_len_e    key_len_i,
  input  logic                 start_i,
  input  logic                 dec_key_gen_i,
  output logic                 dec_key_gen_o,
  input  logic                 key_clear_i,
  output logic                 key_clear_o,
  input  logic                 data_out_clear_i, // Re-use the cipher core muxes.
  output logic                 data_out_clear_o,

  // I/O data & initial key
  input  logic [3:0][3:0][7:0] state_init_i,
  input  logic     [7:0][31:0] key_init_i,
  output logic [3:0][3:0][7:0] state_o
);

  import aes_pkg::*;

  // Signals
  logic [3:0][3:0][7:0] state_d;
  logic [3:0][3:0][7:0] state_q;
  logic                 state_we;
  state_sel_e           state_sel;

  logic [3:0][3:0][7:0] sub_bytes_out;
  logic [3:0][3:0][7:0] shift_rows_out;
  logic [3:0][3:0][7:0] mix_columns_out;
  logic [3:0][3:0][7:0] add_round_key_in;
  logic [3:0][3:0][7:0] add_round_key_out;
  add_rk_sel_e          add_round_key_in_sel;

  logic     [7:0][31:0] key_full_d;
  logic     [7:0][31:0] key_full_q;
  logic                 key_full_we;
  key_full_sel_e        key_full_sel;
  logic     [7:0][31:0] key_dec_d;
  logic     [7:0][31:0] key_dec_q;
  logic                 key_dec_we;
  key_dec_sel_e         key_dec_sel;
  logic     [7:0][31:0] key_expand_out;
  ciph_op_e             key_expand_op;
  logic                 key_expand_step;
  logic                 key_expand_clear;
  logic           [3:0] key_expand_round;
  key_words_sel_e       key_words_sel;
  logic     [3:0][31:0] key_words;
  logic [3:0][3:0][7:0] key_bytes;
  logic [3:0][3:0][7:0] key_mix_columns_out;
  logic [3:0][3:0][7:0] round_key;
  round_key_sel_e       round_key_sel;

  //////////
  // Data //
  //////////

  // State registers
  always_comb begin : state_mux
    unique case (state_sel)
      STATE_INIT:  state_d = state_init_i;
      STATE_ROUND: state_d = add_round_key_out;
      STATE_CLEAR: state_d = '0;
      default:     state_d = '0;
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : state_reg
    if (!rst_ni) begin
      state_q <= '0;
    end else if (state_we) begin
      state_q <= state_d;
    end
  end

  // Cipher data path
  aes_sub_bytes #(
    .SBoxImpl ( SBoxImpl )
  ) aes_sub_bytes (
    .op_i   ( op_i          ),
    .data_i ( state_q       ),
    .data_o ( sub_bytes_out )
  );

  aes_shift_rows aes_shift_rows (
    .op_i   ( op_i           ),
    .data_i ( sub_bytes_out  ),
    .data_o ( shift_rows_out )
  );

  aes_mix_columns aes_mix_columns (
    .op_i   ( op_i            ),
    .data_i ( shift_rows_out  ),
    .data_o ( mix_columns_out )
  );

  always_comb begin : add_round_key_in_mux
    unique case (add_round_key_in_sel)
      ADD_RK_INIT:  add_round_key_in = state_q;
      ADD_RK_ROUND: add_round_key_in = mix_columns_out;
      ADD_RK_FINAL: add_round_key_in = shift_rows_out;
      default:      add_round_key_in = state_q;
    endcase
  end

  assign add_round_key_out = add_round_key_in ^ round_key;

  /////////
  // Key //
  /////////

  // Full Key registers
  always_comb begin : key_full_mux
    unique case (key_full_sel)
      KEY_FULL_ENC_INIT: key_full_d = key_init_i;
      KEY_FULL_DEC_INIT: key_full_d = key_dec_q;
      KEY_FULL_ROUND:    key_full_d = key_expand_out;
      KEY_FULL_CLEAR:    key_full_d = '0;
      default:           key_full_d = '0;
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : key_full_reg
    if (!rst_ni) begin
      key_full_q <= '0;
    end else if (key_full_we) begin
      key_full_q <= key_full_d;
    end
  end

  // Decryption Key registers
  always_comb begin : key_dec_mux
    unique case (key_dec_sel)
      KEY_DEC_EXPAND: key_dec_d = key_expand_out;
      KEY_DEC_CLEAR:  key_dec_d = '0;
      default:        key_dec_d = '0;
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : key_dec_reg
    if (!rst_ni) begin
      key_dec_q <= '0;
    end else if (key_dec_we) begin
      key_dec_q <= key_dec_d;
    end
  end

  // Key expand data path
  aes_key_expand #(
    .AES192Enable ( AES192Enable ),
    .SBoxImpl     ( SBoxImpl     )
  ) aes_key_expand (
    .clk_i     ( clk_i            ),
    .rst_ni    ( rst_ni           ),
    .op_i      ( key_expand_op    ),
    .step_i    ( key_expand_step  ),
    .clear_i   ( key_expand_clear ),
    .round_i   ( key_expand_round ),
    .key_len_i ( key_len_i        ),
    .key_i     ( key_full_q       ),
    .key_o     ( key_expand_out   )
  );

  always_comb begin : key_words_mux
    unique case (key_words_sel)
      KEY_WORDS_0123: key_words = key_full_q[3:0];
      KEY_WORDS_2345: key_words = AES192Enable ? key_full_q[5:2] : '0;
      KEY_WORDS_4567: key_words = key_full_q[7:4];
      KEY_WORDS_ZERO: key_words = '0;
      default:        key_words = '0;
    endcase
  end

  // Convert words to bytes (every key word contains one column)
  assign key_bytes = aes_transpose(key_words);

  aes_mix_columns aes_key_mix_columns (
    .op_i   ( CIPH_INV            ),
    .data_i ( key_bytes           ),
    .data_o ( key_mix_columns_out )
  );

  always_comb begin : round_key_mux
    unique case (round_key_sel)
      ROUND_KEY_DIRECT: round_key = key_bytes;
      ROUND_KEY_MIXED:  round_key = key_mix_columns_out;
      default:          round_key = key_bytes;
    endcase
  end

  /////////////
  // Control //
  /////////////

  // Control
  aes_cipher_control aes_cipher_control (
    .clk_i                  ( clk_i                ),
    .rst_ni                 ( rst_ni               ),

    .in_valid_i             ( in_valid_i           ),
    .in_ready_o             ( in_ready_o           ),
    .out_valid_o            ( out_valid_o          ),
    .out_ready_i            ( out_ready_i          ),
    .op_i                   ( op_i                 ),
    .key_len_i              ( key_len_i            ),
    .start_i                ( start_i              ),
    .dec_key_gen_i          ( dec_key_gen_i        ),
    .dec_key_gen_o          ( dec_key_gen_o        ),
    .key_clear_i            ( key_clear_i          ),
    .key_clear_o            ( key_clear_o          ),
    .data_out_clear_i       ( data_out_clear_i     ),
    .data_out_clear_o       ( data_out_clear_o     ),

    .state_sel_o            ( state_sel            ),
    .state_we_o             ( state_we             ),
    .add_rk_sel_o           ( add_round_key_in_sel ),
    .key_expand_op_o        ( key_expand_op        ),
    .key_full_sel_o         ( key_full_sel         ),
    .key_full_we_o          ( key_full_we          ),
    .key_dec_sel_o          ( key_dec_sel          ),
    .key_dec_we_o           ( key_dec_we           ),
    .key_expand_step_o      ( key_expand_step      ),
    .key_expand_clear_o     ( key_expand_clear     ),
    .key_expand_round_o     ( key_expand_round     ),
    .key_words_sel_o        ( key_words_sel        ),
    .round_key_sel_o        ( round_key_sel        )
  );

  /////////////
  // Outputs //
  /////////////

  // The output of the last round is not stored into the state register but forwarded directly.
  assign state_o = add_round_key_out;

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid
  `ASSERT(AesStateSelValid, state_sel inside {
      STATE_INIT,
      STATE_ROUND,
      STATE_CLEAR
      })
  `ASSERT(AesAddRKSelValid, add_round_key_in_sel inside {
      ADD_RK_INIT,
      ADD_RK_ROUND,
      ADD_RK_FINAL
      })
  `ASSERT_KNOWN(AesKeyFullSelKnown, key_full_sel)
  `ASSERT_KNOWN(AesKeyDecSelKnown, key_dec_sel)
  `ASSERT_KNOWN(AesKeyWordsSelKnown, key_words_sel)
  `ASSERT_KNOWN(AesRoundKeySelKnown, round_key_sel)

endmodule
