// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES core implementation

module aes_core #(
  parameter bit AES192Enable = 1,
  parameter     SBoxImpl     = "lut"
) (
  input                            clk_i,
  input                            rst_ni,

  // Bus Interface
  input  aes_reg_pkg::aes_reg2hw_t reg2hw,
  output aes_reg_pkg::aes_hw2reg_t hw2reg
);

  import aes_reg_pkg::*;
  import aes_pkg::*;

  // Signals
  logic     [3:0][31:0] data_in;
  logic     [3:0]       data_in_qe;
  logic                 data_in_we;
  logic     [7:0][31:0] key_init;
  logic     [7:0]       key_init_qe;

  logic                 ctrl_qe;
  logic                 ctrl_we;
  mode_e                mode_d, mode_q;
  key_len_e             key_len;
  key_len_e             key_len_d, key_len_q;
  logic                 manual_start_trigger_q;
  logic                 force_data_overwrite_q;

  logic [3:0][3:0][7:0] state_init;
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

  logic     [7:0][31:0] key_init_d;
  logic     [7:0][31:0] key_init_q;
  logic     [7:0]       key_init_we;
  key_init_sel_e        key_init_sel;
  logic     [7:0][31:0] key_full_d;
  logic     [7:0][31:0] key_full_q;
  logic                 key_full_we;
  key_full_sel_e        key_full_sel;
  logic     [7:0][31:0] key_dec_d;
  logic     [7:0][31:0] key_dec_q;
  logic                 key_dec_we;
  key_dec_sel_e         key_dec_sel;
  logic     [7:0][31:0] key_expand_out;
  mode_e                key_expand_mode;
  logic                 key_expand_step;
  logic                 key_expand_clear;
  logic           [3:0] key_expand_round;
  key_words_sel_e       key_words_sel;
  logic     [3:0][31:0] key_words;
  logic [3:0][3:0][7:0] key_bytes;
  logic [3:0][3:0][7:0] key_mix_columns_out;
  logic [3:0][3:0][7:0] round_key;
  round_key_sel_e       round_key_sel;

  logic     [3:0][31:0] data_out_d;
  logic     [3:0][31:0] data_out_q;
  logic                 data_out_we;
  logic           [3:0] data_out_re;

  // Unused signals
  logic     [3:0][31:0] unused_data_out_q;

  ////////////
  // Inputs //
  ////////////

  // Inputs
  always_comb begin : key_init_get
    for (int i=0; i<8; i++) begin
      key_init[i]    = reg2hw.key[i].q;
      key_init_qe[i] = reg2hw.key[i].qe;
    end
  end

  always_comb begin : data_in_get
    for (int i=0; i<4; i++) begin
      data_in[i]    = reg2hw.data_in[i].q;
      data_in_qe[i] = reg2hw.data_in[i].qe;
    end
  end

  always_comb begin : data_out_get
    for (int i=0; i<4; i++) begin
      // data_out is actually hwo, but we need hrw for hwre
      unused_data_out_q[i] = reg2hw.data_out[i].q;
      data_out_re[i]       = reg2hw.data_out[i].re;
    end
  end

  assign mode_d = mode_e'(reg2hw.ctrl.mode.q);

  assign key_len = key_len_e'(reg2hw.ctrl.key_len.q);
  always_comb begin : get_key_len
    unique case (key_len)
      AES_128: key_len_d = AES_128;
      AES_256: key_len_d = AES_256;
      AES_192: key_len_d = AES192Enable ? AES_192 : AES_128;
      default: key_len_d = AES_128; // unsupported values are mapped to AES_128
    endcase
  end

  assign ctrl_qe = reg2hw.ctrl.mode.qe & reg2hw.ctrl.key_len.qe &
      reg2hw.ctrl.manual_start_trigger.qe & reg2hw.ctrl.force_data_overwrite.qe;

  //////////
  // Data //
  //////////

  // Convert input data to state (every input data word contains one state column)
  assign state_init = aes_transpose(data_in);

  // State registers
  always_comb begin : state_mux
    unique case (state_sel)
      STATE_INIT:  state_d = state_init;
      STATE_ROUND: state_d = add_round_key_out;
      STATE_CLEAR: state_d = '0;
      default:     state_d = state_init;
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
  .SBoxImpl     ( SBoxImpl )
  ) aes_sub_bytes (
    .mode_i ( mode_q        ),
    .data_i ( state_q       ),
    .data_o ( sub_bytes_out )
  );

  aes_shift_rows aes_shift_rows (
    .mode_i ( mode_q         ),
    .data_i ( sub_bytes_out  ),
    .data_o ( shift_rows_out )
  );

  aes_mix_columns aes_mix_columns (
    .mode_i ( mode_q          ),
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

  // Initial Key registers
  always_comb begin : key_init_mux
    unique case (key_init_sel)
      KEY_INIT_INPUT: key_init_d = key_init;
      KEY_INIT_CLEAR: key_init_d = '0;
      default:        key_init_d = key_init;
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : key_init_reg
    if (!rst_ni) begin
      key_init_q <= '0;
    end else begin
      for (int i=0; i<8; i++) begin
        if (key_init_we[i]) begin
          key_init_q[i] <= key_init_d[i];
        end
      end
    end
  end

  // Full Key registers
  always_comb begin : key_full_mux
    unique case (key_full_sel)
      KEY_FULL_ENC_INIT: key_full_d = key_init_q;
      KEY_FULL_DEC_INIT: key_full_d = key_dec_q;
      KEY_FULL_ROUND:    key_full_d = key_expand_out;
      KEY_FULL_CLEAR:    key_full_d = '0;
      default:           key_full_d = key_init_q;
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
      default:        key_dec_d = key_expand_out;
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
    .mode_i    ( key_expand_mode  ),
    .step_i    ( key_expand_step  ),
    .clear_i   ( key_expand_clear ),
    .round_i   ( key_expand_round ),
    .key_len_i ( key_len_q        ),
    .key_i     ( key_full_q       ),
    .key_o     ( key_expand_out   )
  );

  always_comb begin : key_words_mux
    unique case (key_words_sel)
      KEY_WORDS_0123: key_words = key_full_q[3:0];
      KEY_WORDS_2345: key_words = AES192Enable ? key_full_q[5:2] : key_full_q[3:0];
      KEY_WORDS_4567: key_words = key_full_q[7:4];
      KEY_WORDS_ZERO: key_words = '0;
      default:        key_words = key_full_q[3:0];
    endcase
  end

  // Convert words to bytes (every key word contains one column)
  assign key_bytes = aes_transpose(key_words);

  aes_mix_columns aes_key_mix_columns (
    .mode_i ( AES_DEC             ),
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
  aes_control aes_control (
    .clk_i                  ( clk_i                              ),
    .rst_ni                 ( rst_ni                             ),

    .mode_i                 ( mode_q                             ),
    .key_len_i              ( key_len_q                          ),
    .manual_start_trigger_i ( manual_start_trigger_q             ),
    .force_data_overwrite_i ( force_data_overwrite_q             ),
    .start_i                ( reg2hw.trigger.start.q             ),
    .key_clear_i            ( reg2hw.trigger.key_clear.q         ),
    .data_in_clear_i        ( reg2hw.trigger.data_in_clear.q     ),
    .data_out_clear_i       ( reg2hw.trigger.data_out_clear.q    ),

    .data_in_qe_i           ( data_in_qe                         ),
    .key_init_qe_i          ( key_init_qe                        ),
    .data_out_re_i          ( data_out_re                        ),

    .state_sel_o            ( state_sel                          ),
    .state_we_o             ( state_we                           ),
    .add_rk_sel_o           ( add_round_key_in_sel               ),

    .key_expand_mode_o      ( key_expand_mode                    ),
    .key_init_sel_o         ( key_init_sel                       ),
    .key_init_we_o          ( key_init_we                        ),
    .key_full_sel_o         ( key_full_sel                       ),
    .key_full_we_o          ( key_full_we                        ),
    .key_dec_sel_o          ( key_dec_sel                        ),
    .key_dec_we_o           ( key_dec_we                         ),
    .key_expand_step_o      ( key_expand_step                    ),
    .key_expand_clear_o     ( key_expand_clear                   ),
    .key_expand_round_o     ( key_expand_round                   ),
    .key_words_sel_o        ( key_words_sel                      ),
    .round_key_sel_o        ( round_key_sel                      ),

    .data_in_we_o           ( data_in_we                         ),
    .data_out_we_o          ( data_out_we                        ),

    .start_o                ( hw2reg.trigger.start.d             ),
    .start_we_o             ( hw2reg.trigger.start.de            ),
    .key_clear_o            ( hw2reg.trigger.key_clear.d         ),
    .key_clear_we_o         ( hw2reg.trigger.key_clear.de        ),
    .data_in_clear_o        ( hw2reg.trigger.data_in_clear.d     ),
    .data_in_clear_we_o     ( hw2reg.trigger.data_in_clear.de    ),
    .data_out_clear_o       ( hw2reg.trigger.data_out_clear.d    ),
    .data_out_clear_we_o    ( hw2reg.trigger.data_out_clear.de   ),

    .output_valid_o         ( hw2reg.status.output_valid.d       ),
    .output_valid_we_o      ( hw2reg.status.output_valid.de      ),
    .input_ready_o          ( hw2reg.status.input_ready.d        ),
    .input_ready_we_o       ( hw2reg.status.input_ready.de       ),
    .idle_o                 ( hw2reg.status.idle.d               ),
    .idle_we_o              ( hw2reg.status.idle.de              ),
    .stall_o                ( hw2reg.status.stall.d              ),
    .stall_we_o             ( hw2reg.status.stall.de             )
  );

  // Input data register clear
  always_comb begin : data_in_reg_clear
    for (int i=0; i<4; i++) begin
      hw2reg.data_in[i].d  = '0;
      hw2reg.data_in[i].de = data_in_we;
    end
  end

  // Control register
  assign ctrl_we = ctrl_qe & hw2reg.status.idle.d;

  always_ff @(posedge clk_i or negedge rst_ni) begin : ctrl_reg
    if (!rst_ni) begin
      mode_q                 <= AES_ENC;
      key_len_q              <= AES_128;
      manual_start_trigger_q <= '0;
      force_data_overwrite_q <= '0;
    end else if (ctrl_we) begin
      mode_q                 <= mode_d;
      key_len_q              <= key_len_d;
      manual_start_trigger_q <= reg2hw.ctrl.manual_start_trigger.q;
      force_data_overwrite_q <= reg2hw.ctrl.force_data_overwrite.q;
    end
  end

  /////////////
  // Outputs //
  /////////////

  // Convert output state to output data (every state column corresponds to one output word)
  assign data_out_d = aes_transpose(add_round_key_out);

  always_ff @(posedge clk_i or negedge rst_ni) begin : data_out_reg
    if (!rst_ni) begin
      data_out_q <= '0;
    end else if (data_out_we) begin
      data_out_q <= data_out_d;
    end
  end

  // Outputs
  always_comb begin : key_reg_put
    for (int i=0; i<8; i++) begin
      hw2reg.key[i].d  = key_init_q[i];
    end
  end

  always_comb begin : data_out_put
    for (int i=0; i<4; i++) begin
      hw2reg.data_out[i].d = data_out_q[i];
    end
  end

  assign hw2reg.ctrl.key_len.d  = {key_len_q};

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid
  `ASSERT_KNOWN(AesModeKnown, mode_q, clk_i, !rst_ni)
  `ASSERT(AesKeyLenValid, key_len_q inside {
      AES_128,
      AES_192,
      AES_256
      }, clk_i, !rst_ni)
  `ASSERT(AesStateSelValid, state_sel inside {
      STATE_INIT,
      STATE_ROUND,
      STATE_CLEAR
      }, clk_i, !rst_ni)
  `ASSERT(AesAddRKSelValid, add_round_key_in_sel inside {
      ADD_RK_INIT,
      ADD_RK_ROUND,
      ADD_RK_FINAL
      }, clk_i, !rst_ni)
  `ASSERT_KNOWN(AesKeyInitSelKnown, key_init_sel, clk_i, !rst_ni)
  `ASSERT_KNOWN(AesKeyFullSelKnown, key_full_sel, clk_i, !rst_ni)
  `ASSERT_KNOWN(AesKeyDecSelKnown, key_dec_sel, clk_i, !rst_ni)
  `ASSERT_KNOWN(AesKeyWordsSelKnown, key_words_sel, clk_i, !rst_ni)
  `ASSERT_KNOWN(AesRoundKeySelKnown, round_key_sel, clk_i, !rst_ni)

endmodule
