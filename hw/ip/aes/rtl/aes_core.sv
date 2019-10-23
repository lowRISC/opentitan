// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES core implementation

module aes_core #(
  parameter bit AES192Enable = 1
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
  logic    [31:0] data_in[4];
  logic     [3:0] data_in_qe;
  logic    [31:0] key_init[8];
  logic     [7:0] key_init_qe;

  mode_e          mode, key_expand_mode;
  key_len_e       key_len_q, key_len;

  logic     [7:0] state_init[16];
  logic     [7:0] state_d[16];
  logic     [7:0] state_q[16];
  logic           state_we;
  state_sel_e     state_sel;

  logic     [7:0] sub_bytes_out[16];
  logic     [7:0] shift_rows_out[16];
  logic     [7:0] mix_columns_out[16];
  logic     [7:0] add_round_key_in[16];
  logic     [7:0] add_round_key_out[16];
  add_rk_sel_e    add_round_key_in_sel;

  logic    [31:0] key_full_d[8];
  logic    [31:0] key_full_q[8];
  logic           key_full_we;
  key_full_sel_e  key_full_sel;
  logic    [31:0] key_dec_d[8];
  logic    [31:0] key_dec_q[8];
  logic           key_dec_we;
  key_dec_sel_e   key_dec_sel;
  logic    [31:0] key_expand_out[8];
  logic           key_expand_step;
  logic           key_expand_clear;
  logic     [3:0] key_expand_round;
  key_words_sel_e key_words_sel;
  logic    [31:0] key_words[4];
  logic     [7:0] key_bytes[16];
  logic     [7:0] key_mix_columns_out[16];
  logic     [7:0] round_key[16];
  round_key_sel_e round_key_sel;

  logic    [31:0] data_out_d[4];
  logic    [31:0] data_out_q[4];
  logic           data_out_we;
  logic     [3:0] data_out_re;

  // Unused signals
  logic    [31:0] unused_data_out_q[4];
  logic           unused_mode_qe;
  logic           unused_manual_start_trigger_qe;
  logic           unused_force_data_overwrite_qe;

  // Inputs
  assign key_init[0] = reg2hw.key[0].q;
  assign key_init[1] = reg2hw.key[1].q;
  assign key_init[2] = reg2hw.key[2].q;
  assign key_init[3] = reg2hw.key[3].q;
  assign key_init[4] = reg2hw.key[4].q;
  assign key_init[5] = reg2hw.key[5].q;
  assign key_init[6] = reg2hw.key[6].q;
  assign key_init[7] = reg2hw.key[7].q;

  assign key_init_qe = {reg2hw.key[7].qe, reg2hw.key[6].qe, reg2hw.key[5].qe, reg2hw.key[4].qe,
                        reg2hw.key[3].qe, reg2hw.key[2].qe, reg2hw.key[1].qe, reg2hw.key[0].qe};

  assign data_in[0] = reg2hw.data_in[0].q;
  assign data_in[1] = reg2hw.data_in[1].q;
  assign data_in[2] = reg2hw.data_in[2].q;
  assign data_in[3] = reg2hw.data_in[3].q;

  assign data_in_qe = {reg2hw.data_in[3].qe, reg2hw.data_in[2].qe,
                       reg2hw.data_in[1].qe, reg2hw.data_in[0].qe};

  always_comb begin : conv_data_in_to_state
    for (int i=0; i<4; i++) begin
      state_init[4*i+0] = data_in[i][ 7: 0];
      state_init[4*i+1] = data_in[i][15: 8];
      state_init[4*i+2] = data_in[i][23:16];
      state_init[4*i+3] = data_in[i][31:24];
    end
  end

  assign mode = mode_e'(reg2hw.ctrl.mode.q);

  assign key_len_q = key_len_e'(reg2hw.ctrl.key_len.q);
  always_comb begin : get_key_len
    unique case (key_len_q)
      AES_128: key_len = AES_128;
      AES_256: key_len = AES_256;
      AES_192: begin
        key_len = AES192Enable ? AES_192 : AES_128;
      end
      default: key_len = AES_128; // unsupported values are mapped to AES_128
    endcase
  end

  assign data_out_re = {reg2hw.data_out[3].re, reg2hw.data_out[2].re,
                        reg2hw.data_out[1].re, reg2hw.data_out[0].re};

  // Unused inputs
  // data_out is actually hwo, but we need hrw for hwre
  assign unused_data_out_q[0] = reg2hw.data_out[0].q;
  assign unused_data_out_q[1] = reg2hw.data_out[1].q;
  assign unused_data_out_q[2] = reg2hw.data_out[2].q;
  assign unused_data_out_q[3] = reg2hw.data_out[3].q;

  // key_len is hrw and hwqe, other fields of ctrl reg are hro and don't need hwqe
  assign unused_mode_qe                 = reg2hw.ctrl.mode.qe;
  assign unused_manual_start_trigger_qe = reg2hw.ctrl.manual_start_trigger.qe;
  assign unused_force_data_overwrite_qe = reg2hw.ctrl.force_data_overwrite.qe;

  // State registers
  always_comb begin : state_mux
    unique case (state_sel)
      STATE_INIT:  state_d = state_init;
      STATE_ROUND: state_d = add_round_key_out;
      STATE_CLEAR: state_d = '{default: '0};
      default      state_d = '{default: 'X};
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : state_reg
    if (!rst_ni) begin
      state_q <= '{default: '0};
    end else if (state_we) begin
      state_q <= state_d;
    end
  end

  // Cipher data path
  aes_sub_bytes aes_sub_bytes (
    .mode_i ( mode          ),
    .data_i ( state_q       ),
    .data_o ( sub_bytes_out )
  );

  aes_shift_rows aes_shift_rows (
    .mode_i ( mode           ),
    .data_i ( sub_bytes_out  ),
    .data_o ( shift_rows_out )
  );

  aes_mix_columns aes_mix_columns (
    .mode_i ( mode            ),
    .data_i ( shift_rows_out  ),
    .data_o ( mix_columns_out )
  );

  always_comb begin : add_round_key_in_mux
    unique case (add_round_key_in_sel)
      ADD_RK_INIT:  add_round_key_in = state_q;
      ADD_RK_ROUND: add_round_key_in = mix_columns_out;
      ADD_RK_FINAL: add_round_key_in = shift_rows_out;
      default:      add_round_key_in = '{default: 'X};
    endcase
  end

  always_comb begin : add_round_key
    for (int i=0; i<16; i++) begin
      add_round_key_out[i] = add_round_key_in[i] ^ round_key[i];
    end
  end

  // Full Key registers
  always_comb begin : key_full_mux
    unique case (key_full_sel)
      KEY_FULL_ENC_INIT: key_full_d = key_init;
      KEY_FULL_DEC_INIT: key_full_d = key_dec_q;
      KEY_FULL_ROUND:    key_full_d = key_expand_out;
      KEY_FULL_CLEAR:    key_full_d = '{default: '0};
      default:           key_full_d = '{default: 'X};
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : key_full_reg
    if (!rst_ni) begin
      key_full_q <= '{default: '0};
    end else if (key_full_we) begin
      key_full_q <= key_full_d;
    end
  end

  // Decryption Key registers
  always_comb begin : key_dec_mux
    unique case (key_dec_sel)
      KEY_DEC_EXPAND: key_dec_d = key_expand_out;
      KEY_DEC_CLEAR:  key_dec_d = '{default: '0};
      default:        key_dec_d = '{default: 'X};
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : key_dec_reg
    if (!rst_ni) begin
      key_dec_q <= '{default: '0};
    end else if (key_dec_we) begin
      key_dec_q <= key_dec_d;
    end
  end

  // Key expand data path
  aes_key_expand #(
  .AES192Enable (AES192Enable)
  ) aes_key_expand (
    .clk_i     ( clk_i            ),
    .rst_ni    ( rst_ni           ),
    .mode_i    ( key_expand_mode  ),
    .step_i    ( key_expand_step  ),
    .clear_i   ( key_expand_clear ),
    .round_i   ( key_expand_round ),
    .key_len_i ( key_len          ),
    .key_i     ( key_full_q       ),
    .key_o     ( key_expand_out   )
  );

  always_comb begin : key_words_mux
    unique case (key_words_sel)
      KEY_WORDS_0123: begin
        key_words[0] = key_full_q[0];
        key_words[1] = key_full_q[1];
        key_words[2] = key_full_q[2];
        key_words[3] = key_full_q[3];
      end
      KEY_WORDS_2345: begin
        if (AES192Enable) begin
          key_words[0] = key_full_q[2];
          key_words[1] = key_full_q[3];
          key_words[2] = key_full_q[4];
          key_words[3] = key_full_q[5];
        end else begin
          key_words    = '{default: 'X};
        end
      end
      KEY_WORDS_4567: begin
        key_words[0] = key_full_q[4];
        key_words[1] = key_full_q[5];
        key_words[2] = key_full_q[6];
        key_words[3] = key_full_q[7];
      end
      KEY_WORDS_ZERO: begin
        key_words    = '{default: '0};
      end
      default: begin
        key_words    = '{default: 'X};
      end
    endcase
  end

  always_comb begin : conv_key_words_to_bytes
    for (int i=0; i<4; i++) begin
      key_bytes[4*i+0] = key_words[i][ 7: 0];
      key_bytes[4*i+1] = key_words[i][15: 8];
      key_bytes[4*i+2] = key_words[i][23:16];
      key_bytes[4*i+3] = key_words[i][31:24];
    end
  end

  aes_mix_columns aes_key_mix_columns (
    .mode_i ( AES_DEC             ),
    .data_i ( key_bytes           ),
    .data_o ( key_mix_columns_out )
  );

  always_comb begin : round_key_mux
    unique case (round_key_sel)
      ROUND_KEY_DIRECT: round_key = key_bytes;
      ROUND_KEY_MIXED:  round_key = key_mix_columns_out;
      default:          round_key = '{default: 'X};
    endcase
  end

  // Output registers
  always_comb begin : conv_add_rk_out_to_data_out
    for (int i=0; i<4; i++) begin
      data_out_d[i] = {add_round_key_out[4*i+3], add_round_key_out[4*i+2],
                       add_round_key_out[4*i+1], add_round_key_out[4*i+0]};
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : data_out_reg
    if (!rst_ni) begin
      data_out_q <= '{default: '0};
    end else if (data_out_we) begin
      data_out_q <= data_out_d;
    end
  end

  // Control
  aes_control #(
  .AES192Enable (AES192Enable)
  ) aes_control (
    .clk_i                  ( clk_i                              ),
    .rst_ni                 ( rst_ni                             ),

    .mode_i                 ( mode                               ),
    .key_len_i              ( key_len                            ),
    .force_data_overwrite_i ( reg2hw.ctrl.force_data_overwrite.q ),
    .manual_start_trigger_i ( reg2hw.ctrl.manual_start_trigger.q ),
    .start_i                ( reg2hw.trigger.start.q             ),
    .key_clear_i            ( reg2hw.trigger.key_clear.q         ),
    .data_out_clear_i       ( reg2hw.trigger.data_out_clear.q    ),

    .data_in_qe_i           ( data_in_qe                         ),
    .key_init_qe_i          ( key_init_qe                        ),
    .data_out_re_i          ( data_out_re                        ),

    .state_sel_o            ( state_sel                          ),
    .state_we_o             ( state_we                           ),
    .add_rk_sel_o           ( add_round_key_in_sel               ),
    .key_expand_mode_o      ( key_expand_mode                    ),
    .key_full_sel_o         ( key_full_sel                       ),
    .key_full_we_o          ( key_full_we                        ),
    .key_dec_sel_o          ( key_dec_sel                        ),
    .key_dec_we_o           ( key_dec_we                         ),
    .key_expand_step_o      ( key_expand_step                    ),
    .key_expand_clear_o     ( key_expand_clear                   ),
    .key_expand_round_o     ( key_expand_round                   ),
    .key_words_sel_o        ( key_words_sel                      ),
    .round_key_sel_o        ( round_key_sel                      ),

    .data_out_we_o          ( data_out_we                        ),

    .start_o                ( hw2reg.trigger.start.d             ),
    .start_we_o             ( hw2reg.trigger.start.de            ),
    .key_clear_o            ( hw2reg.trigger.key_clear.d         ),
    .key_clear_we_o         ( hw2reg.trigger.key_clear.de        ),
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

  // Outputs
  assign hw2reg.data_out[0].d = data_out_q[0];
  assign hw2reg.data_out[1].d = data_out_q[1];
  assign hw2reg.data_out[2].d = data_out_q[2];
  assign hw2reg.data_out[3].d = data_out_q[3];

  assign hw2reg.ctrl.key_len.d  = {key_len};
  assign hw2reg.ctrl.key_len.de = reg2hw.ctrl.key_len.qe;

endmodule
