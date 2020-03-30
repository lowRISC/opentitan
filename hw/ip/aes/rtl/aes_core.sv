// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES core implementation

`include "prim_assert.sv"

module aes_core #(
  parameter bit AES192Enable = 1,
  parameter     SBoxImpl     = "lut"
) (
  input  logic                     clk_i,
  input  logic                     rst_ni,

  // PRNG Interface
  output logic                     prng_data_req_o,
  input  logic                     prng_data_ack_i,
  input  logic [63:0]              prng_data_i,

  output logic                     prng_reseed_req_o,
  input  logic                     prng_reseed_ack_i,

  // Bus Interface
  input  aes_reg_pkg::aes_reg2hw_t reg2hw,
  output aes_reg_pkg::aes_hw2reg_t hw2reg
);

  import aes_reg_pkg::*;
  import aes_pkg::*;

  // Signals
  logic                 ctrl_qe;
  logic                 ctrl_we;
  aes_op_e              aes_op_d, aes_op_q;
  aes_mode_e            aes_mode;
  aes_mode_e            aes_mode_d, aes_mode_q;
  ciph_op_e             cipher_op;
  key_len_e             key_len;
  key_len_e             key_len_d, key_len_q;
  logic                 manual_operation_q;

  logic [3:0][3:0][7:0] state_in;
  si_sel_e              state_in_sel;
  logic [3:0][3:0][7:0] add_state_in;
  add_si_sel_e          add_state_in_sel;

  logic [3:0][3:0][7:0] state_init;
  logic [3:0][3:0][7:0] state_done;

  logic     [7:0][31:0] key_init;
  logic     [7:0]       key_init_qe;
  logic     [7:0][31:0] key_init_d;
  logic     [7:0][31:0] key_init_q;
  logic     [7:0]       key_init_we;
  key_init_sel_e        key_init_sel;

  logic     [3:0][31:0] iv;
  logic     [3:0]       iv_qe;
  logic     [7:0][15:0] iv_d;
  logic     [7:0][15:0] iv_q;
  logic     [7:0]       iv_we;
  iv_sel_e              iv_sel;

  logic     [7:0][15:0] ctr;
  logic     [7:0]       ctr_we;
  logic                 ctr_incr;
  logic                 ctr_ready;

  logic     [3:0][31:0] data_in_prev_d;
  logic     [3:0][31:0] data_in_prev_q;
  logic                 data_in_prev_we;
  dip_sel_e             data_in_prev_sel;

  logic     [3:0][31:0] data_in;
  logic     [3:0]       data_in_qe;
  logic                 data_in_we;

  logic [3:0][3:0][7:0] add_state_out;
  add_so_sel_e          add_state_out_sel;

  logic     [3:0][31:0] data_out_d;
  logic     [3:0][31:0] data_out_q;
  logic                 data_out_we;
  logic           [3:0] data_out_re;

  logic                 cipher_in_valid;
  logic                 cipher_in_ready;
  logic                 cipher_out_valid;
  logic                 cipher_out_ready;
  logic                 cipher_crypt;
  logic                 cipher_crypt_busy;
  logic                 cipher_dec_key_gen;
  logic                 cipher_dec_key_gen_busy;
  logic                 cipher_key_clear;
  logic                 cipher_key_clear_busy;
  logic                 cipher_data_out_clear;
  logic                 cipher_data_out_clear_busy;

  // Unused signals
  logic     [3:0][31:0] unused_data_out_q;

  ////////////
  // Inputs //
  ////////////

  always_comb begin : key_init_get
    for (int i=0; i<8; i++) begin
      key_init[i]    = reg2hw.key[i].q;
      key_init_qe[i] = reg2hw.key[i].qe;
    end
  end

  always_comb begin : iv_get
    for (int i=0; i<4; i++) begin
      iv[i]    = reg2hw.iv[i].q;
      iv_qe[i] = reg2hw.iv[i].qe;
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

  assign aes_op_d = aes_op_e'(reg2hw.ctrl.operation.q);

  assign aes_mode = aes_mode_e'(reg2hw.ctrl.mode.q);
  always_comb begin : mode_get
    unique case (aes_mode)
      AES_ECB: aes_mode_d = AES_ECB;
      AES_CBC: aes_mode_d = AES_CBC;
      AES_CTR: aes_mode_d = AES_CTR;
      default: aes_mode_d = AES_ECB; // unsupported values are mapped to AES_ECB
    endcase
  end

  assign key_len = key_len_e'(reg2hw.ctrl.key_len.q);
  always_comb begin : key_len_get
    unique case (key_len)
      AES_128: key_len_d = AES_128;
      AES_256: key_len_d = AES_256;
      AES_192: key_len_d = AES192Enable ? AES_192 : AES_128;
      default: key_len_d = AES_128; // unsupported values are mapped to AES_128
    endcase
  end

  assign ctrl_qe = reg2hw.ctrl.operation.qe & reg2hw.ctrl.mode.qe & reg2hw.ctrl.key_len.qe &
      reg2hw.ctrl.manual_operation.qe;

  //////////////////////
  // Key, IV and Data //
  //////////////////////

  // Initial Key registers
  always_comb begin : key_init_mux
    unique case (key_init_sel)
      KEY_INIT_INPUT: key_init_d = key_init;
      KEY_INIT_CLEAR: key_init_d = {prng_data_i, prng_data_i, prng_data_i, prng_data_i};
      default:        key_init_d = {prng_data_i, prng_data_i, prng_data_i, prng_data_i};
    endcase
  end

  always_ff @(posedge clk_i) begin : key_init_reg
    for (int i=0; i<8; i++) begin
      if (key_init_we[i]) begin
        key_init_q[i] <= key_init_d[i];
      end
    end
  end

  // IV registers
  always_comb begin : iv_mux
    unique case (iv_sel)
      IV_INPUT:        iv_d = iv;
      IV_DATA_OUT:     iv_d = data_out_d;
      IV_DATA_IN_PREV: iv_d = data_in_prev_q;
      IV_CTR:          iv_d = ctr;
      IV_CLEAR:        iv_d = {prng_data_i, prng_data_i};
      default:         iv_d = {prng_data_i, prng_data_i};
    endcase
  end

  always_ff @(posedge clk_i) begin : iv_reg
    for (int i=0; i<8; i++) begin
      if (iv_we[i]) begin
        iv_q[i] <= iv_d[i];
      end
    end
  end

  // Previous input data register
  always_comb begin : data_in_prev_mux
    unique case (data_in_prev_sel)
      DIP_DATA_IN: data_in_prev_d = data_in;
      DIP_CLEAR:   data_in_prev_d = {prng_data_i, prng_data_i};
      default:     data_in_prev_d = {prng_data_i, prng_data_i};
    endcase
  end

  always_ff @(posedge clk_i) begin : data_in_prev_reg
    if (data_in_prev_we) begin
      data_in_prev_q <= data_in_prev_d;
    end
  end

  /////////////
  // Counter //
  /////////////

  aes_ctr aes_ctr (
    .clk_i    ( clk_i     ),
    .rst_ni   ( rst_ni    ),

    .incr_i   ( ctr_incr  ),
    .ready_o  ( ctr_ready ),

    .ctr_i    ( iv_q      ),
    .ctr_o    ( ctr       ),
    .ctr_we_o ( ctr_we    )
  );

  /////////////////
  // Cipher Core //
  /////////////////

  // Cipher core operation
  assign cipher_op = (aes_mode_q == AES_ECB && aes_op_q == AES_ENC) ? CIPH_FWD :
                     (aes_mode_q == AES_ECB && aes_op_q == AES_DEC) ? CIPH_INV :
                     (aes_mode_q == AES_CBC && aes_op_q == AES_ENC) ? CIPH_FWD :
                     (aes_mode_q == AES_CBC && aes_op_q == AES_DEC) ? CIPH_INV :
                     (aes_mode_q == AES_CTR)                        ? CIPH_FWD : CIPH_FWD;

  // Mux for state input
  always_comb begin : state_in_mux
    unique case (state_in_sel)
      SI_ZERO: state_in = '0;
      SI_DATA: state_in = aes_transpose(data_in);
      default: state_in = '0;
    endcase
  end

  // Mux for addition to state input
  always_comb begin : add_state_in_mux
    unique case (add_state_in_sel)
      ADD_SI_ZERO: add_state_in = '0;
      ADD_SI_IV:   add_state_in = aes_transpose(iv_q);
      default:     add_state_in = '0;
    endcase
  end

  // Convert input data to state format (every input data word contains one state column)
  assign state_init = state_in ^ add_state_in;

  // Cipher core
  aes_cipher_core #(
    .AES192Enable ( AES192Enable ),
    .SBoxImpl     ( SBoxImpl     )
  ) aes_cipher_core (
    .clk_i            ( clk_i                      ),
    .rst_ni           ( rst_ni                     ),

    .in_valid_i       ( cipher_in_valid            ),
    .in_ready_o       ( cipher_in_ready            ),
    .out_valid_o      ( cipher_out_valid           ),
    .out_ready_i      ( cipher_out_ready           ),
    .op_i             ( cipher_op                  ),
    .key_len_i        ( key_len_q                  ),
    .crypt_i          ( cipher_crypt               ),
    .crypt_o          ( cipher_crypt_busy          ),
    .dec_key_gen_i    ( cipher_dec_key_gen         ),
    .dec_key_gen_o    ( cipher_dec_key_gen_busy    ),
    .key_clear_i      ( cipher_key_clear           ),
    .key_clear_o      ( cipher_key_clear_busy      ),
    .data_out_clear_i ( cipher_data_out_clear      ),
    .data_out_clear_o ( cipher_data_out_clear_busy ),

    .prng_data_i      ( prng_data_i                ),

    .state_init_i     ( state_init                 ),
    .key_init_i       ( key_init_q                 ),
    .state_o          ( state_done                 )
  );

  // Mux for addition to state output
  always_comb begin : add_state_out_mux
    unique case (add_state_out_sel)
      ADD_SO_ZERO: add_state_out = '0;
      ADD_SO_IV:   add_state_out = aes_transpose(iv_q);
      ADD_SO_DIP:  add_state_out = aes_transpose(data_in_prev_q);
      default:     add_state_out = '0;
    endcase
  end

  // Convert output state to output data format (every state column corresponds to one output word)
  assign data_out_d = aes_transpose(state_done ^ add_state_out);

  /////////////
  // Control //
  /////////////

  // Control
  aes_control aes_control (
    .clk_i                   ( clk_i                            ),
    .rst_ni                  ( rst_ni                           ),

    .op_i                    ( aes_op_q                         ),
    .mode_i                  ( aes_mode_q                       ),
    .cipher_op_i             ( cipher_op                        ),
    .manual_operation_i      ( manual_operation_q               ),
    .start_i                 ( reg2hw.trigger.start.q           ),
    .key_clear_i             ( reg2hw.trigger.key_clear.q       ),
    .iv_clear_i              ( reg2hw.trigger.iv_clear.q        ),
    .data_in_clear_i         ( reg2hw.trigger.data_in_clear.q   ),
    .data_out_clear_i        ( reg2hw.trigger.data_out_clear.q  ),
    .prng_reseed_i           ( reg2hw.trigger.prng_reseed.q     ),

    .key_init_qe_i           ( key_init_qe                      ),
    .iv_qe_i                 ( iv_qe                            ),
    .data_in_qe_i            ( data_in_qe                       ),
    .data_out_re_i           ( data_out_re                      ),
    .data_in_we_o            ( data_in_we                       ),
    .data_out_we_o           ( data_out_we                      ),

    .data_in_prev_sel_o      ( data_in_prev_sel                 ),
    .data_in_prev_we_o       ( data_in_prev_we                  ),

    .state_in_sel_o          ( state_in_sel                     ),
    .add_state_in_sel_o      ( add_state_in_sel                 ),
    .add_state_out_sel_o     ( add_state_out_sel                ),

    .ctr_incr_o              ( ctr_incr                         ),
    .ctr_ready_i             ( ctr_ready                        ),
    .ctr_we_i                ( ctr_we                           ),

    .cipher_in_valid_o       ( cipher_in_valid                  ),
    .cipher_in_ready_i       ( cipher_in_ready                  ),
    .cipher_out_valid_i      ( cipher_out_valid                 ),
    .cipher_out_ready_o      ( cipher_out_ready                 ),
    .cipher_crypt_o          ( cipher_crypt                     ),
    .cipher_crypt_i          ( cipher_crypt_busy                ),
    .cipher_dec_key_gen_o    ( cipher_dec_key_gen               ),
    .cipher_dec_key_gen_i    ( cipher_dec_key_gen_busy          ),
    .cipher_key_clear_o      ( cipher_key_clear                 ),
    .cipher_key_clear_i      ( cipher_key_clear_busy            ),
    .cipher_data_out_clear_o ( cipher_data_out_clear            ),
    .cipher_data_out_clear_i ( cipher_data_out_clear_busy       ),

    .key_init_sel_o          ( key_init_sel                     ),
    .key_init_we_o           ( key_init_we                      ),
    .iv_sel_o                ( iv_sel                           ),
    .iv_we_o                 ( iv_we                            ),

    .prng_data_req_o         ( prng_data_req_o                  ),
    .prng_data_ack_i         ( prng_data_ack_i                  ),
    .prng_reseed_req_o       ( prng_reseed_req_o                ),
    .prng_reseed_ack_i       ( prng_reseed_ack_i                ),

    .start_o                 ( hw2reg.trigger.start.d           ),
    .start_we_o              ( hw2reg.trigger.start.de          ),
    .key_clear_o             ( hw2reg.trigger.key_clear.d       ),
    .key_clear_we_o          ( hw2reg.trigger.key_clear.de      ),
    .iv_clear_o              ( hw2reg.trigger.iv_clear.d        ),
    .iv_clear_we_o           ( hw2reg.trigger.iv_clear.de       ),
    .data_in_clear_o         ( hw2reg.trigger.data_in_clear.d   ),
    .data_in_clear_we_o      ( hw2reg.trigger.data_in_clear.de  ),
    .data_out_clear_o        ( hw2reg.trigger.data_out_clear.d  ),
    .data_out_clear_we_o     ( hw2reg.trigger.data_out_clear.de ),
    .prng_reseed_o           ( hw2reg.trigger.prng_reseed.d     ),
    .prng_reseed_we_o        ( hw2reg.trigger.prng_reseed.de    ),

    .output_valid_o          ( hw2reg.status.output_valid.d     ),
    .output_valid_we_o       ( hw2reg.status.output_valid.de    ),
    .input_ready_o           ( hw2reg.status.input_ready.d      ),
    .input_ready_we_o        ( hw2reg.status.input_ready.de     ),
    .idle_o                  ( hw2reg.status.idle.d             ),
    .idle_we_o               ( hw2reg.status.idle.de            ),
    .stall_o                 ( hw2reg.status.stall.d            ),
    .stall_we_o              ( hw2reg.status.stall.de           )
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
      aes_op_q           <= AES_ENC;
      aes_mode_q         <= AES_ECB;
      key_len_q          <= AES_128;
      manual_operation_q <= '0;
    end else if (ctrl_we) begin
      aes_op_q           <= aes_op_d;
      aes_mode_q         <= aes_mode_d;
      key_len_q          <= key_len_d;
      manual_operation_q <= reg2hw.ctrl.manual_operation.q;
    end
  end

  /////////////
  // Outputs //
  /////////////

  always_ff @(posedge clk_i) begin : data_out_reg
    if (data_out_we) begin
      data_out_q <= data_out_d;
    end
  end

  always_comb begin : key_reg_put
    for (int i=0; i<8; i++) begin
      hw2reg.key[i].d  = key_init_q[i];
    end
  end

  always_comb begin : iv_reg_put
    for (int i=0; i<4; i++) begin
      hw2reg.iv[i].d  = {iv_q[2*i+1], iv_q[2*i]};
    end
  end

  always_comb begin : data_out_put
    for (int i=0; i<4; i++) begin
      hw2reg.data_out[i].d = data_out_q[i];
    end
  end

  assign hw2reg.ctrl.mode.d    = {aes_mode_q};
  assign hw2reg.ctrl.key_len.d = {key_len_q};

  // These fields are actually hro. But software must be able observe the current value (rw).
  assign hw2reg.ctrl.operation.d        = {aes_op_q};
  assign hw2reg.ctrl.manual_operation.d = manual_operation_q;

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid
  `ASSERT_KNOWN(AesKeyInitSelKnown, key_init_sel)
  `ASSERT(AesIvSelValid, iv_sel inside {
      IV_INPUT,
      IV_DATA_OUT,
      IV_DATA_IN_PREV,
      IV_CTR,
      IV_CLEAR
      })
  `ASSERT_KNOWN(AesDataInPrevSelKnown, data_in_prev_sel)
  `ASSERT(AesModeValid, aes_mode_q inside {
      AES_ECB,
      AES_CBC,
      AES_CTR
      })
  `ASSERT_KNOWN(AesOpKnown, aes_op_q)
  `ASSERT_KNOWN(AesStateInSelKnown, state_in_sel)
  `ASSERT_KNOWN(AesAddStateInSelKnown, add_state_in_sel)
  `ASSERT(AesAddStateOutSelValid, add_state_out_sel inside {
      ADD_SO_ZERO,
      ADD_SO_IV,
      ADD_SO_DIP
      })

endmodule
