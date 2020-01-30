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
  input logic                      clk_i,
  input logic                      rst_ni,

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
  aes_op_e              aes_op_d, aes_op_q;
  ciph_op_e             cipher_op;
  key_len_e             key_len;
  key_len_e             key_len_d, key_len_q;
  logic                 manual_operation_q;

  logic [3:0][3:0][7:0] state_init;
  logic [3:0][3:0][7:0] state_done;

  logic     [7:0][31:0] key_init_d;
  logic     [7:0][31:0] key_init_q;
  logic     [7:0]       key_init_we;
  key_init_sel_e        key_init_sel;

  logic     [3:0][31:0] data_out_d;
  logic     [3:0][31:0] data_out_q;
  logic                 data_out_we;
  logic           [3:0] data_out_re;

  logic                 cipher_in_valid;
  logic                 cipher_in_ready;
  logic                 cipher_out_valid;
  logic                 cipher_out_ready;
  logic                 cipher_start;
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

  assign aes_op_d = aes_op_e'(reg2hw.ctrl.operation.q);

  assign key_len = key_len_e'(reg2hw.ctrl.key_len.q);
  always_comb begin : get_key_len
    unique case (key_len)
      AES_128: key_len_d = AES_128;
      AES_256: key_len_d = AES_256;
      AES_192: key_len_d = AES192Enable ? AES_192 : AES_128;
      default: key_len_d = AES_128; // unsupported values are mapped to AES_128
    endcase
  end

  assign ctrl_qe = reg2hw.ctrl.operation.qe & reg2hw.ctrl.key_len.qe &
      reg2hw.ctrl.manual_operation.qe;

  //////////////////
  // Data and Key //
  //////////////////

  // Convert input data to state (every input data word contains one state column)
  assign state_init = aes_transpose(data_in);

  // Initial Key registers
  always_comb begin : key_init_mux
    unique case (key_init_sel)
      KEY_INIT_INPUT: key_init_d = key_init;
      KEY_INIT_CLEAR: key_init_d = '0;
      default:        key_init_d = '0;
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

  /////////////////
  // Cipher Core //
  /////////////////

  // Cipher core operation
  assign cipher_op = (aes_op_q == AES_ENC) ? CIPH_FWD : CIPH_INV;

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
    .start_i          ( cipher_start               ),
    .dec_key_gen_i    ( cipher_dec_key_gen         ),
    .dec_key_gen_o    ( cipher_dec_key_gen_busy    ),
    .key_clear_i      ( cipher_key_clear           ),
    .key_clear_o      ( cipher_key_clear_busy      ),
    .data_out_clear_i ( cipher_data_out_clear      ),
    .data_out_clear_o ( cipher_data_out_clear_busy ),

    .state_init_i     ( state_init                 ),
    .key_init_i       ( key_init_q                 ),
    .state_o          ( state_done                 )
  );

  /////////////
  // Control //
  /////////////

  // Control
  aes_control aes_control (
    .clk_i                   ( clk_i                            ),
    .rst_ni                  ( rst_ni                           ),

    .cipher_op_i             ( cipher_op                        ),
    .manual_operation_i      ( manual_operation_q               ),
    .start_i                 ( reg2hw.trigger.start.q           ),
    .key_clear_i             ( reg2hw.trigger.key_clear.q       ),
    .data_in_clear_i         ( reg2hw.trigger.data_in_clear.q   ),
    .data_out_clear_i        ( reg2hw.trigger.data_out_clear.q  ),

    .data_in_qe_i            ( data_in_qe                       ),
    .key_init_qe_i           ( key_init_qe                      ),
    .data_out_re_i           ( data_out_re                      ),
    .data_in_we_o            ( data_in_we                       ),
    .data_out_we_o           ( data_out_we                      ),

    .cipher_in_valid_o       ( cipher_in_valid                  ),
    .cipher_in_ready_i       ( cipher_in_ready                  ),
    .cipher_out_valid_i      ( cipher_out_valid                 ),
    .cipher_out_ready_o      ( cipher_out_ready                 ),
    .cipher_start_o          ( cipher_start                     ),
    .cipher_dec_key_gen_o    ( cipher_dec_key_gen               ),
    .cipher_dec_key_gen_i    ( cipher_dec_key_gen_busy          ),
    .cipher_key_clear_o      ( cipher_key_clear                 ),
    .cipher_key_clear_i      ( cipher_key_clear_busy            ),
    .cipher_data_out_clear_o ( cipher_data_out_clear            ),
    .cipher_data_out_clear_i ( cipher_data_out_clear_busy       ),

    .key_init_sel_o          ( key_init_sel                     ),
    .key_init_we_o           ( key_init_we                      ),

    .start_o                 ( hw2reg.trigger.start.d           ),
    .start_we_o              ( hw2reg.trigger.start.de          ),
    .key_clear_o             ( hw2reg.trigger.key_clear.d       ),
    .key_clear_we_o          ( hw2reg.trigger.key_clear.de      ),
    .data_in_clear_o         ( hw2reg.trigger.data_in_clear.d   ),
    .data_in_clear_we_o      ( hw2reg.trigger.data_in_clear.de  ),
    .data_out_clear_o        ( hw2reg.trigger.data_out_clear.d  ),
    .data_out_clear_we_o     ( hw2reg.trigger.data_out_clear.de ),

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
      key_len_q          <= AES_128;
      manual_operation_q <= '0;
    end else if (ctrl_we) begin
      aes_op_q           <= aes_op_d;
      key_len_q          <= key_len_d;
      manual_operation_q <= reg2hw.ctrl.manual_operation.q;
    end
  end

  /////////////
  // Outputs //
  /////////////

  // Convert output state to output data (every state column corresponds to one output word)
  assign data_out_d = aes_transpose(state_done);

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

  // These fields are actually hro. But software must be able observe the current value (rw).
  assign hw2reg.ctrl.operation.d        = {aes_op_q};
  assign hw2reg.ctrl.manual_operation.d = manual_operation_q;

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid
  `ASSERT_KNOWN(AesKeyInitSelKnown, key_init_sel)
  `ASSERT_KNOWN(AesOpKnown, aes_op_q)

endmodule
