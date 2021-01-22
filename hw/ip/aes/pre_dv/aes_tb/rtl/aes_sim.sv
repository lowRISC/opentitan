// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES simulation wrapper

module aes_sim import aes_pkg::*;
#(
  parameter bit          AES192Enable         = 1,
  parameter bit          Masking              = 1,
  parameter sbox_impl_e  SBoxImpl             = SBoxImplCanrightMaskedNoreuse,
  parameter int unsigned SecStartTriggerDelay = 40,
  parameter bit          SecAllowForcingMasks = 0
) (
  input                     clk_i,
  input                     rst_ni,

  // Bus Interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o
);

  import aes_reg_pkg::*;

  // Instantiate top-level
  aes #(
    .AES192Enable         ( AES192Enable         ),
    .Masking              ( Masking              ),
    .SBoxImpl             ( SBoxImpl             ),
    .SecStartTriggerDelay ( SecStartTriggerDelay ),
    .SecAllowForcingMasks ( SecAllowForcingMasks )
  ) u_aes (
    .clk_i,
    .rst_ni,
    .idle_o     (          ),
    .tl_i,
    .tl_o,
    .alert_rx_i ( alert_rx ),
    .alert_tx_o ( alert_tx )
  );

  // Signals for controlling model checker
  logic        start /*verilator public_flat*/;
  logic        init  /*verilator public_flat*/;
  logic        done  /*verilator public_flat*/;
  logic        busy  /*verilator public_flat*/;
  logic        stall /*verilator public_flat*/;
  logic        step  /*verilator public_flat*/;

  // From aes_cipher_control.sv:
  typedef enum logic [5:0] {
    IDLE     = 6'b111100,
    INIT     = 6'b101001,
    ROUND    = 6'b010000,
    FINISH   = 6'b100010,
    CLEAR_S  = 6'b011011,
    CLEAR_KD = 6'b110111,
    ERROR    = 6'b001110
  } aes_cipher_ctrl_e;
  aes_cipher_ctrl_e aes_cipher_ctrl_ns, aes_cipher_ctrl_cs;
  //

  assign aes_cipher_ctrl_cs = u_aes.u_aes_core.u_aes_cipher_core.u_aes_cipher_control.aes_cipher_ctrl_cs;
  assign aes_cipher_ctrl_ns = u_aes.u_aes_core.u_aes_cipher_core.u_aes_cipher_control.aes_cipher_ctrl_ns;

  assign start = (aes_cipher_ctrl_cs == IDLE) && (aes_cipher_ctrl_ns == INIT);   // IDLE -> INIT
  assign init  = (aes_cipher_ctrl_cs == INIT);                                   // INIT
  assign done  = (aes_cipher_ctrl_cs == FINISH) && (aes_cipher_ctrl_ns == IDLE); // FINISH -> IDLE
  assign busy  = u_aes.u_aes_core.u_aes_control.cipher_crypt_i |
                 u_aes.u_aes_core.u_aes_control.cipher_crypt_o |
                 u_aes.u_aes_core.u_aes_control.cipher_dec_key_gen_i |
                 u_aes.u_aes_core.u_aes_control.cipher_dec_key_gen_o;
  assign stall = u_aes.u_aes_core.u_aes_control.stall_o;

  assign step  = ((aes_cipher_ctrl_cs == INIT) && (aes_cipher_ctrl_ns == ROUND)) || // INIT -> ROUND
                 ((aes_cipher_ctrl_cs == ROUND) && // ROUND + updating state or full key
                   (u_aes.u_aes_core.u_aes_cipher_core.u_aes_cipher_control.key_full_we_o ||
                    u_aes.u_aes_core.u_aes_cipher_core.u_aes_cipher_control.state_we_o)) ||
                 ((aes_cipher_ctrl_cs == FINISH) && // FINISH + performing handshake
                    u_aes.u_aes_core.u_aes_cipher_core.u_aes_cipher_control.out_valid_o &&
                    u_aes.u_aes_core.u_aes_cipher_core.u_aes_cipher_control.out_ready_i);

  // Make internal signals directly accessible
  // control
  logic        op            /*verilator public_flat*/;
  logic  [4:0] mode          /*verilator public_flat*/;
  logic        cipher_op     /*verilator public_flat*/;
  logic        key_expand_op /*verilator public_flat*/;
  logic  [2:0] key_len       /*verilator public_flat*/;
  logic  [3:0] round         /*verilator public_flat*/;

  assign op            = {u_aes.u_aes_core.aes_op_q};
  assign mode          = {u_aes.u_aes_core.aes_mode_q[4:0]};
  assign cipher_op     = {u_aes.u_aes_core.u_aes_cipher_core.op_i};
  assign key_expand_op = {u_aes.u_aes_core.u_aes_cipher_core.u_aes_key_expand.op_i};
  assign key_len       = {u_aes.u_aes_core.u_aes_cipher_core.key_len_i};
  assign round         = u_aes.u_aes_core.u_aes_cipher_core.u_aes_cipher_control.rnd_ctr_q;

  // iv
  logic [31:0] iv[4] /*verilator public_flat*/;

  // data
  logic [31:0] data_in[4]            /*verilator public_flat*/;
  logic  [7:0] state_d[16]           /*verilator public_flat*/;
  logic  [7:0] state_q[16]           /*verilator public_flat*/;
  logic  [7:0] sub_bytes_out[16]     /*verilator public_flat*/;
  logic  [7:0] shift_rows_out[16]    /*verilator public_flat*/;
  logic  [7:0] mix_columns_out[16]   /*verilator public_flat*/;
  logic  [7:0] add_round_key_out[16] /*verilator public_flat*/;
  logic [31:0] data_out_d[4]         /*verilator public_flat*/;

  // key
  logic [31:0] key_full_q[8] /*verilator public_flat*/;
  logic  [7:0] round_key[16] /*verilator public_flat*/;

  logic  [7:0] rcon_q /*verilator public_flat*/;

  // bytes
  for (genvar j=0; j<4; j++) begin : columns
    for (genvar i=0; i<4; i++) begin : rows
      if (!Masking) begin
        assign state_d[4*j+i]           = u_aes.u_aes_core.u_aes_cipher_core.state_d[0][i][j];
        assign state_q[4*j+i]           = u_aes.u_aes_core.u_aes_cipher_core.state_q[0][i][j];
        assign sub_bytes_out[4*j+i]     = u_aes.u_aes_core.u_aes_cipher_core.sub_bytes_out[i][j];
        assign shift_rows_out[4*j+i]    = u_aes.u_aes_core.u_aes_cipher_core.shift_rows_out[0][i][j];
        assign mix_columns_out[4*j+i]   = u_aes.u_aes_core.u_aes_cipher_core.mix_columns_out[0][i][j];
        assign add_round_key_out[4*j+i] = u_aes.u_aes_core.u_aes_cipher_core.add_round_key_out[0][i][j];
        assign round_key[4*j+i]         = u_aes.u_aes_core.u_aes_cipher_core.round_key[0][i][j];
      end else begin
        // Unmask internal signals for C side
        assign state_d[4*j+i]           = u_aes.u_aes_core.u_aes_cipher_core.state_d[0][i][j] ^ u_aes.u_aes_core.u_aes_cipher_core.state_d[1][i][j];
        assign state_q[4*j+i]           = u_aes.u_aes_core.u_aes_cipher_core.state_q[0][i][j] ^ u_aes.u_aes_core.u_aes_cipher_core.state_q[1][i][j];
        assign sub_bytes_out[4*j+i]     = u_aes.u_aes_core.u_aes_cipher_core.sub_bytes_out[i][j] ^ u_aes.u_aes_core.u_aes_cipher_core.sb_out_mask[i][j];
        assign shift_rows_out[4*j+i]    = u_aes.u_aes_core.u_aes_cipher_core.shift_rows_out[0][i][j] ^ u_aes.u_aes_core.u_aes_cipher_core.shift_rows_out[1][i][j];
        assign mix_columns_out[4*j+i]   = u_aes.u_aes_core.u_aes_cipher_core.mix_columns_out[0][i][j] ^ u_aes.u_aes_core.u_aes_cipher_core.mix_columns_out[1][i][j];
        assign add_round_key_out[4*j+i] = u_aes.u_aes_core.u_aes_cipher_core.add_round_key_out[0][i][j] ^ u_aes.u_aes_core.u_aes_cipher_core.add_round_key_out[1][i][j];
        assign round_key[4*j+i]         = u_aes.u_aes_core.u_aes_cipher_core.round_key[0][i][j] ^ u_aes.u_aes_core.u_aes_cipher_core.round_key[1][i][j];
      end
    end
  end

  // words - iv + data
  for (genvar i = 0; i<4; i++) begin : gen_access_to_words_data
    assign iv[i]         = {u_aes.u_aes_core.iv_q[2*i+1], u_aes.u_aes_core.iv_q[2*i]};
    assign data_in[i]    = u_aes.u_aes_core.data_in[i];
    assign data_out_d[i] = u_aes.u_aes_core.data_out_d[i];
  end

  // words - key
  for (genvar i = 0; i<8; i++) begin : gen_access_to_words_key
    if (!Masking) begin
      assign key_full_q[i] = u_aes.u_aes_core.u_aes_cipher_core.key_full_q[0][i];
    end else begin
      assign key_full_q[i] = u_aes.u_aes_core.u_aes_cipher_core.key_full_q[0][i] ^ u_aes.u_aes_core.u_aes_cipher_core.key_full_q[1][i];
    end
  end

  assign rcon_q = u_aes.u_aes_core.u_aes_cipher_core.u_aes_key_expand.rcon_q;

  // alerts
  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx;
  prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx, unused_alert_tx;

  assign alert_rx[0].ping_p = 1'b0;
  assign alert_rx[0].ping_n = 1'b1;
  assign alert_rx[0].ack_p  = 1'b0;
  assign alert_rx[0].ack_n  = 1'b1;
  assign alert_rx[1].ping_p = 1'b0;
  assign alert_rx[1].ping_n = 1'b1;
  assign alert_rx[1].ack_p  = 1'b0;
  assign alert_rx[1].ack_n  = 1'b1;
  assign unused_alert_tx = alert_tx;

endmodule
