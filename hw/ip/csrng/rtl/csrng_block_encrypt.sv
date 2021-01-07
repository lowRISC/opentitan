// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng block encrypt module
//

module csrng_block_encrypt #(
  parameter aes_pkg::sbox_impl_e SBoxImpl = aes_pkg::SBoxImplLut,
  parameter int Cmd = 3,
  parameter int StateId = 4,
  parameter int BlkLen = 128,
  parameter int KeyLen = 256
) (
  input logic                clk_i,
  input logic                rst_ni,

   // update interface
  input logic                block_encrypt_bypass_i,
  input logic                block_encrypt_enable_i,
  input logic                block_encrypt_lc_hw_debug_not_on_i,
  input logic                block_encrypt_req_i,
  output logic               block_encrypt_rdy_o,
  input logic [KeyLen-1:0]   block_encrypt_key_i,
  input logic [BlkLen-1:0]   block_encrypt_v_i,
  input logic [Cmd-1:0]      block_encrypt_cmd_i,
  input logic [StateId-1:0]  block_encrypt_id_i,
  output logic               block_encrypt_ack_o,
  input logic                block_encrypt_rdy_i,
  output logic [Cmd-1:0]     block_encrypt_cmd_o,
  output logic [StateId-1:0] block_encrypt_id_o,
  output logic [BlkLen-1:0]  block_encrypt_v_o,
  output logic [2:0]         block_encrypt_sfifo_blkenc_err_o
);

  localparam int BlkEncFifoDepth = 1;
  localparam int BlkEncFifoWidth = BlkLen+StateId+Cmd;
  localparam int NumShares = 1;

  // signals
  // blk_encrypt_in fifo
  logic [BlkEncFifoWidth-1:0] sfifo_blkenc_rdata;
  logic                       sfifo_blkenc_push;
  logic [BlkEncFifoWidth-1:0] sfifo_blkenc_wdata;
  logic                       sfifo_blkenc_pop;
  logic                       sfifo_blkenc_not_full;
  logic                       sfifo_blkenc_not_empty;
  // breakout
  logic [Cmd-1:0]             sfifo_blkenc_cmd;
  logic [StateId-1:0]         sfifo_blkenc_id;
  logic [BlkLen-1:0]          sfifo_blkenc_v;

  logic                 cipher_in_valid;
  logic                 cipher_in_ready;
  logic                 cipher_out_valid;
  logic                 cipher_out_ready;
  logic [BlkLen-1:0]    cipher_data_out;
  logic                 aes_cipher_core_enable;

  logic [3:0][3:0][7:0] state_init[NumShares];

  logic [7:0][31:0]     key_init[NumShares];
  logic [3:0][3:0][7:0] state_done[NumShares];
  logic [3:0][3:0][7:0] state_out;

  assign     state_init[0] = block_encrypt_v_i;

  assign     key_init[0] = block_encrypt_key_i;
  assign     state_out = state_done[0];
  assign     cipher_data_out =  state_out;


  //--------------------------------------------
  // aes cipher core lifecycle enable
  //--------------------------------------------

  assign aes_cipher_core_enable = (!block_encrypt_bypass_i) || block_encrypt_lc_hw_debug_not_on_i;

  //--------------------------------------------
  // aes cipher core
  //--------------------------------------------
  assign cipher_in_valid = (aes_cipher_core_enable && block_encrypt_req_i);

  // Cipher core
  aes_cipher_core #(
    .AES192Enable ( 1'b0 ),  // AES192Enable disabled
    .Masking      ( 1'b0 ),  // Masking disable
    .SBoxImpl     ( SBoxImpl )
  ) u_aes_cipher_core   (
    .clk_i              (clk_i),
    .rst_ni             (rst_ni),

    .cfg_valid_i        ( 1'b1                       ),
    .in_valid_i         ( cipher_in_valid            ),
    .in_ready_o         ( cipher_in_ready            ),
    .out_valid_o        ( cipher_out_valid           ),
    .out_ready_i        ( cipher_out_ready           ),
    .op_i               ( aes_pkg::CIPH_FWD          ),
    .key_len_i          ( aes_pkg::AES_256           ),
    .crypt_i            ( aes_cipher_core_enable     ),
    .crypt_o            (                            ),
    .dec_key_gen_i      ( 1'b0                       ), // Disable
    .dec_key_gen_o      (                            ),
    .key_clear_i        ( 1'b0                       ), // Disable
    .key_clear_o        (                            ),
    .data_out_clear_i   ( 1'b0                       ), // Disable
    .data_out_clear_o   (                            ),
    .alert_o            (                            ), // Currently unused.
    .prd_clearing_i     ( '0                         ),
    .force_zero_masks_i ( 1'b0                       ),
    .data_in_mask_o     (                            ),
    .entropy_req_o      (                            ),
    .entropy_ack_i      ( 1'b0                       ),
    .entropy_i          ( '0                         ),

    .state_init_i       ( state_init                 ),
    .key_init_i         ( key_init                   ),
    .state_o            ( state_done                 )
  );


  //--------------------------------------------
  // bypass fifo - intent is to bypass the aes block
  //--------------------------------------------

  prim_fifo_sync #(
    .Width(BlkEncFifoWidth),
    .Pass(0),
    .Depth(BlkEncFifoDepth)
  ) u_prim_fifo_sync_blkenc (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .clr_i    (!block_encrypt_enable_i),
    .wvalid_i (sfifo_blkenc_push),
    .wready_o (sfifo_blkenc_not_full),
    .wdata_i  (sfifo_blkenc_wdata),
    .rvalid_o (sfifo_blkenc_not_empty),
    .rready_i (sfifo_blkenc_pop),
    .rdata_o  (sfifo_blkenc_rdata),
    .depth_o  ()
  );

  assign sfifo_blkenc_push = block_encrypt_req_i && sfifo_blkenc_not_full;
  assign sfifo_blkenc_wdata = {block_encrypt_v_i,block_encrypt_id_i,block_encrypt_cmd_i};

  assign block_encrypt_rdy_o = !aes_cipher_core_enable ? sfifo_blkenc_not_full : cipher_in_ready;

  assign sfifo_blkenc_pop = block_encrypt_ack_o;
  assign {sfifo_blkenc_v,sfifo_blkenc_id,sfifo_blkenc_cmd} = sfifo_blkenc_rdata;

  assign block_encrypt_ack_o = block_encrypt_rdy_i &&
         (!aes_cipher_core_enable ? sfifo_blkenc_not_empty : cipher_out_valid);

  assign block_encrypt_cmd_o = sfifo_blkenc_cmd;
  assign block_encrypt_id_o = sfifo_blkenc_id;
  assign block_encrypt_v_o = !aes_cipher_core_enable ? sfifo_blkenc_v : cipher_data_out;
  assign cipher_out_ready = block_encrypt_rdy_i;

  assign block_encrypt_sfifo_blkenc_err_o =
         {(sfifo_blkenc_push && !sfifo_blkenc_not_full),
          (sfifo_blkenc_pop && !sfifo_blkenc_not_empty),
          (!sfifo_blkenc_not_full && !sfifo_blkenc_not_empty)};

endmodule
