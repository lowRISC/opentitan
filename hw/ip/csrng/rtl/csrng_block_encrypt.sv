// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng block encrypt module
//

module csrng_block_encrypt import aes_pkg::*; #(
  parameter int unsigned Cmd = 3,
  parameter int unsigned StateId = 4,
  parameter int unsigned BlkLen = 128,
  parameter int unsigned KeyLen = 256
) (
  input                  clk_i,
  input                  rst_ni,

   // update interface
  input logic                block_encrypt_bypass_i,
  input logic                block_encrypt_enable_i,
//  input logic [2:0]         block_encrypt_keylen_i, // TODO: make programmable?
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
  output logic               block_encrypt_fifo_err_o
);

  localparam BlkEncFifoDepth = 3;
  localparam BlkEncFifoWidth = BlkLen+StateId+Cmd;
  localparam AES192Enable = 1;
  localparam SBoxImpl     = "lut";

  // signals
  // blk_encrypt_in fifo
  logic [BlkEncFifoWidth-1:0] sfifo_blkenc_rdata;
  logic                       sfifo_blkenc_push;
  logic [BlkEncFifoWidth-1:0] sfifo_blkenc_wdata;
  logic                       sfifo_blkenc_pop;
  logic                       sfifo_blkenc_err;
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
  logic                 cipher_crypt;
  logic                 cipher_dec_key_gen;
  logic                 cipher_key_clear;
  logic                 cipher_data_out_clear;
  logic [63:0]          prng_data;
  logic [BlkLen-1:0]    cipher_data_out;


  assign block_encrypt_fifo_err_o = sfifo_blkenc_err;

  //--------------------------------------------
  // aes cipher core
  //--------------------------------------------

  assign cipher_in_valid = (!block_encrypt_bypass_i && block_encrypt_req_i);
  assign cipher_crypt = !block_encrypt_bypass_i;
  assign cipher_dec_key_gen = 1'b0; // Disable
  assign cipher_key_clear = 1'b0; // Disable
  assign cipher_data_out_clear = 1'b0; // Disable
  assign prng_data = '0;

  // Cipher core
  aes_cipher_core #(
    .AES192Enable ( AES192Enable ),
    .SBoxImpl     ( SBoxImpl     )
  ) u_aes_cipher_core (
    .clk_i            (clk_i),
    .rst_ni           (rst_ni),

    .in_valid_i       ( cipher_in_valid            ),
    .in_ready_o       ( cipher_in_ready            ),
    .out_valid_o      ( cipher_out_valid           ),
    .out_ready_i      ( cipher_out_ready           ),
    .op_i             ( CIPH_FWD                   ),
    .key_len_i        ( AES_256                    ),
    .crypt_i          ( cipher_crypt               ),
    .crypt_o          (                            ),
    .dec_key_gen_i    ( cipher_dec_key_gen         ),
    .dec_key_gen_o    (                            ),
    .key_clear_i      ( cipher_key_clear           ),
    .key_clear_o      (                            ),
    .data_out_clear_i ( cipher_data_out_clear      ),
    .data_out_clear_o (                            ),

    .prng_data_i      ( prng_data                  ),

    .state_init_i     ( block_encrypt_v_i          ),
    .key_init_i       ( block_encrypt_key_i        ),
    .state_o          ( cipher_data_out            )
  );

  prim_fifo_sync # (.Width(BlkEncFifoWidth),.Pass(0),.Depth(BlkEncFifoDepth))
    u_prim_fifo_sync_blkenc
      (
       .clk_i    (clk_i),
       .rst_ni   (rst_ni),
       .clr_i    (!block_encrypt_enable_i),
       .wvalid   (sfifo_blkenc_push),
       .wready   (sfifo_blkenc_not_full),
       .wdata    (sfifo_blkenc_wdata),
       .rvalid   (sfifo_blkenc_not_empty),
       .rready   (sfifo_blkenc_pop),
       .rdata    (sfifo_blkenc_rdata),
       .depth    ()
       );

  assign sfifo_blkenc_push = block_encrypt_req_i && sfifo_blkenc_not_full;
  assign sfifo_blkenc_wdata = {block_encrypt_v_i,block_encrypt_id_i,block_encrypt_cmd_i};

  assign block_encrypt_rdy_o = block_encrypt_bypass_i ? sfifo_blkenc_not_full : cipher_in_ready;

  assign sfifo_blkenc_pop = block_encrypt_ack_o;
  assign {sfifo_blkenc_v,sfifo_blkenc_id,sfifo_blkenc_cmd} = sfifo_blkenc_rdata;

  assign block_encrypt_ack_o = block_encrypt_bypass_i ?
         (sfifo_blkenc_not_empty && block_encrypt_rdy_i) : cipher_out_valid;

  assign block_encrypt_cmd_o = sfifo_blkenc_cmd;
  assign block_encrypt_id_o = sfifo_blkenc_id;
  assign block_encrypt_v_o = block_encrypt_bypass_i ? sfifo_blkenc_v : cipher_data_out;
  assign cipher_out_ready = block_encrypt_rdy_i; // TODO: revisit

  assign sfifo_blkenc_err =
         (sfifo_blkenc_push && !sfifo_blkenc_not_full) ||
         (sfifo_blkenc_pop && !sfifo_blkenc_not_empty);

endmodule
