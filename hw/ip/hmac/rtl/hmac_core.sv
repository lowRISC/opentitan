// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// HMAC Core implementation

module hmac_core import prim_sha2_pkg::*; (
  input clk_i,
  input rst_ni,

  input [1023:0]      secret_key, // {word0, word1, ..., word7}
  input               wipe_secret,
  input [31:0]        wipe_v,
  input               hmac_en,
  input digest_mode_e digest_size,
  input key_length_e  key_length,

  input        reg_hash_start,
  input        reg_hash_continue,
  input        reg_hash_process,
  output logic hash_done,
  output logic sha_hash_start,
  output logic sha_hash_continue,
  output logic sha_hash_process,
  input        sha_hash_done,

  // fifo
  output logic        sha_rvalid,
  output sha_fifo32_t sha_rdata,
  input               sha_rready,

  input               fifo_rvalid,
  input  sha_fifo32_t fifo_rdata,
  output logic        fifo_rready,

  // fifo control (select and fifo write data)
  output logic       fifo_wsel,      // 0: from reg, 1: from digest
  output logic       fifo_wvalid,
  // 0: digest[0][upper], 1:digest[0][lower] .. 14: digest[7][upper], 15: digest[7][lower]
  output logic [3:0] fifo_wdata_sel,
  input              fifo_wready,

  input  [127:0] message_length,
  output [127:0] sha_message_length,

  output logic idle
);

  localparam int unsigned BlockSizeSHA256     = 512;
  localparam int unsigned BlockSizeSHA512     = 1024;

  localparam int unsigned BlockSizeBitsSHA256 = $clog2(BlockSizeSHA256);
  localparam int unsigned BlockSizeBitsSHA512 = $clog2(BlockSizeSHA512);

  localparam int unsigned HashWordBitsSHA256  = $clog2($bits(sha_word32_t));

  localparam bit [127:0] BlockSizeSHA256in128  = 128'(BlockSizeSHA256);
  localparam bit [127:0] BlockSizeSHA512in128  = 128'(BlockSizeSHA512);

  localparam bit [BlockSizeBitsSHA256:0] BlockSizeBSBSHA256 =
                                                            BlockSizeSHA256[BlockSizeBitsSHA256:0];
  localparam bit [BlockSizeBitsSHA512:0] BlockSizeBSBSHA512 =
                                                            BlockSizeSHA512[BlockSizeBitsSHA512:0];

  logic hash_start;    // generated from internal state machine
  logic hash_continue; // generated from internal state machine
  logic hash_process;  // generated from internal state machine to trigger hash
  logic hmac_hash_done;

  logic [BlockSizeSHA256-1:0] i_pad_256;
  logic [BlockSizeSHA512-1:0] i_pad_512;
  logic [BlockSizeSHA256-1:0] o_pad_256;
  logic [BlockSizeSHA512-1:0] o_pad_512;

  logic [127:0] txcount; // works for both digest lengths

  logic [BlockSizeBitsSHA512-HashWordBitsSHA256-1:0] pad_index_512;
  logic [BlockSizeBitsSHA256-HashWordBitsSHA256-1:0] pad_index_256;
  logic clr_txcount, load_txcount, inc_txcount;

  logic hmac_sha_rvalid;

  typedef enum logic [1:0] {
    SelIPad,
    SelOPad,
    SelFifo
  } sel_rdata_t;

  sel_rdata_t sel_rdata;

  typedef enum logic {
    SelIPadMsg,
    SelOPadMsg
  } sel_msglen_t;

  sel_msglen_t sel_msglen;

  typedef enum logic {
    Inner,  // Update when state goes to StIPad
    Outer   // Update when state enters StOPad
  } round_t ;

  logic update_round ;
  round_t round_q, round_d;

  typedef enum logic [2:0] {
    StIdle,
    StIPad,
    StMsg,              // Actual Msg, and Digest both
    StPushToMsgFifo,    // Digest --> Msg Fifo
    StWaitResp,         // Hash done( by checking processed_length? or hash_done)
    StOPad,
    StDone              // hmac_done
  } st_e ;

  st_e st_q, st_d;

  logic clr_fifo_wdata_sel;
  logic txcnt_eq_blksz;

  logic reg_hash_process_flag;

  assign sha_hash_start    = (hmac_en) ? hash_start                       : reg_hash_start ;
  assign sha_hash_continue = (hmac_en) ? hash_continue                    : reg_hash_continue ;
  assign sha_hash_process  = (hmac_en) ? reg_hash_process | hash_process  : reg_hash_process ;
  assign hash_done         = (hmac_en) ? hmac_hash_done                   : sha_hash_done  ;

  assign pad_index_512 = txcount[BlockSizeBitsSHA512-1:HashWordBitsSHA256];
  assign pad_index_256 = txcount[BlockSizeBitsSHA256-1:HashWordBitsSHA256];

  // defaults key length to block size if supplied key length is larger than block size
  always_comb begin : adjust_key_pad_length
    unique case (key_length)
      Key_128: begin
        i_pad_256 = {secret_key[1023:896],
                    {(BlockSizeSHA256-128){1'b0}}} ^ {(BlockSizeSHA256/8){8'h36}};
        i_pad_512 = {secret_key[1023:896],
                    {(BlockSizeSHA512-128){1'b0}}} ^ {(BlockSizeSHA512/8){8'h36}};
        o_pad_256 = {secret_key[1023:896],
                    {(BlockSizeSHA256-128){1'b0}}} ^ {(BlockSizeSHA256/8){8'h5c}};
        o_pad_512 = {secret_key[1023:896],
                    {(BlockSizeSHA512-128){1'b0}}} ^ {(BlockSizeSHA512/8){8'h5c}};
      end
      Key_256: begin
        i_pad_256 = {secret_key[1023:768],
                    {(BlockSizeSHA256-256){1'b0}}} ^ {(BlockSizeSHA256/8){8'h36}};
        i_pad_512 = {secret_key[1023:768],
                    {(BlockSizeSHA512-256){1'b0}}} ^ {(BlockSizeSHA512/8){8'h36}};
        o_pad_256 = {secret_key[1023:768],
                    {(BlockSizeSHA256-256){1'b0}}} ^ {(BlockSizeSHA256/8){8'h5c}};
        o_pad_512 = {secret_key[1023:768],
                    {(BlockSizeSHA512-256){1'b0}}} ^ {(BlockSizeSHA512/8){8'h5c}};
      end
      Key_384: begin
        i_pad_256 = {secret_key[1023:640],
                    {(BlockSizeSHA256-384){1'b0}}} ^ {(BlockSizeSHA256/8){8'h36}};
        i_pad_512 = {secret_key[1023:640],
                    {(BlockSizeSHA512-384){1'b0}}} ^ {(BlockSizeSHA512/8){8'h36}};
        o_pad_256 = {secret_key[1023:640],
                    {(BlockSizeSHA256-384){1'b0}}} ^ {(BlockSizeSHA256/8){8'h5c}};
        o_pad_512 = {secret_key[1023:640],
                    {(BlockSizeSHA512-384){1'b0}}} ^ {(BlockSizeSHA512/8){8'h5c}};
      end
      Key_512: begin
        i_pad_256 = secret_key[1023:512] ^ {(BlockSizeSHA256/8){8'h36}};
        i_pad_512 = {secret_key[1023:512],
                    {(BlockSizeSHA512-512){1'b0}}} ^ {(BlockSizeSHA512/8){8'h36}};
        o_pad_256 = secret_key[1023:512] ^ {(BlockSizeSHA256/8){8'h5c}};
        o_pad_512 = {secret_key[1023:512],
                    {(BlockSizeSHA512-512){1'b0}}} ^ {(BlockSizeSHA512/8){8'h5c}};
      end
      Key_1024: begin
        // cap key to 512-bit for SHA-256
        i_pad_256 = secret_key[1023:512] ^ {(BlockSizeSHA256/8){8'h36}};
        i_pad_512 = secret_key[1023:0]   ^ {(BlockSizeSHA512/8){8'h36}};
        // cap key to 512-bit for SHA-256
        o_pad_256 = secret_key[1023:512] ^ {(BlockSizeSHA256/8){8'h5c}};
        o_pad_512 = secret_key[1023:0]   ^ {(BlockSizeSHA512/8){8'h5c}};
      end
      default: begin // TODO: in case of unsupported lengths, default to 256-bit key or flag error?
        i_pad_256 = {secret_key[1023:768],
                    {(BlockSizeSHA256-256){1'b0}}} ^ {(BlockSizeSHA256/8){8'h36}};
        i_pad_512 = {secret_key[1023:768],
                    {(BlockSizeSHA512-256){1'b0}}} ^ {(BlockSizeSHA512/8){8'h36}};
        o_pad_256 = {secret_key[1023:768],
                    {(BlockSizeSHA256-256){1'b0}}} ^ {(BlockSizeSHA256/8){8'h5c}};
        o_pad_512 = {secret_key[1023:768],
                    {(BlockSizeSHA512-256){1'b0}}} ^ {(BlockSizeSHA512/8){8'h5c}};
      end
    endcase
  end

  assign fifo_rready  = (hmac_en) ? (st_q == StMsg) & sha_rready : sha_rready ;
  // sha_rvalid is controlled by State Machine below.
  assign sha_rvalid = (!hmac_en) ? fifo_rvalid : hmac_sha_rvalid ;
  assign sha_rdata =
    (!hmac_en)    ? fifo_rdata                                                             :
    (sel_rdata == SelIPad && digest_size == SHA2_256)
                  ? '{data: i_pad_256[(BlockSizeSHA256-1)-32*pad_index_256-:32], mask: '1} :
    (sel_rdata == SelIPad && ((digest_size == SHA2_384) || (digest_size == SHA2_512)))
                  ? '{data: i_pad_512[(BlockSizeSHA512-1)-32*pad_index_512-:32], mask: '1} :
    (sel_rdata == SelOPad && digest_size == SHA2_256)
                  ? '{data: o_pad_256[(BlockSizeSHA256-1)-32*pad_index_256-:32], mask: '1} :
    (sel_rdata == SelOPad && ((digest_size == SHA2_384) || (digest_size == SHA2_512)))
                  ? '{data: o_pad_512[(BlockSizeSHA512-1)-32*pad_index_512-:32], mask: '1} :
    (sel_rdata == SelFifo) ? fifo_rdata                                                    :
                  '{default: '0};

  logic [127:0] sha_msg_len;

  always_comb begin: assign_sha_message_length
    sha_msg_len = '0;
    if (!hmac_en) begin
      sha_msg_len = message_length;
    // HASH = (o_pad || HASH_INTERMEDIATE (i_pad || msg))
    // message length for HASH_INTERMEDIATE = block size (i_pad) + message length
    end else if (sel_msglen == SelIPadMsg) begin
      if (digest_size == SHA2_256) begin
        sha_msg_len = message_length + BlockSizeSHA256in128;
      end else if ((digest_size == SHA2_384) || (digest_size == SHA2_512)) begin
        sha_msg_len = message_length + BlockSizeSHA512in128;
      end
    end else if (sel_msglen == SelOPadMsg) begin
    // message length for HASH = block size (o_pad) + HASH_INTERMEDIATE digest length
      if (digest_size == SHA2_256) begin
        sha_msg_len = BlockSizeSHA256in128 + 128'd256;
      end else if (digest_size == SHA2_384) begin
        sha_msg_len = BlockSizeSHA512in128 + 128'd384;
      end else if (digest_size == SHA2_512) begin
        sha_msg_len = BlockSizeSHA512in128 + 128'd512;
      end
    end else
      sha_msg_len = '0;
  end

  assign sha_message_length = sha_msg_len;

  assign txcnt_eq_blksz = (digest_size == SHA2_256) ?
                                      (txcount[BlockSizeBitsSHA256:0] == BlockSizeBSBSHA256) :
                          ((digest_size == SHA2_384) || (digest_size == SHA2_512)) ?
                                      (txcount[BlockSizeBitsSHA512:0] == BlockSizeBSBSHA512) :
                                      '0;

  assign inc_txcount = sha_rready && sha_rvalid;

  // txcount
  //    Looks like txcount can be removed entirely here in hmac_core
  //    In the first round (InnerPaddedKey), it can just watch process and hash_done
  //    In the second round, it only needs count 256 bits for hash digest to trigger
  //    hash_process to SHA2
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      txcount <= '0;
    end else if (clr_txcount) begin
      txcount <= '0;
    end else if (load_txcount) begin
      // When loading, add block size to the message length because the SW-visible message length
      // does not include the block containing the key xor'ed with the inner pad.
      if (digest_size == SHA2_256) begin
        txcount <= message_length + BlockSizeSHA256in128;
      end else if ((digest_size == SHA2_384) || (digest_size == SHA2_512)) begin
        txcount <= message_length + BlockSizeSHA512in128;
      end else begin
        txcount <= message_length + '0;
      end
    end else if (inc_txcount) begin
      txcount[63:5] <= txcount[63:5] + 1'b1; // increment by 32 (data word size)
    end
  end

  // reg_hash_process trigger logic
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      reg_hash_process_flag <= 1'b0;
    end else if (reg_hash_process) begin
      reg_hash_process_flag <= 1'b1;
    end else if (hmac_hash_done || reg_hash_start || reg_hash_continue) begin
      reg_hash_process_flag <= 1'b0;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      round_q <= Inner;
    end else if (update_round) begin
      round_q <= round_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      fifo_wdata_sel <= 3'h 0;
    end else if (clr_fifo_wdata_sel) begin
      fifo_wdata_sel <= 3'h 0;
    end else if (fifo_wsel && fifo_wvalid) begin
      fifo_wdata_sel <= fifo_wdata_sel + 1'b1; // increment by 1
    end
  end

  assign sel_msglen = (round_q == Inner) ? SelIPadMsg : SelOPadMsg ;

  always_ff @(posedge clk_i or negedge rst_ni) begin : state_ff
    if (!rst_ni) st_q <= StIdle;
    else         st_q <= st_d;
  end

  always_comb begin : next_state
    hmac_hash_done  = 1'b0;
    hmac_sha_rvalid = 1'b0;

    clr_txcount  = 1'b0;
    load_txcount = 1'b0;

    update_round = 1'b0;
    round_d      = Inner;

    fifo_wsel    = 1'b0;   // from register
    fifo_wvalid  = 1'b0;

    clr_fifo_wdata_sel = 1'b1;

    sel_rdata = SelFifo;

    hash_start    = 1'b0;
    hash_continue = 1'b0;
    hash_process  = 1'b0;

    unique case (st_q)
      StIdle: begin
        if (hmac_en && reg_hash_start) begin
          st_d = StIPad;

          clr_txcount  = 1'b1;
          update_round = 1'b1;
          round_d      = Inner;
          hash_start   = 1'b1;
        end else begin
          st_d = StIdle;
        end
      end

      StIPad: begin
        sel_rdata = SelIPad;

        if (txcnt_eq_blksz) begin
          st_d = StMsg;

          hmac_sha_rvalid = 1'b0; // block new read request
        end else begin
          st_d = StIPad;

          hmac_sha_rvalid = 1'b1;
        end
      end

      StMsg: begin
        sel_rdata = SelFifo;
        fifo_wsel = (round_q == Outer);

        if (round_q == Inner && reg_hash_continue) begin
          load_txcount  = 1'b1;
          hash_continue = 1'b1;
        end

        if ( (((round_q == Inner) && reg_hash_process_flag) || (round_q == Outer))
            && (txcount >= sha_message_length)) begin
          st_d    = StWaitResp;
          hmac_sha_rvalid = 1'b0; // block
          hash_process = (round_q == Outer);
        end else begin
          st_d            = StMsg;
          hmac_sha_rvalid = fifo_rvalid;
        end
      end

      StWaitResp: begin
        hmac_sha_rvalid = 1'b0;

        if (sha_hash_done) begin
          if (round_q == Outer) begin
            st_d = StDone;
          end else begin // round_q == Inner
            st_d = StPushToMsgFifo;
          end
        end else begin
          st_d = StWaitResp;
        end
      end

      StPushToMsgFifo: begin
        hmac_sha_rvalid    = 1'b0;
        fifo_wsel          = 1'b1;
        fifo_wvalid        = 1'b1;
        clr_fifo_wdata_sel = 1'b0;

        if (fifo_wready && (((fifo_wdata_sel == 4'd7)  && (digest_size == SHA2_256)) ||
                            ((fifo_wdata_sel == 4'd15) && (digest_size == SHA2_512)) ||
                            ((fifo_wdata_sel == 4'd11) && (digest_size == SHA2_384)))) begin

          st_d = StOPad;

          clr_txcount  = 1'b1;
          update_round = 1'b1;
          round_d      = Outer;
          hash_start   = 1'b1;
        end else begin
          st_d = StPushToMsgFifo;

        end
      end

      StOPad: begin
        sel_rdata = SelOPad;
        fifo_wsel = 1'b1; // Remained HMAC select to indicate HMAC is in second stage

        if (txcnt_eq_blksz) begin
          st_d = StMsg;

          hmac_sha_rvalid = 1'b0; // block new read request
        end else begin
          st_d = StOPad;

          hmac_sha_rvalid = 1'b1;
        end
      end

      StDone: begin
        // raise interrupt (hash_done)
        st_d = StIdle;

        hmac_hash_done = 1'b1;
      end

      default: begin
        st_d = StIdle;
      end

    endcase
  end

  // Idle: Idle in HMAC_CORE only represents the idle status when hmac mode is
  // set. If hmac_en is 0, this logic sends the idle signal always.
  assign idle = (st_q == StIdle) && !(reg_hash_start || reg_hash_continue);
endmodule
