// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SHA-256/384/512 configurable mode engine (64-bit word datapath)

module prim_sha2 import prim_sha2_pkg::*;
#(
  parameter bit MultimodeEn = 0, // assert to enable multi-mode digest feature

  localparam int unsigned RndWidth256 = $clog2(NumRound256),
  localparam int unsigned RndWidth512 = $clog2(NumRound512),
  localparam sha_word64_t ZeroWord      = '0
 ) (
  input clk_i,
  input rst_ni,

  input               wipe_secret_i,
  input sha_word64_t  wipe_v_i,
  // control signals and message words input to the message FIFO
  input               fifo_rvalid_i, // indicates that the message FIFO (prim_sync_fifo) has words
                                     // ready to write into the SHA-2 padding buffer
  input  sha_fifo64_t fifo_rdata_i,
  output logic        fifo_rready_o, // indicates the internal padding buffer is ready to receive
                                     // words from the message FIFO
  // control signals
  input               sha_en_i,   // if disabled, it clears internal content
  input               hash_start_i, // start hashing: initialize data counter to zero and clear
                                    // digest
  input               hash_continue_i, // continue hashing: set data counter to `message_length_i`
                                       // and use current digest
  input digest_mode_e digest_mode_i,
  input               hash_process_i,
  output logic        hash_done_o,

  input  [127:0]            message_length_i, // bits but byte based
  input  sha_word64_t [7:0] digest_i,
  input  logic [7:0]        digest_we_i,
  output sha_word64_t [7:0] digest_o, // tie off unused port slice when MultimodeEn = 0
  output logic hash_running_o, // `1` iff hash computation is active (as opposed to `idle_o`, which
                               // is also `0` and thus 'busy' when waiting for a FIFO input)
  output logic idle_o
);

  logic        msg_feed_complete;
  logic        shaf_rready;
  logic        shaf_rvalid;

  // control signals - shared for both modes
  logic update_w_from_fifo, calculate_next_w;
  logic init_hash, run_hash, one_chunk_done;
  logic update_digest, clear_digest;
  logic hash_done_next; // to meet the phase with digest value
  logic hash_go;

  // datapath signals - shared for both modes
  logic [RndWidth512-1:0] round_d, round_q;
  logic [3:0]             w_index_d, w_index_q;
  digest_mode_e           digest_mode_flag_d, digest_mode_flag_q;
  sha_word64_t            shaf_rdata;

  // tie off unused input ports and signals slices
  if (!MultimodeEn) begin : gen_tie_unused
    logic [7:0] unused_digest_upper;
    for (genvar i = 0; i < 8; i++) begin : gen_unused_digest_upper
      assign unused_digest_upper[i] = ^digest_i[i][63:32];
    end
    logic unused_signals;
    assign unused_signals = ^{wipe_v_i[63:32], shaf_rdata[63:32], unused_digest_upper};
  end

  // Most operations and control signals are identical no matter if we are starting or continuing
  // to hash.
  assign hash_go = hash_start_i | hash_continue_i;

  assign digest_mode_flag_d = hash_go     ? digest_mode_i   :    // latch in configured mode
                              hash_done_o ? None            :    // clear
                                            digest_mode_flag_q;  // keep

  if (MultimodeEn) begin : gen_multimode
    // datapath signal definitions for multi-mode
    sha_word64_t [7:0]  hash_d, hash_q; // a,b,c,d,e,f,g,h
    sha_word64_t [15:0] w_d, w_q;
    sha_word64_t [7:0]  digest_d, digest_q;

    // compute w
    always_comb begin : compute_w_multimode
      w_d = w_q;
      if (wipe_secret_i) begin
        w_d = w_q ^ {16{wipe_v_i[63:0]}};
      end else if (!sha_en_i || hash_go) begin
        w_d = '0;
      end else if (!run_hash && update_w_from_fifo) begin
        // this logic runs at the first stage of SHA: hash not running yet,
        // still filling in first 16 words
        w_d = {shaf_rdata, w_q[15:1]};
      end else if (calculate_next_w) begin // message scheduling/derivation for last 48/64 rounds
        if (digest_mode_flag_q == SHA2_256) begin
          // this computes the next w[16] and shifts out w[0] into compression below
          w_d = {{32'b0, calc_w_256(w_q[0][31:0], w_q[1][31:0], w_q[9][31:0],
                w_q[14][31:0])}, w_q[15:1]};
        end else if ((digest_mode_flag_q == SHA2_384) || (digest_mode_flag_q == SHA2_512)) begin
          w_d = {calc_w_512(w_q[0], w_q[1], w_q[9], w_q[14]), w_q[15:1]};
        end
      end else if (run_hash) begin
        // just shift-out the words as they get consumed. There's no incoming data.
        w_d = {ZeroWord, w_q[15:1]};
      end
    end : compute_w_multimode

    // update w
    always_ff @(posedge clk_i or negedge rst_ni) begin : update_w_multimode
      if (!rst_ni)            w_q <= '0;
      else if (MultimodeEn)   w_q <= w_d;
    end : update_w_multimode

    // compute hash
    always_comb begin : compression_multimode
      hash_d = hash_q;
      if (wipe_secret_i) begin
        for (int i = 0; i < 8; i++) begin
          hash_d[i] = hash_q[i] ^ wipe_v_i;
        end
      end else if (init_hash) begin
        hash_d = digest_q;
      end else if (run_hash) begin
        if (digest_mode_flag_q == SHA2_256) begin
          hash_d = compress_multi_256(w_q[0][31:0],
                   CubicRootPrime256[round_q[RndWidth256-1:0]], hash_q);
        end else if ((digest_mode_flag_q == SHA2_512) || (digest_mode_flag_q == SHA2_384)) begin
          hash_d = compress_512(w_q[0], CubicRootPrime512[round_q], hash_q);
        end
      end
    end : compression_multimode

    // update hash
    always_ff @(posedge clk_i or negedge rst_ni) begin : update_hash_multimode
      if (!rst_ni)  hash_q <= '0;
      else          hash_q <= hash_d;
    end : update_hash_multimode

    // compute digest
    always_comb begin : compute_digest_multimode
      digest_d = digest_q;
      if (wipe_secret_i) begin
        for (int i = 0 ; i < 8 ; i++) begin
          digest_d[i] = digest_q[i] ^ wipe_v_i;
        end
      end else if (hash_start_i) begin
        for (int i = 0 ; i < 8 ; i++) begin
          if (digest_mode_i == SHA2_256) begin
            digest_d[i] = {32'b0, InitHash_256[i]};
          end else if (digest_mode_i == SHA2_384) begin
            digest_d[i] = InitHash_384[i];
          end else if (digest_mode_i == SHA2_512) begin
            digest_d[i] = InitHash_512[i];
          end
        end
      end else if (clear_digest) begin
        digest_d = '0;
      end else if (!sha_en_i) begin
        for (int i = 0; i < 8; i++) begin
          digest_d[i] = digest_we_i[i] ? digest_i[i] : digest_q[i];
        end
      end else if (update_digest) begin
        for (int i = 0 ; i < 8 ; i++) begin
          digest_d[i] = digest_q[i] + hash_q[i];
        end
        if (hash_done_o == 1'b1 && digest_mode_flag_q == SHA2_384) begin
          // final digest truncation for SHA-2 384
          digest_d[6] = '0;
          digest_d[7] = '0;
        end else if (hash_done_o == 1'b1 && digest_mode_flag_q == SHA2_256) begin
          // make sure to clear out most significant 32-bits of each digest word (zero-padding)
          for (int i = 0 ; i < 8 ; i++) begin
            digest_d[i][63:32] = 32'b0;
          end
        end
      end
    end : compute_digest_multimode

    // update digest
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni)  digest_q <= '0;
      else          digest_q <= digest_d;
    end

    // assign digest to output
    assign digest_o = digest_q;

  end else begin : gen_256 // MultimodeEn = 0
    // datapath signal definitions for SHA-2 256 only
    sha_word32_t        shaf_rdata256;
    sha_word32_t [7:0]  hash256_d, hash256_q; // a,b,c,d,e,f,g,h
    sha_word32_t [15:0] w256_d, w256_q;
    sha_word32_t [7:0]  digest256_d, digest256_q;

    assign shaf_rdata256 = shaf_rdata[31:0];

    always_comb begin : compute_w_256
      // ~MultimodeEn
      w256_d = w256_q;
      if (wipe_secret_i) begin
        w256_d = w256_q ^ {16{wipe_v_i[31:0]}};
      end else if (!sha_en_i || hash_go) begin
        w256_d = '0;
      end else if (!run_hash && update_w_from_fifo) begin
        // this logic runs at the first stage of SHA: hash not running yet,
        // still filling in first 16 words
        w256_d = {shaf_rdata256, w256_q[15:1]};
      end else if (calculate_next_w) begin // message scheduling/derivation for last 48/64 rounds
        w256_d = {calc_w_256(w256_q[0][31:0], w256_q[1][31:0], w256_q[9][31:0],
                 w256_q[14][31:0]), w256_q[15:1]};
      end else if (run_hash) begin
        // just shift-out the words as they get consumed. There's no incoming data.
        w256_d = {ZeroWord[31:0], w256_q[15:1]};
      end
    end : compute_w_256

    // update w_256
    always_ff @(posedge clk_i or negedge rst_ni) begin : update_w_256
      if (!rst_ni)            w256_q <= '0;
      else if (!MultimodeEn)  w256_q <= w256_d;
    end : update_w_256

    // compute hash_256
    always_comb begin : compression_256
      hash256_d = hash256_q;
      if (wipe_secret_i) begin
        for (int i = 0; i < 8; i++) begin
          hash256_d[i] = hash256_q[i] ^ wipe_v_i[31:0];
        end
      end else if (init_hash) begin
        hash256_d = digest256_q;
      end else if (run_hash) begin
        hash256_d = compress_256(w256_q[0], CubicRootPrime256[round_q[RndWidth256-1:0]], hash256_q);
      end
    end : compression_256

    // update hash_256
    always_ff @(posedge clk_i or negedge rst_ni) begin : update_hash256
      if (!rst_ni) hash256_q <= '0;
      else         hash256_q <= hash256_d;
    end : update_hash256

    // compute digest_256
    always_comb begin : compute_digest_256
      digest256_d = digest256_q;
      if (wipe_secret_i) begin
        for (int i = 0 ; i < 8 ; i++) begin
          digest256_d[i] = digest256_q[i] ^ wipe_v_i[31:0];
        end
      end else if (hash_start_i) begin
        for (int i = 0 ; i < 8 ; i++) begin
            digest256_d[i] = InitHash_256[i];
        end
      end else if (clear_digest) begin
        digest256_d = '0;
      end else if (!sha_en_i) begin
        for (int i = 0; i < 8; i++) begin
          digest256_d[i] = digest_we_i[i] ? digest_i[i][31:0] : digest256_q[i];
        end
      end else if (update_digest) begin
        for (int i = 0 ; i < 8 ; i++) begin
          digest256_d[i] = digest256_q[i] + hash256_q[i];
        end
      end
    end : compute_digest_256

    // update digest_256
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni)  digest256_q <= '0;
      else          digest256_q <= digest256_d;
    end

    // assign digest to output
    for (genvar i = 0; i < 8; i++) begin  : gen_assign_digest_256
      assign digest_o[i][31:0]  = digest256_q[i];
      assign digest_o[i][63:32] = 32'b0;
    end
  end

  // compute round counter (shared)
  always_comb begin : round_counter
    round_d = round_q;
    if (!sha_en_i || hash_go) begin
      round_d = '0;
    end else if (run_hash) begin
      if (((round_q[RndWidth256-1:0] == RndWidth256'(unsigned'(NumRound256-1))) &&
         (digest_mode_flag_q == SHA2_256 || !MultimodeEn)) ||
         ((round_q == RndWidth512'(unsigned'(NumRound512-1))) &&
         ((digest_mode_flag_q == SHA2_384) || (digest_mode_flag_q == SHA2_512)))) begin
        round_d = '0;
      end else begin
        round_d = round_q + 1;
      end
    end
  end

  // update round counter (shared)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) round_q <= '0;
    else         round_q <= round_d;
  end

  // compute w_index (shared)
  assign w_index_d = (~sha_en_i || hash_go) ? '0            :  // clear
                     update_w_from_fifo     ? w_index_q + 1 :  // increment
                                              w_index_q;       // keep
  // update w_index (shared)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) w_index_q <= '0;
    else         w_index_q <= w_index_d;
  end

  // ready for a word from the padding buffer in sha2_pad
  assign shaf_rready = update_w_from_fifo;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) hash_done_o <= 1'b0;
    else         hash_done_o <= hash_done_next;
  end

  typedef enum logic [1:0] {
    FifoIdle,
    FifoLoadFromFifo,
    FifoWait
  } fifoctl_state_e;

  fifoctl_state_e fifo_st_q, fifo_st_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) fifo_st_q <= FifoIdle;
    else         fifo_st_q <= fifo_st_d;
  end

  always_comb begin
    fifo_st_d          = FifoIdle;
    update_w_from_fifo = 1'b0;
    hash_done_next     = 1'b0;

    unique case (fifo_st_q)
      FifoIdle: begin
        if (hash_go) fifo_st_d = FifoLoadFromFifo;
        else         fifo_st_d = FifoIdle;
      end

      FifoLoadFromFifo: begin
        if (!shaf_rvalid) begin
          // Wait until it is filled
          fifo_st_d          = FifoLoadFromFifo;
          update_w_from_fifo = 1'b0;
        end else if (w_index_q == 4'd 15) begin
          fifo_st_d = FifoWait;
          // To increment w_index and it rolls over to 0
          update_w_from_fifo = 1'b1;
        end else begin
          fifo_st_d          = FifoLoadFromFifo;
          update_w_from_fifo = 1'b1;
        end
      end

      FifoWait: begin
        if (msg_feed_complete && one_chunk_done) begin
          fifo_st_d      = FifoIdle;
          // hashing the full message is done
          hash_done_next = 1'b1;
        end else if (one_chunk_done) begin
          fifo_st_d      = FifoLoadFromFifo;
        end else begin
          fifo_st_d      = FifoWait;
        end
      end

      default: begin
        fifo_st_d = FifoIdle;
      end
    endcase

    if (!sha_en_i)  begin
      fifo_st_d          = FifoIdle;
      update_w_from_fifo = 1'b0;
    end else if (hash_go) begin
      fifo_st_d          = FifoLoadFromFifo;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) digest_mode_flag_q <= None;
    else         digest_mode_flag_q <= digest_mode_flag_d;
  end

  // SHA control (shared)
  typedef enum logic [1:0] {
    ShaIdle,
    ShaCompress,
    ShaUpdateDigest
  } sha_st_t;

  sha_st_t sha_st_q, sha_st_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) sha_st_q <= ShaIdle;
    else         sha_st_q <= sha_st_d;
  end

  logic sha_en_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) sha_en_q <= 1'b0;
    else         sha_en_q <= sha_en_i;
  end

  assign clear_digest = hash_start_i | (~sha_en_i & sha_en_q);

  always_comb begin
    update_digest    = 1'b0;
    calculate_next_w = 1'b0;
    init_hash        = 1'b0;
    run_hash         = 1'b0;
    sha_st_d         = sha_st_q;

    unique case (sha_st_q)
      ShaIdle: begin
        if (fifo_st_q == FifoWait) begin
          init_hash = 1'b1;
          sha_st_d  = ShaCompress;
        end else begin
          sha_st_d  = ShaIdle;
        end
      end

      ShaCompress: begin
        run_hash = 1'b1;
        if (((digest_mode_flag_q == SHA2_256 || ~MultimodeEn) && round_q < 48) ||
           (((digest_mode_flag_q == SHA2_384) ||
           (digest_mode_flag_q == SHA2_512)) && round_q < 64)) begin
          calculate_next_w = 1'b1;
        end else if (one_chunk_done) begin
          sha_st_d = ShaUpdateDigest;
        end else begin
          sha_st_d = ShaCompress;
        end
      end

      ShaUpdateDigest: begin
        update_digest = 1'b1;
        if (fifo_st_q == FifoWait) begin
          init_hash = 1'b1;
          sha_st_d  = ShaCompress;
        end else begin
          sha_st_d  = ShaIdle;
        end
      end

      default: begin
        sha_st_d = ShaIdle;
      end
    endcase

    if (!sha_en_i || hash_go) sha_st_d  = ShaIdle;
  end

  assign one_chunk_done = ((digest_mode_flag_q == SHA2_256 || ~MultimodeEn)
                          && (round_q == 7'd63)) ? 1'b1 :
                          (((digest_mode_flag_q == SHA2_384) || (digest_mode_flag_q == SHA2_512))
                          && (round_q == 7'd79)) ? 1'b1 : 1'b0;

  prim_sha2_pad #(
      .MultimodeEn(MultimodeEn)
    ) u_pad (
    .clk_i,
    .rst_ni,
    .fifo_rvalid_i,
    .fifo_rdata_i,
    .fifo_rready_o,
    .shaf_rvalid_o (shaf_rvalid), // is set when the 512-bit chunk is ready in the padding buffer
    .shaf_rdata_o  (shaf_rdata),
    .shaf_rready_i (shaf_rready), // indicates that w is ready for more words from padding buffer
    .sha_en_i,
    .hash_start_i,
    .hash_continue_i,
    .digest_mode_i,
    .hash_process_i,
    .hash_done_o,
    .message_length_i,
    .msg_feed_complete_o (msg_feed_complete)
  );

  assign hash_running_o = init_hash | run_hash | update_digest;

  // Idle
  assign idle_o = (fifo_st_q == FifoIdle) && (sha_st_q == ShaIdle) && !hash_go;
endmodule : prim_sha2
