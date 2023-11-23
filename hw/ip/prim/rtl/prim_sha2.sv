// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SHA-256/384/512 configurable mode engine (64-bit word datapath)
//

module prim_sha2 import prim_sha2_pkg::*; (
  input clk_i,
  input rst_ni,

  input              wipe_secret,
  input sha_word64_t wipe_v,

  // Control signals and message words input to the message FIFO
  input               fifo_rvalid, // indicates that the message FIFO (prim_sync_fifo) has words
                                   // ready to write into the SHA-2 padding buffer
  input  sha_fifo64_t fifo_rdata,
  output logic        fifo_rready, // indicates that the internal padding buffer is ready to receive
                                  // words from the message FIFO

  // Control signals
  input               sha_en,   // if disabled, it clears internal content
  input               hash_start,
  input digest_mode_e digest_mode,
  input               hash_process,
  output logic        hash_done,

  input  [127:0]            message_length, // bits but byte based
  output sha_word64_t [7:0] digest,

  output logic idle
);

  localparam int unsigned RoundWidth256 = $clog2(NumRound256);
  localparam int unsigned RoundWidth512 = $clog2(NumRound512);

  localparam sha_word64_t ZeroWord = '0;

  logic        msg_feed_complete;
  logic        shaf_rready;
  sha_word64_t shaf_rdata;
  logic        shaf_rvalid;

  logic [RoundWidth512-1:0] round;

  logic         [3:0] w_index;
  sha_word64_t [15:0] w;

  digest_mode_e digest_mode_flag;


  // w, hash, digest update logic control signals
  logic update_w_from_fifo, calculate_next_w;
  logic init_hash, run_hash, complete_one_chunk;
  logic update_digest, clear_digest;

  logic hash_done_next; // to meet the phase with digest value.

  sha_word64_t [7:0] hash;    // a,b,c,d,e,f,g,h

  // Fill up w
  always_ff @(posedge clk_i or negedge rst_ni) begin : fill_w
    if (!rst_ni) begin
      w <= '0;
    end else if (wipe_secret) begin
      w <= w ^ {16{wipe_v}};
    end else if (!sha_en || hash_start) begin
      w <= '0;
    end else if (!run_hash && update_w_from_fifo) begin
      // this logic runs at the first stage of SHA: hash not running yet,
      // still filling in first 16 words
      w <= {shaf_rdata, w[15:1]};
    end else if (calculate_next_w) begin // message scheduling/derivation for last 48/64 rounds
      if (digest_mode_flag == SHA2_256) begin
        // this computes the next w[16] and shifts out w[0] into compression (see compress() below)
        w <= {{32'b0, calc_w_256(w[0][31:0], w[1][31:0], w[9][31:0], w[14][31:0])}, w[15:1]};
      end else if ((digest_mode_flag == SHA2_384) || (digest_mode_flag == SHA2_512)) begin
        w <= {calc_w_512(w[0], w[1], w[9], w[14]), w[15:1]};
      end
    end else if (run_hash) begin
      // Just shift-out the words as they get consumed. There's no incoming data.
      w <= {ZeroWord, w[15:1]};
    end
  end : fill_w

  // Update engine
  always_ff @(posedge clk_i or negedge rst_ni) begin : compress_round
    if (!rst_ni) begin
      hash <= '{default:'0};
    end else if (wipe_secret) begin
      for (int i = 0 ; i < 8 ; i++) begin
        hash[i] <= hash[i] ^ wipe_v;
      end
    end else if (init_hash) begin
      hash <= digest;
    end else if (run_hash) begin
      if (digest_mode_flag == SHA2_256) begin
        hash <= compress_256( w[0][31:0], CubicRootPrime256[round[RoundWidth256-1:0]], hash);
      end else if ((digest_mode_flag == SHA2_512) || (digest_mode_flag == SHA2_384)) begin
        hash <= compress_512( w[0], CubicRootPrime512[round], hash);
      end
    end
  end : compress_round

  // Digest
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      digest <= '{default: '0};
    end else if (wipe_secret) begin
      for (int i = 0 ; i < 8 ; i++) begin
        digest[i] <= digest[i] ^ wipe_v;
      end
    end else if (hash_start) begin
      for (int i = 0 ; i < 8 ; i++) begin
        if (digest_mode == SHA2_256) begin
          digest[i] <= {32'b0, InitHash_256[i]};
        end else if (digest_mode == SHA2_384) begin
          digest[i] <= InitHash_384[i];
        end else if (digest_mode == SHA2_512) begin
          digest[i] <= InitHash_512[i];
        end
      end
    end else if (!sha_en || clear_digest) begin
      digest <= '0;
    end else if (update_digest) begin
      for (int i = 0 ; i < 8 ; i++) begin
        digest[i] <= digest[i] + hash[i];
      end
      if (hash_done == 1'b1 && digest_mode_flag == SHA2_384) begin
        // final digest truncation for SHA-2 384
        digest[6] <= '0;
        digest[7] <= '0;
      end else if (hash_done == 1'b1 && digest_mode_flag == SHA2_256) begin
        // make sure to clear out most significant 32-bits of each digest word (zero-padding)
        digest[0][63:32] <= '0;
        digest[1][63:32] <= '0;
        digest[2][63:32] <= '0;
        digest[3][63:32] <= '0;
        digest[4][63:32] <= '0;
        digest[5][63:32] <= '0;
        digest[6][63:32] <= '0;
        digest[7][63:32] <= '0;
      end
    end
  end

  // round counter
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      round <= '0;
    end else if (!sha_en || hash_start) begin
      round <= '0;
    end else if (run_hash) begin
      if (((round[RoundWidth256-1:0] == RoundWidth256'(unsigned'(NumRound256-1))) &&
         digest_mode_flag == SHA2_256) || ((round == RoundWidth512'(unsigned'(NumRound512-1))) &&
         ((digest_mode_flag == SHA2_384) || (digest_mode_flag == SHA2_512)))) begin
        round <= '0;
      end else begin
        round <= round + 1;
      end
    end
  end

  // w_index
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if      (!rst_ni)               w_index <= '0;
    else if (!sha_en || hash_start) w_index <= '0;
    else if (update_w_from_fifo)    w_index <= w_index + 1;
  end

  // ready for a word from the padding buffer in sha2_pad
  assign shaf_rready = update_w_from_fifo;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) hash_done <= 1'b0;
    else         hash_done <= hash_done_next;
  end

  typedef enum logic [1:0] {
    FifoIdle,
    FifoLoadFromFifo,
    FifoWait
  } fifoctl_state_e;

  fifoctl_state_e fifo_st_q, fifo_st_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if      (!rst_ni)    fifo_st_q <= FifoIdle;
    else if (!sha_en)    fifo_st_q <= FifoIdle;
    else if (hash_start) fifo_st_q <= FifoLoadFromFifo;
    else                 fifo_st_q <= fifo_st_d;
  end

  always_comb begin
    fifo_st_d = FifoIdle;
    update_w_from_fifo = 1'b0;
    hash_done_next = 1'b0;

    unique case (fifo_st_q)
      FifoIdle: begin
        if (hash_start) fifo_st_d = FifoLoadFromFifo;
        else fifo_st_d = FifoIdle;
      end

      FifoLoadFromFifo: begin
        if (!sha_en) begin
          fifo_st_d          = FifoIdle;
          update_w_from_fifo = 1'b0;
        end else if (!shaf_rvalid) begin
          // Wait until it is filled
          fifo_st_d          = FifoLoadFromFifo;
          update_w_from_fifo = 1'b0;
        end else if (w_index == 4'd 15) begin
          fifo_st_d = FifoWait;
          // To increment w_index and it rolls over to 0
          update_w_from_fifo = 1'b1;
        end else begin
          fifo_st_d          = FifoLoadFromFifo;
          update_w_from_fifo = 1'b1;
        end
      end

      FifoWait: begin
        // Wait until next fetch begins (begin at round == 48)
        if (msg_feed_complete && complete_one_chunk) begin
          fifo_st_d = FifoIdle;
          // hashing the full message is done
          hash_done_next = 1'b1;
        end else if (complete_one_chunk) begin
          fifo_st_d = FifoLoadFromFifo;
        end else begin
          fifo_st_d = FifoWait;
        end
      end

      default: begin
        fifo_st_d = FifoIdle;
      end
    endcase
  end

  // Latch SHA-2 configured mode at hash_start
   always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)         digest_mode_flag <= None;
    else if (hash_start) digest_mode_flag <= digest_mode;
    else if (hash_done)  digest_mode_flag <= None;
  end

  // SHA control
  typedef enum logic [1:0] {
    ShaIdle,
    ShaCompress,
    ShaUpdateDigest
  } sha_st_t;

  sha_st_t sha_st_q, sha_st_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)                    sha_st_q <= ShaIdle;
    else if (!sha_en || hash_start) sha_st_q <= ShaIdle;
    else                            sha_st_q <= sha_st_d;
  end

  assign clear_digest = hash_start;

  always_comb begin
    update_digest    = 1'b0;
    calculate_next_w = 1'b0;
    init_hash        = 1'b0;
    run_hash         = 1'b0;

    unique case (sha_st_q)
      ShaIdle: begin
        if (fifo_st_q == FifoWait) begin
          init_hash = 1'b1;
          sha_st_d = ShaCompress;
        end else begin
          sha_st_d = ShaIdle;
        end
      end

      ShaCompress: begin
        run_hash = 1'b1;
        if ((digest_mode_flag == SHA2_256 && round < 48) ||
           (((digest_mode_flag == SHA2_384) || (digest_mode_flag == SHA2_512)) && round < 64)) begin
          calculate_next_w = 1'b1;
        end
        if (complete_one_chunk) begin
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
          sha_st_d = ShaIdle;
        end
      end

      default: begin
        sha_st_d = ShaIdle;
      end
    endcase
  end

  assign complete_one_chunk = ((digest_mode_flag == SHA2_256) && (round == 7'd63)) ? 1'b1 :
                              (((digest_mode_flag == SHA2_384) || (digest_mode_flag == SHA2_512))
                              && (round == 7'd79)) ? 1'b1 : 1'b0;

  sha2_multimode_pad u_pad (
    .clk_i,
    .rst_ni,

    .fifo_rvalid,
    .fifo_rdata,
    .fifo_rready,

    .shaf_rvalid, // set when the 512-bit chunk is ready in the padding buffer and can load into w
    .shaf_rdata,
    .shaf_rready, // indicates that w is ready for more words from padding buffer

    .sha_en,
    .hash_start,
    .digest_mode,
    .hash_process,
    .hash_done,

    .message_length,
    .msg_feed_complete
  );

  // Idle
  assign idle = (fifo_st_q == FifoIdle) && (sha_st_q == ShaIdle) && !hash_start;
endmodule : sha2_multimode
