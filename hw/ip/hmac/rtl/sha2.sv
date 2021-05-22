// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SHA-256 algorithm
//

module sha2 import hmac_pkg::*; (
  input clk_i,
  input rst_ni,

  input            wipe_secret,
  input sha_word_t wipe_v,

  // FIFO read signal
  input             fifo_rvalid,
  input  sha_fifo_t fifo_rdata,
  output logic      fifo_rready,

  // Control signals
  input        sha_en,   // If disabled, it clears internal content.
  input        hash_start,
  input        hash_process,
  output logic hash_done,

  input        [63:0] message_length,   // bits but byte based
  output sha_word_t [7:0] digest,

  output logic idle
);

  localparam int unsigned RoundWidth = $clog2(NumRound);

  logic msg_feed_complete;

  logic      shaf_rready;
  sha_word_t shaf_rdata;
  logic      shaf_rvalid;

  logic [RoundWidth-1:0] round;

  logic      [3:0]  w_index;
  sha_word_t [15:0] w;

  localparam sha_word_t ZeroWord = '0;

  // w, hash, digest update logic control signals
  logic update_w_from_fifo, calculate_next_w;
  logic init_hash, run_hash, complete_one_chunk;
  logic update_digest, clear_digest;

  logic hash_done_next; // to meet the phase with digest value.

  sha_word_t [7:0] hash;    // a,b,c,d,e,f,g,h

  // Fill up w
  always_ff @(posedge clk_i or negedge rst_ni) begin : fill_w
    if (!rst_ni) begin
      w <= '0;
    end else if (wipe_secret) begin
      w <= w ^ {16{wipe_v}};
    end else if (!sha_en) begin
      w <= '0;
    end else if (!run_hash && update_w_from_fifo) begin
      // this logic runs at the first stage of SHA.
      w <= {shaf_rdata, w[15:1]};
    end else if (calculate_next_w) begin
      w <= {calc_w(w[0], w[1], w[9], w[14]), w[15:1]};
    //end else if (run_hash && update_w_from_fifo) begin
    //  // This code runs when round is in [48, 63]. At this time, it reads from the fifo
    //  // to fill the register if available. If FIFO goes to empty, w_index doesn't increase
    //  // and it cannot reach 15. Then the sha engine doesn't start, which introduces latency.
    //  //
    //  // But in this case, still w should be shifted to feed SHA compress engine. Then
    //  // fifo_rdata should be inserted in the middle of w index.
    //  // w[64-round + w_index] <= fifo_rdata;
    //  for (int i = 0 ; i < 16 ; i++) begin
    //    if (i == (64 - round + w_index)) begin
    //      w[i] <= shaf_rdata;
    //    end else if (i == 15) begin
    //      w[i] <= '0;
    //    end else begin
    //      w[i] <= w[i+1];
    //    end
    //  end
    end else if (run_hash) begin
      // Just shift-out. There's no incoming data
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
      hash <= compress( w[0], CubicRootPrime[round], hash);
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
        digest[i] <= InitHash[i];
      end
    end else if (!sha_en || clear_digest) begin
      digest <= '0;
    end else if (update_digest) begin
      for (int i = 0 ; i < 8 ; i++) begin
        digest[i] <= digest[i] + hash[i];
      end
    end
  end

  // round
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      round <= '0;
    end else if (!sha_en) begin
      round <= '0;
    end else if (run_hash) begin
      if (round == RoundWidth'(unsigned'(NumRound-1))) begin
        round <= '0;
      end else begin
        round <= round + 1;
      end
    end
  end

  // w_index
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      w_index <= '0;
    end else if (!sha_en) begin
      w_index <= '0;
    end else if (update_w_from_fifo) begin
      w_index <= w_index + 1;
    end
  end

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
    if (!rst_ni) begin
      fifo_st_q <= FifoIdle;
    end else begin
      fifo_st_q <= fifo_st_d;
    end
  end

  always_comb begin
    fifo_st_d = FifoIdle;
    update_w_from_fifo = 1'b0;
    hash_done_next = 1'b0;

    unique case (fifo_st_q)
      FifoIdle: begin
        if (hash_start) begin
          fifo_st_d = FifoLoadFromFifo;
        end else begin
          fifo_st_d = FifoIdle;
        end
      end

      FifoLoadFromFifo: begin
        if (!sha_en) begin
          fifo_st_d = FifoIdle;
          update_w_from_fifo = 1'b0;
        end else if (!shaf_rvalid) begin
          // Wait until it is filled
          fifo_st_d = FifoLoadFromFifo;
          update_w_from_fifo = 1'b0;
        end else if (w_index == 4'd 15) begin
          fifo_st_d = FifoWait;
          update_w_from_fifo = 1'b1;
        end else begin
          fifo_st_d = FifoLoadFromFifo;
          update_w_from_fifo = 1'b1;
        end
      end

      FifoWait: begin
        // Wait until next fetch begins (begin at round == 48)a
        if (msg_feed_complete && complete_one_chunk) begin
          fifo_st_d = FifoIdle;

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

  // SHA control
  typedef enum logic [1:0] {
    ShaIdle,
    ShaCompress,
    ShaUpdateDigest
  } sha_st_t;

  sha_st_t sha_st_q, sha_st_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sha_st_q <= ShaIdle;
    end else begin
      sha_st_q <= sha_st_d;
    end
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

        if (round < 48) begin
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
          sha_st_d = ShaCompress;
        end else begin
          sha_st_d = ShaIdle;
        end
      end

      default: begin
        sha_st_d = ShaIdle;
      end
    endcase
  end

  // complete_one_chunk
  assign complete_one_chunk = (round == 6'd63);

  sha2_pad u_pad (
    .clk_i,
    .rst_ni,

    .wipe_secret,
    .wipe_v,

    .fifo_rvalid,
    .fifo_rdata,
    .fifo_rready,

    .shaf_rvalid,
    .shaf_rdata,
    .shaf_rready,

    .sha_en,
    .hash_start,
    .hash_process,
    .hash_done,

    .message_length,
    .msg_feed_complete
  );

  // Idle
  assign idle = (fifo_st_q == FifoIdle) && (sha_st_q == ShaIdle) && !hash_start;

endmodule : sha2
