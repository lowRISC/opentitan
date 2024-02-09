// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// 32-bit input wrapper for the SHA-2 engine

module prim_sha2_32 import prim_sha2_pkg::*;
#(
  parameter bit MultimodeEn = 0 // assert to enable multi-mode feature
 ) (
  input clk_i,
  input rst_ni,

  input              wipe_secret_i,
  input sha_word32_t wipe_v_i,
  // Control signals and message words input to the message FIFO
  input               fifo_rvalid_i,      // indicates that there are data words/word parts
                                          // ready to write into the SHA-2 padding buffer
  input  sha_fifo32_t fifo_rdata_i,
  output logic        fifo_rready_o,      // indicates that the wrapper word accumulation buffer is
                                        // ready to receive words to feed into the SHA-2 engine
  // Control signals
  input                     sha_en_i, // if disabled, it clears internal content
  input                     hash_start_i,
  input                     hash_continue_i,
  input digest_mode_e       digest_mode_i,
  input                     hash_process_i,
  output logic              hash_done_o,
  input [127:0]             message_length_i, // use extended message length 128 bits
  input  sha_word64_t [7:0] digest_i,
  input  logic [7:0]        digest_we_i,
  output sha_word64_t [7:0] digest_o,         // use extended digest length
  output logic              hash_running_o,
  output logic              idle_o
);
  // signal definitions shared for both 256-bit and multi-mode
  sha_fifo64_t  full_word;
  logic sha_ready, hash_go;

  // Most operations and control signals are identical no matter if we are starting or re-starting
  // to hash.
  assign hash_go = hash_start_i | hash_continue_i;

  // tie off unused ports/port slices
  if (!MultimodeEn) begin : gen_tie_unused
    logic unused_signals;
    assign unused_signals = ^{message_length_i[127:64], digest_mode_i, hash_go};
  end

  // logic and prim_sha2 instantiation for MultimodeEn = 1
  if (MultimodeEn) begin : gen_multimode_logic
    // signal definitions for multi-mode
    sha_fifo64_t  word_buffer_d, word_buffer_q;
    logic [1:0]   word_part_count_d, word_part_count_q;
    logic         sha_process, process_flag_d, process_flag_q;
    logic         word_valid;
    logic         word_part_inc, word_part_reset;
    digest_mode_e digest_mode_flag_d, digest_mode_flag_q;

    always_comb begin : multimode_combinational
      word_part_inc    = 1'b0;
      word_part_reset  = 1'b0;
      full_word.mask   = 8'hFF; // to keep the padding buffer ready to receive
      full_word.data   = 64'h0;
      sha_process      = 1'b0;
      word_valid       = 1'b0;
      fifo_rready_o    = 1'b0;

      // assign word_buffer
      if (!sha_en_i || hash_go) word_buffer_d = 0;
      else                      word_buffer_d = word_buffer_q;

      if (sha_en_i && fifo_rvalid_i) begin // valid incoming word part and SHA engine is enabled
        if (word_part_count_q == 2'b00) begin
          if (digest_mode_flag_q != SHA2_256) begin
            // accumulate most significant 32 bits of word and mask bits
            word_buffer_d.data[63:32] = fifo_rdata_i.data;
            word_buffer_d.mask[7:4]   = fifo_rdata_i.mask;
            word_part_inc             = 1'b1;
            fifo_rready_o             = 1'b1;
            if (hash_process_i || process_flag_q) begin // ready to push out word (partial)
              word_valid      = 1'b1;
              // add least significant padding
              full_word.data  =  {fifo_rdata_i.data, 32'b0};
              full_word.mask  =  {fifo_rdata_i.mask, 4'h0};
              sha_process     = 1'b1;
              if (sha_ready == 1'b1) begin
                // if word has been absorbed into hash engine
                fifo_rready_o = 1'b1; // word pushed out to SHA engine, word buffer ready
                word_part_inc = 1'b0;
              end else begin
                fifo_rready_o = 1'b0;
              end
            end
          end else begin   // SHA2_256 so pad and push out the word
            word_valid = 1'b1;
            // store the word with most significant padding
            word_buffer_d.data = {32'b0, fifo_rdata_i.data};
            word_buffer_d.mask = {4'hF, fifo_rdata_i.mask}; // pad with all-1 byte mask

            // pad with all-zero data and all-one byte masking and push word out already for 256
            full_word.data =  {32'b0, fifo_rdata_i.data};
            full_word.mask = {4'hF, fifo_rdata_i.mask};
            if (hash_process_i || process_flag_q) begin
                sha_process = 1'b1;
            end
            if (sha_ready == 1'b1) begin
              // if word has been absorbed into hash engine
              fifo_rready_o = 1'b1; // word pushed out to SHA engine so word buffer ready
            end else begin
              fifo_rready_o = 1'b0;
            end
          end
        end else if (word_part_count_q == 2'b01) begin
          fifo_rready_o = 1'b1; // buffer still has room for another word
          // accumulate least significant 32 bits and mask
          word_buffer_d.data [31:0] = fifo_rdata_i.data;
          word_buffer_d.mask [3:0]  = fifo_rdata_i.mask;

          // now ready to pass full word through
          word_valid              = 1'b1;
          full_word.data [63:32]  = word_buffer_q.data[63:32];
          full_word.mask [7:4]    = word_buffer_q.mask[7:4];
          full_word.data [31:0]   = fifo_rdata_i.data;
          full_word.mask  [3:0]   = fifo_rdata_i.mask;

          if (hash_process_i || process_flag_q) begin
              sha_process = 1'b1;
          end
          if (sha_ready == 1'b1) begin
            // word has been consumed
            fifo_rready_o       = 1'b1; // word pushed out to SHA engine so word buffer ready
            word_part_reset   = 1'b1;
            word_part_inc     = 1'b0;
          end else begin
            fifo_rready_o       = 1'b1;
            word_part_inc     = 1'b1;
          end
        end else if (word_part_count_q == 2'b10) begin // word buffer is full and not loaded out yet
          // fifo_rready_o is now deasserted: accumulated word is waiting to be pushed out
          fifo_rready_o     = 1'b0;
          word_valid        = 1'b1; // word buffer is ready to shift word out to SHA engine
          full_word         = word_buffer_q;
          if (hash_process_i || process_flag_q) begin
              sha_process   = 1'b1;
          end
          if (sha_ready == 1'b1) begin // waiting on sha_ready to turn 1
            // do not assert fifo_rready_o yet
            word_part_reset = 1'b1;
          end
        end
      end else if (sha_en_i) begin // hash engine still enabled but no new valid input
        // provide the last latched input so long as hash is enabled
        full_word = word_buffer_q;
        if (word_part_count_q == 2'b00 && (hash_process_i || process_flag_q)) begin
          sha_process = 1'b1; // wait on hash_process_i
        end else if (word_part_count_q == 2'b01 && (hash_process_i || process_flag_q)) begin
          // 384/512: msg ended: apply 32-bit word packing and push last word
          full_word.data [31:0] = 32'b0;
          full_word.mask [3:0]  = 4'h0;
          word_valid            = 1'b1;
          sha_process           = 1'b1;
          if (sha_ready == 1'b1) begin // word has been consumed
            word_part_reset = 1'b1; // which will also reset word_valid in the next cycle
          end
        end else if (word_part_count_q == 2'b01) begin // word feeding stalled but msg not ended
          word_valid = 1'b0;
        end else if (word_part_count_q == 2'b10 && (hash_process_i || process_flag_q)) begin
          // 384/512: msg ended but last word still waiting to be fed in
          word_valid  = 1'b1;
          sha_process = 1'b1;
          if (sha_ready == 1'b1) begin // word has been consumed
            word_part_reset = 1'b1; // which will also reset word_valid in the next cycle
          end
        end else if (word_part_count_q == 2'b10) begin // word feeding stalled
          word_valid = 1'b0;
        end
      end

      // assign word_part_count_d
      if ((word_part_reset || hash_go || !sha_en_i)) begin
        word_part_count_d = '0;
      end else if (word_part_inc) begin
        word_part_count_d = word_part_count_q + 1'b1;
      end else begin
        word_part_count_d = word_part_count_q;
      end

      // assign digest_mode_flag_d
      if (hash_go)          digest_mode_flag_d = digest_mode_i;      // latch in configured mode
      else if (hash_done_o) digest_mode_flag_d = None;               // clear
      else                  digest_mode_flag_d = digest_mode_flag_q; // keep

      // assign process_flag
      if (!sha_en_i || hash_go) process_flag_d = 1'b0;
      else if (hash_process_i)  process_flag_d = 1'b1;
      else                      process_flag_d = process_flag_q;
    end : multimode_combinational

    prim_sha2 #(
      .MultimodeEn(1)
    ) u_prim_sha2_multimode (
      .clk_i (clk_i),
      .rst_ni (rst_ni),
      .wipe_secret_i      (wipe_secret_i),
      .wipe_v_i           ({wipe_v_i, wipe_v_i}),
      .fifo_rvalid_i      (word_valid),
      .fifo_rdata_i       (full_word),
      .fifo_rready_o      (sha_ready),
      .sha_en_i           (sha_en_i),
      .hash_start_i       (hash_start_i),
      .hash_continue_i    (hash_continue_i),
      .digest_mode_i      (digest_mode_i),
      .hash_process_i     (sha_process),
      .hash_done_o        (hash_done_o),
      .message_length_i   (message_length_i),
      .digest_i           (digest_i),
      .digest_we_i        (digest_we_i),
      .digest_o           (digest_o),
      .hash_running_o     (hash_running_o),
      .idle_o             (idle_o)
    );

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni)  word_part_count_q <= '0;
      else          word_part_count_q <= word_part_count_d;
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni)  word_buffer_q <= 0;
      else          word_buffer_q <= word_buffer_d;
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
     if (!rst_ni)          process_flag_q <= '0;
      else  process_flag_q <= process_flag_d;
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) digest_mode_flag_q <= None;
      else         digest_mode_flag_q <= digest_mode_flag_d;
    end
  // logic and prim_sha2 instantiation for MultimodeEn = 0
  end else begin : gen_sha256_logic  // MultimodeEn = 0
    always_comb begin : sha256_combinational
      full_word.data   = {32'b0, fifo_rdata_i.data};
      full_word.mask   = {4'hF,  fifo_rdata_i.mask};
      fifo_rready_o    = sha_ready;
    end : sha256_combinational

    prim_sha2 #(
      .MultimodeEn(0)
    ) u_prim_sha2_256 (
      .clk_i (clk_i),
      .rst_ni (rst_ni),
      .wipe_secret_i      (wipe_secret_i),
      .wipe_v_i           ({wipe_v_i, wipe_v_i}),
      .fifo_rvalid_i      (fifo_rvalid_i), // feed input directly
      .fifo_rdata_i       (full_word),
      .fifo_rready_o      (sha_ready),
      .sha_en_i           (sha_en_i),
      .hash_start_i       (hash_start_i),
      .hash_continue_i    (hash_continue_i),
      .digest_mode_i      (None),           // unused input port tied to ground
      .hash_process_i     (hash_process_i), // feed input port directly to SHA-2 engine
      .hash_done_o        (hash_done_o),
      .message_length_i   ({{64'b0}, message_length_i[63:0]}),
      .digest_i           (digest_i),
      .digest_we_i        (digest_we_i),
      .digest_o           (digest_o),
      .hash_running_o     (hash_running_o),
      .idle_o             (idle_o)
    );
  end

endmodule : prim_sha2_32
