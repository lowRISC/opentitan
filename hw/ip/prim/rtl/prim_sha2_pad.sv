// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SHA-256/Multi-Mode SHA-2 Padding logic

`include "prim_assert.sv"

module prim_sha2_pad import prim_sha2_pkg::*;
#(
  parameter bit MultimodeEn = 1
 ) (
  input clk_i,
  input rst_ni,

  // to actual FIFO
  input                 fifo_rvalid_i,
  input  sha_fifo64_t   fifo_rdata_i,
  output logic          fifo_rready_o,
  // from SHA2 compression engine
  output logic          shaf_rvalid_o,
  output sha_word64_t   shaf_rdata_o,
  input                 shaf_rready_i,
  input                 sha_en_i,
  input                 hash_start_i,
  input                 hash_continue_i,
  input digest_mode_e   digest_mode_i,
  input                 hash_process_i,
  input                 hash_done_o,
  input        [127:0]  message_length_i,   // # of bytes in bits (8 bits granularity)
  output logic          msg_feed_complete_o // indicates all message is feeded
);

  logic [127:0] tx_count_d, tx_count;    // fin received data count.
  logic         inc_txcount;
  logic         fifo_partial;
  logic         txcnt_eq_1a0;
  logic         hash_go;

  logic         hash_process_flag_d, hash_process_flag_q;
  digest_mode_e digest_mode_flag_d,  digest_mode_flag_q;

  // Most operations and control signals are identical no matter if we are starting or continuing
  // to hash.
  assign hash_go = hash_start_i | hash_continue_i;

  // tie off unused inport ports and signals
  if (!MultimodeEn) begin : gen_tie_unused
    logic unused_signals;
    assign unused_signals = ^{message_length_i[127:64]};
  end

  assign fifo_partial = MultimodeEn ? ~&fifo_rdata_i.mask :
                                      ~&fifo_rdata_i.mask[3:0];

  // tx_count[8:0] == 'h1c0 --> should send LenHi
  assign txcnt_eq_1a0 = (digest_mode_flag_q == SHA2_256   || ~MultimodeEn)               ?
                                                                        (tx_count[8:0] == 9'h1a0)  :
                        ((digest_mode_flag_q == SHA2_384) || (digest_mode_flag_q == SHA2_512)) ?
                                                                        (tx_count[9:0] == 10'h340) :
                                                                        '0;

  assign hash_process_flag_d = (~sha_en_i || hash_go || hash_done_o) ? 1'b0 :
                               hash_process_i                        ? 1'b1 :
                                                                          hash_process_flag_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)  hash_process_flag_q <= 1'b0;
    else          hash_process_flag_q <= hash_process_flag_d;
  end

  // data path: fout_wdata
  typedef enum logic [2:0] {
    FifoIn,         // fin_wdata, fin_wstrb
    Pad80,          // {8'h80, 8'h00} , strb (calc based on len[4:3])
    Pad00,          // 32'h0, full strb
    LenHi,          // len[63:32], full strb
    LenLo           // len[31:0], full strb
  } sel_data_e;
  sel_data_e sel_data;

  always_comb begin
    unique case (sel_data)
      FifoIn: begin
        shaf_rdata_o = fifo_rdata_i.data;
      end

      Pad80: begin
        // {a[7:0], b[7:0], c[7:0], d[7:0]}
        // msglen[4:3] == 00 |-> {'h80, 'h00, 'h00, 'h00}
        // msglen[4:3] == 01 |-> {msg,  'h80, 'h00, 'h00}
        // msglen[4:3] == 10 |-> {msg[15:0],  'h80, 'h00}
        // msglen[4:3] == 11 |-> {msg[23:0],        'h80}
        if ((digest_mode_flag_q == SHA2_256) || ~MultimodeEn) begin
          unique case (message_length_i[4:3])
            2'b 00:  shaf_rdata_o = 64'h 0000_0000_8000_0000;
            2'b 01:  shaf_rdata_o = {32'h 0000_0000, fifo_rdata_i.data[31:24], 24'h 8000_00};
            2'b 10:  shaf_rdata_o = {32'h 0000_0000, fifo_rdata_i.data[31:16], 16'h 8000};
            2'b 11:  shaf_rdata_o = {32'h 0000_0000, fifo_rdata_i.data[31: 8],  8'h 80};
            default: shaf_rdata_o = 64'h0;
          endcase
        end else if ((digest_mode_flag_q == SHA2_384) || (digest_mode_flag_q == SHA2_512)) begin
          unique case (message_length_i[5:3])
            3'b 000: shaf_rdata_o = 64'h 8000_0000_0000_0000;
            3'b 001: shaf_rdata_o = {fifo_rdata_i.data[63:56], 56'h 8000_0000_0000_00};
            3'b 010: shaf_rdata_o = {fifo_rdata_i.data[63:48], 48'h 8000_0000_0000};
            3'b 011: shaf_rdata_o = {fifo_rdata_i.data[63:40], 40'h 8000_0000_00};
            3'b 100: shaf_rdata_o = {fifo_rdata_i.data[63:32], 32'h 8000_0000};
            3'b 101: shaf_rdata_o = {fifo_rdata_i.data[63:24], 24'h 8000_00};
            3'b 110: shaf_rdata_o = {fifo_rdata_i.data[63:16], 16'h 8000};
            3'b 111: shaf_rdata_o = {fifo_rdata_i.data[63:8],  8'h 80};
            default: shaf_rdata_o = 64'h0;
          endcase
        end else
            shaf_rdata_o = '0;
      end

      Pad00: begin
        shaf_rdata_o = '0;
      end

      LenHi: begin
        shaf_rdata_o = ((digest_mode_flag_q == SHA2_256) || ~MultimodeEn) ?
                                                     {32'b0, message_length_i[63:32]}:
                       ((digest_mode_flag_q == SHA2_384) || (digest_mode_flag_q == SHA2_512)) ?
                                                     message_length_i[127:64] : '0;
      end

      LenLo: begin
        shaf_rdata_o = ((digest_mode_flag_q == SHA2_256) || ~MultimodeEn) ?
                                                     {32'b0, message_length_i[31:0]}:
                       ((digest_mode_flag_q == SHA2_384) || (digest_mode_flag_q == SHA2_512)) ?
                                                     message_length_i[63:0]: '0;
      end

      default: begin
        shaf_rdata_o = '0;
      end
    endcase

    if (!MultimodeEn) shaf_rdata_o [63:32] = 32'b0; // assign most sig 32 bits to constant 0
  end

  // Padded length
  // $ceil(message_length_i + 8 + 64, 512) -> message_length_i [8:0] + 440 and ignore carry
  //assign length_added = (message_length_i[8:0] + 9'h1b8) ;

  // fifo control
  // add 8'h 80 , N 8'h00, 64'h message_length_i

  // Steps
  // 1. `hash_start_i` from CPU (or DMA?)
  // 2. calculate `padded_length` from `message_length_i`
  // 3. Check if tx_count == message_length_i, then go to 5
  // 4. Receiving FIFO input (hand over to fifo output)
  // 5. Padding bit 1 (8'h80) followed by 8'h00 if needed
  // 6. Padding with length (high -> low)

  // State Machine
  typedef enum logic [2:0] {
    StIdle,        // fin_full to prevent unwanted FIFO write
    StFifoReceive, // Check tx_count == message_length_i
    StPad80,       // 8'h 80 + 8'h 00 X N
    StPad00,
    StLenHi,
    StLenLo
  } pad_st_e;

  pad_st_e st_q, st_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) st_q <= StIdle;
    else         st_q <= st_d;
  end

  // Next state
  always_comb begin
    shaf_rvalid_o = 1'b0;
    inc_txcount   = 1'b0;
    sel_data      = FifoIn;
    fifo_rready_o = 1'b0;
    st_d          = StIdle;

    unique case (st_q)
      StIdle: begin
        sel_data      = FifoIn;
        shaf_rvalid_o = 1'b0;
        if (sha_en_i && hash_go) begin
          inc_txcount = 1'b0;
          st_d        = StFifoReceive;
        end else begin
          st_d        = StIdle;
        end
      end

      StFifoReceive: begin
        sel_data = FifoIn;
        if (fifo_partial && fifo_rvalid_i) begin
          // End of the message (last bit is not word-aligned) , assume hash_process_flag is set
          shaf_rvalid_o = 1'b0; // Update entry at StPad80
          inc_txcount   = 1'b0;
          fifo_rready_o = 1'b0;
          st_d = StPad80;
        end else if (!hash_process_flag_q) begin
          fifo_rready_o = shaf_rready_i;
          shaf_rvalid_o = fifo_rvalid_i;
          inc_txcount   = shaf_rready_i;
          st_d = StFifoReceive;
        end else if (((tx_count        == message_length_i) & MultimodeEn) ||
                     ((tx_count [63:0] == message_length_i [63:0]) & !MultimodeEn)) begin
          // already received all msg and was waiting process flag
          shaf_rvalid_o = 1'b0;
          inc_txcount   = 1'b0;
          fifo_rready_o = 1'b0;
          st_d = StPad80;
        end else begin
          shaf_rvalid_o = fifo_rvalid_i;
          fifo_rready_o = shaf_rready_i; // 0 always
          inc_txcount   = shaf_rready_i; // 0 always
          st_d = StFifoReceive;
        end
      end

      StPad80: begin
        sel_data      = Pad80;
        shaf_rvalid_o = 1'b1;
        fifo_rready_o = (digest_mode_flag_q == SHA2_256 || ~MultimodeEn) ?
                        shaf_rready_i && |message_length_i[4:3] :
                        ((digest_mode_flag_q == SHA2_384) || (digest_mode_flag_q == SHA2_512)) ?
                        shaf_rready_i && |message_length_i[5:3] : '0; // Only when partial

        // exactly 192 bits left, do not need to pad00's
        if (shaf_rready_i && txcnt_eq_1a0) begin
          st_d        = StLenHi;
          inc_txcount = 1'b1;
        // it does not matter if value is < or > than 416 bits.  If it's the former, 00 pad until
        // length field.  If >, then the next chunk will contain the length field with appropriate
        // 0 padding.
        end else if (shaf_rready_i && !txcnt_eq_1a0) begin
          st_d        = StPad00;
          inc_txcount = 1'b1;
        end else begin
          st_d        = StPad80;
          inc_txcount = 1'b0;
        end

        // # Below part is temporal code to speed up the SHA by 16 clocks per chunk
        // # (80 clk --> 64 clk)
        // # leaving this as a reference but needs to verify it.
        //if (shaf_rready_i && !txcnt_eq_1a0) begin
        //  st_d = StPad00;
        //
        //  inc_txcount = 1'b1;
        //  shaf_rvalid_o = (msg_word_aligned) ? 1'b1 : fifo_rvalid;
        //  fifo_rready = (msg_word_aligned) ? 1'b0 : 1'b1;
        //end else if (!shaf_rready_i && !txcnt_eq_1a0) begin
        //  st_d = StPad80;
        //
        //  inc_txcount = 1'b0;
        //  shaf_rvalid_o = (msg_word_aligned) ? 1'b1 : fifo_rvalid;
        //
        //end else if (shaf_rready_i && txcnt_eq_1a0) begin
        //  st_d = StLenHi;
        //  inc_txcount = 1'b1;
        //end else begin
        //  // !shaf_rready_i && txcnt_eq_1a0 , just wait until fifo_rready asserted
        //  st_d = StPad80;
        //  inc_txcount = 1'b0;
        //end
      end

      StPad00: begin
        sel_data      = Pad00;
        shaf_rvalid_o = 1'b1;

        if (shaf_rready_i) begin
          inc_txcount = 1'b1;
          if (txcnt_eq_1a0) st_d = StLenHi;
          else              st_d = StPad00;
        end else begin
          st_d = StPad00;
        end
      end

      StLenHi: begin
        sel_data      = LenHi;
        shaf_rvalid_o = 1'b1;

        if (shaf_rready_i) begin
          st_d = StLenLo;
          inc_txcount = 1'b1;
        end else begin
          st_d = StLenHi;
          inc_txcount = 1'b0;
        end
      end

      StLenLo: begin
        sel_data        = LenLo;
        shaf_rvalid_o   = 1'b1;

        if (shaf_rready_i) begin
          st_d        = StIdle;
          inc_txcount = 1'b1;
        end else begin
          st_d        = StLenLo;
          inc_txcount = 1'b0;
        end
      end

      default: begin
        st_d = StIdle;
      end
    endcase

    if (!sha_en_i)    st_d = StIdle;
    else if (hash_go) st_d = StFifoReceive;
  end

  // tx_count
  always_comb begin
    tx_count_d = tx_count;

    if (hash_start_i) begin
      // When starting a fresh hash, initialize the data counter to zero.
      tx_count_d = '0;
    end else if (hash_continue_i) begin
      // When continuing to hash, set the data counter to the current message length.
      tx_count_d = message_length_i;
    end else if (inc_txcount) begin
      if ((digest_mode_flag_q == SHA2_256) || !MultimodeEn) begin
        tx_count_d[127:5] = tx_count[127:5] + 1'b1;
      end else if ((digest_mode_flag_q == SHA2_384) || (digest_mode_flag_q == SHA2_512)) begin
        tx_count_d[127:6] = tx_count[127:6] + 1'b1;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) tx_count <= '0;
    else         tx_count <= tx_count_d;
  end

  assign digest_mode_flag_d = hash_start_i ? digest_mode_i  :    // latch in configured mode
                              hash_done_o  ? None           :    // clear
                                             digest_mode_flag_q; // keep

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)  digest_mode_flag_q <= None;
    else          digest_mode_flag_q <= digest_mode_flag_d;
  end

  // State machine is in Idle only when it meets tx_count == message length
  assign msg_feed_complete_o = hash_process_flag_q && (st_q == StIdle);

endmodule
