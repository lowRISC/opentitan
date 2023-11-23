// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Multi-mode SHA-2 engine padding logic
//

`include "prim_assert.sv"

module prim_sha2_pad import prim_sha2_pkg::*; (
  input clk_i,
  input rst_ni,

  // to actual FIFO
  input                 fifo_rvalid,
  input  sha_fifo64_t   fifo_rdata,
  output logic          fifo_rready,

  // from SHA2 compression engine
  output logic          shaf_rvalid,
  output sha_word64_t   shaf_rdata,
  input                 shaf_rready,

  input                 sha_en,
  input                 hash_start,
  input digest_mode_e   digest_mode,
  input                 hash_process,
  input                 hash_done,

  input        [127:0]  message_length, // # of bytes in bits (8 bits granularity)
  output logic          msg_feed_complete // indicates all message is feeded
);

  logic [127:0] tx_count;    // fin received data count.
  logic         inc_txcount;
  logic         fifo_partial;
  logic         txcnt_eq_1a0;
  logic         hash_process_flag; // set by hash_process, clear by hash_done
  digest_mode_e digest_mode_flag;

  assign fifo_partial = ~&fifo_rdata.mask;

  // tx_count[8:0] == 'h1c0 --> should send LenHi
  assign txcnt_eq_1a0 = (digest_mode_flag == SHA2_256) ? (tx_count[8:0] == 9'h1a0) :
                        ((digest_mode_flag == SHA2_384) || (digest_mode_flag == SHA2_512)) ?
                        (tx_count[9:0] == 10'h340) : '0;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)                                 hash_process_flag <= 1'b0;
    else if (!sha_en || hash_start || hash_done) hash_process_flag <= 1'b0;
    else if (hash_process)                       hash_process_flag <= 1'b1;
  end

  // Data path: fout_wdata
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
        shaf_rdata = fifo_rdata.data;
      end

      Pad80: begin
        // {a[7:0], b[7:0], c[7:0], d[7:0]}
        // msglen[4:3] == 00 |-> {'h80, 'h00, 'h00, 'h00}
        // msglen[4:3] == 01 |-> {msg,  'h80, 'h00, 'h00}
        // msglen[4:3] == 10 |-> {msg[15:0],  'h80, 'h00}
        // msglen[4:3] == 11 |-> {msg[23:0],        'h80}
        if (digest_mode_flag == SHA2_256) begin
          unique case (message_length[4:3])
            2'b 00:  shaf_rdata = 64'h 0000_0000_8000_0000;
            2'b 01:  shaf_rdata = {32'h 0000_0000, fifo_rdata.data[31:24], 24'h 8000_00};
            2'b 10:  shaf_rdata = {32'h 0000_0000, fifo_rdata.data[31:16], 16'h 8000};
            2'b 11:  shaf_rdata = {32'h 0000_0000, fifo_rdata.data[31: 8],  8'h 80};
            default: shaf_rdata = 64'h0;
          endcase
        end else if ((digest_mode_flag == SHA2_384) || (digest_mode_flag == SHA2_512)) begin
          unique case (message_length[5:3])
            3'b 000: shaf_rdata = 64'h 8000_0000_0000_0000;
            3'b 001: shaf_rdata = {fifo_rdata.data[63:56], 56'h 8000_0000_0000_00};
            3'b 010: shaf_rdata = {fifo_rdata.data[63:48], 48'h 8000_0000_0000};
            3'b 011: shaf_rdata = {fifo_rdata.data[63:40], 40'h 8000_0000_00};
            3'b 100: shaf_rdata = {fifo_rdata.data[63:32], 32'h 8000_0000};
            3'b 101: shaf_rdata = {fifo_rdata.data[63:24], 24'h 8000_00};
            3'b 110: shaf_rdata = {fifo_rdata.data[63:16], 16'h 8000};
            3'b 111: shaf_rdata = {fifo_rdata.data[63:8],  8'h 80};
            default: shaf_rdata = 64'h0;
          endcase
        end else
            shaf_rdata = '0;
      end

      Pad00: begin
        shaf_rdata = '0;
      end

      LenHi: begin
        shaf_rdata = (digest_mode_flag == SHA2_256) ? {32'b0, message_length[63:32]}:
                     ((digest_mode_flag == SHA2_384) || (digest_mode_flag == SHA2_512)) ?
                     message_length[127:64] : '0;
      end

      LenLo: begin
        shaf_rdata = (digest_mode_flag == SHA2_256) ? {32'b0, message_length[31:0]}:
                     ((digest_mode_flag == SHA2_384) || (digest_mode_flag == SHA2_512)) ?
                     message_length[63:0]: '0;
      end

      default: begin
        shaf_rdata = '0;
      end
    endcase
  end

  // Padded length
  // $ceil(message_length + 8 + 64, 512) -> message_length [8:0] + 440 and ignore carry
  //assign length_added = (message_length[8:0] + 9'h1b8) ;

  // fifo control
  // add 8'h 80 , N 8'h00, 64'h message_length

  // Steps
  // 1. `hash_start` from CPU (or DMA?)
  // 2. calculate `padded_length` from `message_length`
  // 3. Check if tx_count == message_length, then go to 5
  // 4. Receiving FIFO input (hand over to fifo output)
  // 5. Padding bit 1 (8'h80) followed by 8'h00 if needed
  // 6. Padding with length (high -> low)

  // State Machine
  typedef enum logic [2:0] {
    StIdle,        // fin_full to prevent unwanted FIFO write
    StFifoReceive, // Check tx_count == message_length
    StPad80,       // 8'h 80 + 8'h 00 X N
    StPad00,
    StLenHi,
    StLenLo
  } pad_st_e;

  pad_st_e st_q, st_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) st_q <= StIdle;
    else if (!sha_en) st_q <= StIdle;
    else if (hash_start) st_q <= StFifoReceive;
    else st_q <= st_d;
  end

  // Next state
  always_comb begin
    shaf_rvalid = 1'b0;
    inc_txcount = 1'b0;
    sel_data    = FifoIn;
    fifo_rready = 1'b0;
    st_d        = StIdle;

    unique case (st_q)
      StIdle: begin
        sel_data    = FifoIn;
        shaf_rvalid = 1'b0;
        if (sha_en && hash_start) begin
          inc_txcount = 1'b0;
          st_d        = StFifoReceive;
        end else begin
          st_d        = StIdle;
        end
      end

      StFifoReceive: begin
        sel_data = FifoIn;
        if (fifo_partial && fifo_rvalid) begin
          // End of the message (last bit is not word-aligned) , assume hash_process_flag is set
          shaf_rvalid = 1'b0; // Update entry at StPad80
          inc_txcount = 1'b0;
          fifo_rready = 1'b0;
          st_d = StPad80;
        end else if (!hash_process_flag) begin
          fifo_rready = shaf_rready;
          shaf_rvalid = fifo_rvalid;
          inc_txcount = shaf_rready;
          st_d = StFifoReceive;
        end else if (tx_count == message_length) begin
          // already received all msg and was waiting process flag
          shaf_rvalid  = 1'b0;
          inc_txcount  = 1'b0;
          fifo_rready  = 1'b0;
          st_d = StPad80;
        end else begin
          shaf_rvalid = fifo_rvalid;
          fifo_rready = shaf_rready; // 0 always
          inc_txcount = shaf_rready; // 0 always
          st_d = StFifoReceive;
        end
      end

      StPad80: begin
        sel_data    = Pad80;
        shaf_rvalid = 1'b1;
        fifo_rready = (digest_mode_flag == SHA2_256) ? shaf_rready && |message_length[4:3]:
                      ((digest_mode_flag == SHA2_384) || (digest_mode_flag == SHA2_512)) ?
                      shaf_rready && |message_length[5:3] : '0; // Only when partial

        // exactly 192 bits left, do not need to pad00's
        if (shaf_rready && txcnt_eq_1a0) begin
          st_d = StLenHi;
          inc_txcount = 1'b1;
        // it does not matter if value is < or > than 416 bits.  If it's the former, 00 pad until
        // length field.  If >, then the next chunk will contain the length field with appropriate
        // 0 padding.
        end else if (shaf_rready && !txcnt_eq_1a0) begin
          st_d = StPad00;
          inc_txcount = 1'b1;
        end else begin
          st_d = StPad80;
          inc_txcount = 1'b0;
        end

        // # Below part is temporal code to speed up the SHA by 16 clocks per chunk
        // # (80 clk --> 64 clk)
        // # leaving this as a reference but needs to verify it.
        //if (shaf_rready && !txcnt_eq_1a0) begin
        //  st_d = StPad00;
        //
        //  inc_txcount = 1'b1;
        //  shaf_rvalid = (msg_word_aligned) ? 1'b1 : fifo_rvalid;
        //  fifo_rready = (msg_word_aligned) ? 1'b0 : 1'b1;
        //end else if (!shaf_rready && !txcnt_eq_1a0) begin
        //  st_d = StPad80;
        //
        //  inc_txcount = 1'b0;
        //  shaf_rvalid = (msg_word_aligned) ? 1'b1 : fifo_rvalid;
        //
        //end else if (shaf_rready && txcnt_eq_1a0) begin
        //  st_d = StLenHi;
        //  inc_txcount = 1'b1;
        //end else begin
        //  // !shaf_rready && txcnt_eq_1a0 , just wait until fifo_rready asserted
        //  st_d = StPad80;
        //  inc_txcount = 1'b0;
        //end
      end

      StPad00: begin
        sel_data = Pad00;
        shaf_rvalid = 1'b1;

        if (shaf_rready) begin
          inc_txcount = 1'b1;
          if (txcnt_eq_1a0) st_d = StLenHi;
          else st_d = StPad00;
        end else begin
          st_d = StPad00;
        end
      end

      StLenHi: begin
        sel_data    = LenHi;
        shaf_rvalid = 1'b1;

        if (shaf_rready) begin
          st_d = StLenLo;
          inc_txcount = 1'b1;
        end else begin
          st_d = StLenHi;
          inc_txcount = 1'b0;
        end
      end

      StLenLo: begin
        sel_data      = LenLo;
        shaf_rvalid   = 1'b1;

        if (shaf_rready) begin
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
  end

  // tx_count
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      tx_count <= '0;
    end else if (hash_start) begin
      tx_count <= '0;
    end else if (inc_txcount) begin
      if (digest_mode_flag == SHA2_256) begin
        tx_count[127:5] <= tx_count[127:5] + 1'b1;
      end else if ((digest_mode_flag == SHA2_384) ||(digest_mode_flag == SHA2_512)) begin
        tx_count[127:6] <= tx_count[127:6] + 1'b1;
      end
    end
  end

  // Latch SHA-2 configured mode
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)                digest_mode_flag <= None;
    else if (hash_start)        digest_mode_flag <= digest_mode;
    else if (hash_done == 1'b1) digest_mode_flag <= None;
  end

  // State machine is in Idle only when it meets tx_count == message length
  assign msg_feed_complete = hash_process_flag && (st_q == StIdle);

endmodule
