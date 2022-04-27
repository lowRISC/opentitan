// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SPI byte to SPI (Single/ Dual/ Quad)

module spi_p2s
  import spi_device_pkg::*;
(
  input clk_i,
  input rst_ni,

  // Input byte interface
  input            data_valid_i,
  input spi_byte_t data_i,
  output logic     data_sent_o,

  // SPI interface
  input  logic       csb_i, // for line floating
  output logic [3:0] s_en_o,
  output logic [3:0] s_o,

  // Configuration
  // If CPHA=1, then the first byte should be delayed.
  // But this does not matter in SPI Flash. Only applicable to Generic mode
  input cpha_i,

  // Control
  // txorder: controls which bit goes out first.
  input order_i,

  // IO mode
  input io_mode_e io_mode_i
);

  ////////////////
  // Definition //
  ////////////////

  localparam int unsigned Bits     = $bits(spi_byte_t);
  localparam int unsigned BitWidth = $clog2(Bits);

  typedef logic [BitWidth-1:0] count_t;

  typedef enum logic {
    TxIdle,
    TxActive
  } tx_state_e;
  tx_state_e tx_state;   // Only for handling CPHA

  // Latching io_mode_i when last beat is set.
  // This guarantees cnt not abruptly changed during operation
  // which affects `last_beat` again.
  io_mode_e io_mode;

  // in Mode3, the logic skips first clock edge to move to next bit.
  // This is not necessary for Flash / Passthrough mode. But Generic mode
  // sends the data through TX line right after reset
  logic first_beat, last_beat;

  count_t cnt;

  logic [3:0] out_enable;
  spi_byte_t out_shift, out_shift_d;

  // Enable selection
  // in Single mode, line 1 is for output.
  // in Dual mode, line 0:1 are for output
  // in Quad mode, all lines 0:3 are for output.
  always_comb begin
    out_enable = 4'b 0000; // default

    unique case (io_mode)
      SingleIO: begin
        out_enable = {2'b 00, data_valid_i, 1'b 0};
      end

      DualIO: begin
        out_enable = {2'b 00, {2{data_valid_i}}};
      end

      QuadIO: begin
        out_enable = {4{data_valid_i}};
      end

      default: begin
        out_enable = 4'b 0000;
      end
    endcase
  end

  assign s_en_o = (csb_i) ? 4'b 0000 : out_enable ;

  // `data_sent`
  // Popping signal is a little bit tricky if p2s supports Quad IO
  // The sent signal cannot be sent at the end of the beat, as it does not have
  // enought time to affect the FIFO.
  //
  // If the sent signal asserted at the first beat, at the very first byte of
  // SPI has no time to assert valid signal. So the sent signal does not affect
  // the FIFO. So the logic sends first byte twice.
  //
  // This won't affect in Flash mode as in Flash/Passthrough mode, first byte is
  // always SPI command. It does not send anything on the SPI bus.
  //
  // So, the logic generating `sent` signal looks not straightforward. It tries
  // assert second last beat. So, in SingleIO (right after reset always), it
  // asserts at 7th beat. Then the mode could be changed to Dual/ Quad.

  always_comb begin
    data_sent_o = 1'b 0;

    unique case (io_mode)
      SingleIO: data_sent_o = (cnt == 6);
      DualIO:   data_sent_o = (cnt == 2);
      QuadIO:   data_sent_o = (cnt == 0);
      default:  data_sent_o = '0;
    endcase
  end

  // data shift
  always_ff @(posedge clk_i) begin
    unique case (io_mode)
      SingleIO: begin
        out_shift <= (order_i) ? {1'b0, out_shift_d[7:1]} : {out_shift_d[6:0], 1'b0};
      end

      DualIO: begin
        out_shift <= (order_i) ? {2'b0, out_shift_d[7:2]} : {out_shift_d[5:0], 2'b0};
      end

      QuadIO: begin
        out_shift <= (order_i) ? {4'b0, out_shift_d[7:4]} : {out_shift_d[3:0], 4'b0};
      end

      default: begin
        out_shift <= out_shift_d;
      end
    endcase
  end

  // out_shift_d
  assign out_shift_d = (first_beat) ? data_i : out_shift;

  // SPI out
  always_comb begin
    s_o = 4'b 0000;

    unique case (io_mode)
      SingleIO: begin
        s_o[1] = (order_i) ? ((!first_beat) ? out_shift[0] : data_i[0])
                                 : ((!first_beat) ? out_shift[7] : data_i[7]);
      end

      DualIO: begin
        s_o[1:0] = (order_i) ? ((!first_beat) ? out_shift[1:0] : data_i[1:0])
                                   : ((!first_beat) ? out_shift[7:6] : data_i[7:6]);
      end

      QuadIO: begin
        s_o = (order_i) ? ((!first_beat) ? out_shift[3:0] : data_i[3:0])
                              : ((!first_beat) ? out_shift[7:4] : data_i[7:4]);
      end

      default: begin
        s_o = 4'b 0000;
      end
    endcase
  end

  // io_mode
  // io_mode reset value is SingleIO (as described in assumption)
  // Previously, logic updated io_mode at every byte. It was to make io_mode
  // safer. However, as `io_mode_i` is updated at @iSCK (from spi_device top),
  // and also spi_p2s logic runs only when `data_valid_i` is high, the need of
  // latching logic disapears.
  //
  // Now, the logic uses `io_mode_i` directly.
  assign io_mode = io_mode_i;

  // cnt
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cnt <= BitWidth'(0);
    end else if (last_beat) begin
      cnt <= BitWidth'(0);
    end else if (data_valid_i && (tx_state != TxIdle || cpha_i == 1'b 0)) begin
      cnt <= cnt + 1'b 1;
    end
  end

  assign first_beat = (cnt == '0);

  // Last beat depends on the mode
  always_comb begin
    last_beat = 1'b 0;

    unique case (io_mode)
      SingleIO: last_beat = (cnt == BitWidth'('h7));
      DualIO:   last_beat = (cnt == BitWidth'('h3));
      QuadIO:   last_beat = (cnt == BitWidth'('h1));
      default:  last_beat = 1'b0;
    endcase
  end


  ///////////
  // State //
  ///////////

  // At reset, tx state sits in TxIdle. It moves to TxActive.
  // This is to delay the first posedge in Mode 3.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      tx_state <= TxIdle;
    end else begin
      tx_state <= TxActive;
    end
  end

  ////////////////
  // Assumption //
  ////////////////

  // Right after reset (CSb assert), the io_mode_i shall be Single IO
  `ASSERT(IoModeDefault_A, $rose(rst_ni) |-> io_mode_i == SingleIO, clk_i, 0)

  // io_mode shall be changed when bit 0.
  `ASSERT(IoModeChangeValid_A, $changed(io_mode_i) |-> first_beat)

endmodule : spi_p2s
