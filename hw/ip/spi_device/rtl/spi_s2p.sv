// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SPI Serial-to-Parallel interface

module spi_s2p
  import spi_device_pkg::*;
(
  input clk_i,
  input rst_ni, // inverted CSb input

  // SPI data
  input [3:0] s_i,

  // to following logic
  output logic               data_valid_o,
  output spi_byte_t          data_o,

  // Configuration
  input                             order_i,
  input spi_device_pkg::io_mode_e   io_mode_i
);

  /////////////////
  // Definitions //
  /////////////////
  // Maximum Length of a transaction is:
  // 8 bit opcode + 24 or 32 bit address +
  // max 8 bit dummy cycle + 256B payload
  // Or in FwMode, half of DPSRAM
  localparam int unsigned Bits     = $bits(spi_byte_t);
  localparam int unsigned BitWidth = $clog2(Bits);

  typedef logic [BitWidth-1:0] count_t;
  typedef logic [BitCntW-1:0] bitcount_t;

  count_t cnt;

  spi_byte_t data_d, data_q;

  always_comb begin
    unique case (io_mode_i)
      SingleIO: begin
        data_d = (order_i) ? {s_i[0], data_q[7:1]} : {data_q[6:0], s_i[0]};
      end

      DualIO: begin
        data_d = (order_i) ? {s_i[1:0], data_q[7:2]} : {data_q[5:0], s_i[1:0]};
      end

      QuadIO: begin
        data_d = (order_i) ? {s_i[3:0], data_q[7:4]} : {data_q[3:0], s_i[3:0]};
      end

      default: begin
        data_d = data_q;
      end
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_q <= '0;
    end else begin
      data_q <= data_d;
    end
  end

  // send un-latched data
  assign data_o = data_d;

  // Bitcount in a byte
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cnt <= count_t'(Bits-1);
    end else if (cnt == '0) begin
      cnt <= count_t'(Bits-1);
    end else begin
      unique case (io_mode_i)
        SingleIO: cnt <= cnt - count_t'('h1);
        DualIO:   cnt <= cnt - count_t'('h2);
        QuadIO:   cnt <= cnt - count_t'('h4);
        default:  cnt <= cnt;
      endcase
    end
  end

  // data valid
  always_comb begin
    unique case (io_mode_i)
      SingleIO: data_valid_o = (cnt == 'h0);
      DualIO:   data_valid_o = (cnt == 'h1);
      QuadIO:   data_valid_o = (cnt == 'h3);
      default:  data_valid_o = 1'b 0;
    endcase
  end

  ////////////////
  // Assertions //
  ////////////////

  // Right after reset (CSb assert), the io_mode_i shall be Single IO
  // to decode SPI Opcode.
  `ASSERT(IoModeDefault_A, $rose(rst_ni) |-> io_mode_i == SingleIO, clk_i, 0)

endmodule
