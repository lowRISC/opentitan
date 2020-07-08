// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// SPIDPI -- act as a simple host for SPI device

// Bits in LOG_LEVEL sets what is output on info socket
// 0x01 -- monitor packets
// 0x08 -- bit level

module spidpi
  #(
  parameter string NAME = "spi0",
  parameter MODE = 0,
  parameter LOG_LEVEL = 9
  )(
  input  logic clk_i,
  input  logic rst_ni,
  output logic spi_device_sck_o,
  output logic spi_device_csb_o,
  output logic spi_device_sdi_o,
  input  logic spi_device_sdo_i,
  input  logic spi_device_sdo_en_i

);
  import "DPI-C" function
    chandle spidpi_create(input string name, input int mode, input int loglevel);

  import "DPI-C" function
    void spidpi_close(input chandle ctx);

  import "DPI-C" function
    byte spidpi_tick(input chandle ctx_void, input [1:0] d2p_data);

  chandle ctx;

  initial begin
    ctx = spidpi_create(NAME, MODE, LOG_LEVEL);
  end

  final begin
    spidpi_close(ctx);
  end

  logic       unused_rst = rst_ni;
  logic [1:0] d2p;
  logic       unused_dummy;

  assign d2p = { spi_device_sdo_i, spi_device_sdo_en_i};
  always_ff @(posedge clk_i) begin
    automatic byte p2d = spidpi_tick(ctx, d2p);
    spi_device_sck_o <= p2d[0];
    spi_device_csb_o <= p2d[1];
    spi_device_sdi_o <= p2d[2];
    // stop verilator warning
    unused_dummy <= |p2d[7:3];
  end
endmodule
