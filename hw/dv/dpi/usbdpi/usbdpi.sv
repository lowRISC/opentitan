// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// USBDPI -- act as a simple host for usbuart device

// Bits in LOG_LEVEL sets what is output on socket
// 0x01 -- monitor_usb (packet level)
// 0x08 -- bit level

module usbdpi
  #(
  parameter string NAME = "usb0",
  parameter LOG_LEVEL = 1
  )(
  input  clk_i,
  input  rst_ni,
  input  clk_48MHz_i,
  output dp_p2d,
  input  dp_d2p,
  input  dp_en_d2p,
  output dn_p2d,
  input  dn_d2p,
  input  dn_en_d2p,
  output sense_p2d,
  input  pullup_d2p,
  input  pullup_en_d2p
);
  import "DPI-C" function
    chandle usbdpi_create(input string name, input int loglevel);

  import "DPI-C" function
    void usbdpi_device_to_host(input chandle ctx, input [4:0] d2p);

  import "DPI-C" function
    void usbdpi_close(input chandle ctx);

  import "DPI-C" function
    byte usbdpi_host_to_device(input chandle ctx, input [4:0] d2p);

  chandle ctx;

  initial begin
    ctx = usbdpi_create(NAME, LOG_LEVEL);
  end

  final begin
    usbdpi_close(ctx);
  end

  logic [4:0] d2p;
  logic [4:0] d2p_r;
  logic       unused_dummy;
  logic       unused_clk = clk_i;
  logic       unused_rst = rst_ni;

  assign d2p = {dp_d2p, dp_en_d2p, dn_d2p, dn_en_d2p, pullup_d2p & pullup_en_d2p};
  always_ff @(posedge clk_48MHz_i) begin
    automatic byte p2d = usbdpi_host_to_device(ctx, d2p);
    dp_p2d <= p2d[2];
    dn_p2d <= p2d[1];
    sense_p2d <= p2d[0];
    unused_dummy <= |p2d[7:3];
    d2p_r <= d2p;
    if (d2p_r != d2p) begin
      usbdpi_device_to_host(ctx, d2p);
    end
  end
endmodule
