// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// USBDPI -- act as a simple host for usbuart device

// Bits in LOG_LEVEL sets what is output on socket
// 0x01 -- monitor_usb (packet level)
// 0x02 -- more verbose monitor
// 0x08 -- bit level

module usbdpi #(
  parameter string NAME = "usb0",
  parameter LOG_LEVEL = 1
)(
  input  logic clk_i,
  input  logic rst_ni,
  input  logic clk_48MHz_i,
  output logic dp_p2d,
  input  logic dp_d2p,
  input  logic dp_en_d2p,
  output logic dn_p2d,
  input  logic dn_d2p,
  input  logic dn_en_d2p,
  output logic d_p2d,
  input  logic d_d2p,
  input  logic d_en_d2p,
  input  logic se0_d2p,
  input  logic rx_enable_d2p,
  input  logic tx_use_d_se0_d2p,

  output logic sense_p2d,
  input  logic pullupdp_d2p,
  input  logic pullupdn_d2p
);
  import "DPI-C" function
    chandle usbdpi_create(input string name, input int loglevel);

  import "DPI-C" function
    void usbdpi_device_to_host(input chandle ctx, input bit [10:0] d2p);

  import "DPI-C" function
    void usbdpi_close(input chandle ctx);

  import "DPI-C" function
    byte usbdpi_host_to_device(input chandle ctx, input bit [10:0] d2p);

  chandle ctx;

  initial begin
    ctx = usbdpi_create(NAME, LOG_LEVEL);
    sense_p2d = 1'b0;
  end

  final begin
    usbdpi_close(ctx);
  end

  logic [10:0] d2p;
  logic [10:0] d2p_r;
  logic       unused_dummy;
  logic       unused_clk = clk_i;
  logic       unused_rst = rst_ni;
  logic       dp_int, dn_int, d_last;
  logic       flip_detect, pullup_detect, rx_enable;

  // Detect a request to flip pins by the DN resistor being applied
  assign flip_detect = pullupdn_d2p;
  assign pullup_detect = pullupdp_d2p || pullupdn_d2p;
  assign rx_enable = rx_enable_d2p;

  assign d2p = {dp_d2p, dp_en_d2p, dn_d2p, dn_en_d2p, d_d2p, d_en_d2p, se0_d2p, tx_use_d_se0_d2p,
                pullupdp_d2p, pullupdn_d2p, rx_enable};
  always_ff @(posedge clk_48MHz_i) begin
    if (!sense_p2d || pullup_detect) begin
      automatic byte p2d = usbdpi_host_to_device(ctx, d2p);
      d_last <= d_p2d;
      dp_int <= p2d[2];
      dn_int <= p2d[1];
      sense_p2d <= p2d[0];
      unused_dummy <= |p2d[7:4];
      d2p_r <= d2p;
      if (d2p_r != d2p) begin
        usbdpi_device_to_host(ctx, d2p);
      end
    end else begin // if (pullup_detect)
      d_last <= 0;
      dp_int <= 0;
      dn_int <= 0;
    end
  end

  always_comb begin : proc_data
    d_p2d = d_last;
    if (rx_enable) begin
      // Differential receiver is enabled.
      // If host is driving, update d_p2d only if there is a valid differential
      // value.
      if (d_en_d2p) begin
        d_p2d = d_d2p;
      end else if (dp_int && !dn_int) begin
        d_p2d = 1'b1;
      end else if (!dp_int && dn_int) begin
        d_p2d = 1'b0;
      end
    end
    if (dp_en_d2p) begin
      if (tx_use_d_se0_d2p) begin
        dp_p2d = se0_d2p ? 1'b0 : flip_detect ^ d_d2p;
      end else begin
        dp_p2d = dp_d2p;
      end
    end else begin
      dp_p2d = dp_int;
    end
    if (dn_en_d2p) begin
      if (tx_use_d_se0_d2p) begin
        dn_p2d = se0_d2p ? 1'b0 : flip_detect ^ ~d_d2p;
      end else begin
        dn_p2d = dn_d2p;
      end
    end else begin
      dn_p2d = dn_int;
    end
  end
endmodule
