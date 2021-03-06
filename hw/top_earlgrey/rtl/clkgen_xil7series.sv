// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module clkgen_xil7series # (
  // Add BUFG if not done by downstream logic
  parameter bit AddClkBuf = 1
) (
  input  IO_CLK,
  input  IO_RST_N,
  input  jtag_srst_n,
  output clk_main,
  output clk_48MHz,
  output clk_aon,
  output rst_n
);
  logic locked_pll;
  logic io_clk_buf;
  logic io_rst_buf_n;
  logic clk_10_buf;
  logic clk_10_unbuf;
  logic clk_fb_buf;
  logic clk_fb_unbuf;
  logic clk_48_buf;
  logic clk_48_unbuf;
  logic clk_aon_buf;
  logic clk_aon_unbuf;

  // input clock buffer
  IBUF io_clk_ibuf (
    .I (IO_CLK),
    .O (io_clk_buf)
  );

  // input reset buffer
  IBUF io_rst_ibuf (
    .I (IO_RST_N),
    .O (io_rst_buf_n)
  );

  PLLE2_ADV #(
    .BANDWIDTH            ("OPTIMIZED"),
    .COMPENSATION         ("ZHOLD"),
    .STARTUP_WAIT         ("FALSE"),
    .DIVCLK_DIVIDE        (1),
    .CLKFBOUT_MULT        (12),
    .CLKFBOUT_PHASE       (0.000),
    .CLKOUT0_DIVIDE       (120),
    .CLKOUT0_PHASE        (0.000),
    .CLKOUT0_DUTY_CYCLE   (0.500),
    .CLKOUT1_DIVIDE       (25),
    .CLKOUT1_PHASE        (0.000),
    .CLKOUT1_DUTY_CYCLE   (0.500),
    .CLKOUT2_DIVIDE       (128),
    .CLKOUT2_PHASE        (0.000),
    .CLKOUT2_DUTY_CYCLE   (0.500),
    .CLKIN1_PERIOD        (10.000)
  ) pll (
    .CLKFBOUT            (clk_fb_unbuf),
    .CLKOUT0             (clk_10_unbuf),
    .CLKOUT1             (clk_48_unbuf),
    .CLKOUT2             (clk_aon_unbuf),
    .CLKOUT3             (),
    .CLKOUT4             (),
    .CLKOUT5             (),
     // Input clock control
    .CLKFBIN             (clk_fb_buf),
    .CLKIN1              (io_clk_buf),
    .CLKIN2              (1'b0),
     // Tied to always select the primary input clock
    .CLKINSEL            (1'b1),
    // Ports for dynamic reconfiguration
    .DADDR               (7'h0),
    .DCLK                (1'b0),
    .DEN                 (1'b0),
    .DI                  (16'h0),
    .DO                  (),
    .DRDY                (),
    .DWE                 (1'b0),
    // Other control and status signals
    .LOCKED              (locked_pll),
    .PWRDWN              (1'b0),
    // Do not reset PLL on external reset, otherwise ILA disconnects at a reset
    .RST                 (1'b0));

  // output buffering
  BUFG clk_fb_bufg (
    .I (clk_fb_unbuf),
    .O (clk_fb_buf)
  );

  BUFG clk_aon_bufg (
    .I (clk_aon_unbuf),
    .O (clk_aon_buf)
  );

  if (AddClkBuf == 1) begin : gen_clk_bufs
    BUFG clk_10_bufg (
      .I (clk_10_unbuf),
      .O (clk_10_buf)
    );

    BUFG clk_48_bufg (
      .I (clk_48_unbuf),
      .O (clk_48_buf)
    );
  end else begin : gen_no_clk_bufs
    // BUFGs added by downstream modules, no need to add here
    assign clk_10_buf = clk_10_unbuf;
    assign clk_48_buf = clk_48_unbuf;
  end

  // outputs
  // clock
  assign clk_main = clk_10_buf;
  assign clk_48MHz = clk_48_buf;
  assign clk_aon = clk_aon_buf;

  // reset
  assign rst_n = locked_pll & io_rst_buf_n & jtag_srst_n;
endmodule
