// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module clkgen_xil7series #(
    // Add BUFG if not done by downstream logic
    parameter bit AddClkBuf = 1
) (
    input  IO_CLK,
    input  IO_RST_N,
    output clk_sys,
    output clk_48MHz,
    output rst_sys_n
);
  logic locked_pll;
  logic io_clk_buf;
  logic clk_50_buf;
  logic clk_50_unbuf;
  logic clk_fb_buf;
  logic clk_fb_unbuf;
  logic clk_48_buf;
  logic clk_48_unbuf;

  // input buffer
  IBUF io_clk_ibuf (
      .I(IO_CLK),
      .O(io_clk_buf)
  );

  PLLE2_ADV #(
      .BANDWIDTH("OPTIMIZED"),
      .COMPENSATION("ZHOLD"),
      .STARTUP_WAIT("FALSE"),
      .DIVCLK_DIVIDE(1),
      .CLKFBOUT_MULT(12),
      .CLKFBOUT_PHASE(0.000),
      .CLKOUT0_DIVIDE(24),
      .CLKOUT0_PHASE(0.000),
      .CLKOUT0_DUTY_CYCLE(0.500),
      .CLKOUT1_DIVIDE(25),
      .CLKOUT1_PHASE(0.000),
      .CLKOUT1_DUTY_CYCLE(0.500),
      .CLKIN1_PERIOD(10.000)
  ) pll (
      .CLKFBOUT(clk_fb_unbuf),
      .CLKOUT0 (clk_50_unbuf),
      .CLKOUT1 (clk_48_unbuf),
      .CLKOUT2 (),
      .CLKOUT3 (),
      .CLKOUT4 (),
      .CLKOUT5 (),
      // Input clock control
      .CLKFBIN (clk_fb_buf),
      .CLKIN1  (io_clk_buf),
      .CLKIN2  (1'b0),
      // Tied to always select the primary input clock
      .CLKINSEL(1'b1),
      // Ports for dynamic reconfiguration
      .DADDR   (7'h0),
      .DCLK    (1'b0),
      .DEN     (1'b0),
      .DI      (16'h0),
      .DO      (),
      .DRDY    (),
      .DWE     (1'b0),
      // Other control and status signals
      .LOCKED  (locked_pll),
      .PWRDWN  (1'b0),
      // Do not reset PLL on external reset, otherwise ILA disconnects at a reset
      .RST     (1'b0)
  );

  // output buffering
  BUFG clk_fb_bufg (
      .I(clk_fb_unbuf),
      .O(clk_fb_buf)
  );

  if (AddClkBuf == 1) begin : gen_clk_bufs
    BUFG clk_50_bufg (
        .I(clk_50_unbuf),
        .O(clk_50_buf)
    );

    BUFG clk_48_bufg (
        .I(clk_48_unbuf),
        .O(clk_48_buf)
    );
  end else begin : gen_no_clk_bufs
    // BUFGs added by downstream modules, no need to add here
    assign clk_50_buf = clk_50_unbuf;
    assign clk_48_buf = clk_48_unbuf;
  end

  // outputs
  // clock
  assign clk_sys = clk_50_buf;  // TODO: choose 50 MHz clock as sysclock for now
  assign clk_48MHz = clk_48_buf;

  // reset
  assign rst_sys_n = locked_pll & IO_RST_N;
endmodule
