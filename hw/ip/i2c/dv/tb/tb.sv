// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import i2c_env_pkg::*;
  import i2c_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk_i, rst_ni;
  wire devmode;
  wire intr_fmt_watermark;
  wire intr_rx_watermark;
  wire intr_fmt_overflow;
  wire intr_rx_overflow;
  wire intr_nak;
  wire intr_scl_interference;
  wire intr_sda_interference;
  wire intr_stretch_timeout;
  wire intr_sda_unstable;
  wire intr_trans_complete;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  wire cio_scl_i;
  wire cio_sda_i;
  wire cio_scl_o;
  wire cio_sda_o;
  wire cio_scl_en_o;
  wire cio_sda_en_o;

  // interfaces
  clk_rst_if clk_rst_if (
      .clk  (clk_i),
      .rst_n(rst_ni)
  );
  pins_if #(NUM_MAX_INTERRUPTS) intr_if (interrupts);
  pins_if #(1) devmode_if (devmode);

  tl_if tl_if (
      .clk  (clk_i),
      .rst_n(rst_ni)
  );
  i2c_if i2c_if ();

  // dut
  i2c dut (
      .clk_i (clk_i),
      .rst_ni(rst_ni),

      .tl_i(tl_if.h2d),
      .tl_o(tl_if.d2h),

      .cio_scl_i   (cio_scl_i),
      .cio_scl_o   (cio_scl_o),
      .cio_scl_en_o(cio_scl_en_o),
      .cio_sda_i   (cio_sda_i),
      .cio_sda_o   (cio_sda_o),
      .cio_sda_en_o(cio_sda_en_o),

      .intr_fmt_watermark_o   (intr_fmt_watermark),
      .intr_rx_watermark_o    (intr_rx_watermark),
      .intr_fmt_overflow_o    (intr_fmt_overflow),
      .intr_rx_overflow_o     (intr_rx_overflow),
      .intr_nak_o             (intr_nak),
      .intr_scl_interference_o(intr_scl_interference),
      .intr_sda_interference_o(intr_sda_interference),
      .intr_stretch_timeout_o (intr_stretch_timeout),
      .intr_sda_unstable_o    (intr_sda_unstable),
      .intr_trans_complete_o  (intr_trans_complete)
  );

  // virtual open drain
  assign i2c_if.scl_i = (cio_scl_en_o) ? cio_scl_o : ~cio_scl_o;
  assign i2c_if.sda_i = (cio_sda_en_o) ? cio_sda_o : ~cio_sda_o;
  assign cio_scl_i = i2c_if.scl_o;
  assign cio_sda_i = i2c_if.sda_o;

  // host -> device if
  assign i2c_if.clk_i = clk_i;
  assign i2c_if.rst_ni = rst_ni;

  // interrupt
  assign interrupts[FmtWatermark] = intr_fmt_watermark;
  assign interrupts[RxWatermark] = intr_rx_watermark;
  assign interrupts[FmtOverflow] = intr_fmt_overflow;
  assign interrupts[RxOverflow] = intr_rx_overflow;
  assign interrupts[Nak] = intr_nak;
  assign interrupts[SclInference] = intr_scl_interference;
  assign interrupts[SdaInference] = intr_sda_interference;
  assign interrupts[StretchTimeout] = intr_stretch_timeout;
  assign interrupts[SdaUnstable] = intr_sda_unstable;
  assign interrupts[TransComplete] = intr_trans_complete;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual i2c_if)::set(null, "*.env.m_i2c_agent*", "vif", i2c_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule : tb
