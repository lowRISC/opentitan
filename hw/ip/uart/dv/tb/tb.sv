// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import tl_agent_pkg::*;
  import uart_env_pkg::*;
  import uart_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode;
  wire intr_tx_watermark;
  wire intr_rx_watermark;
  wire intr_tx_overflow;
  wire intr_rx_overflow;
  wire intr_rx_frame_err;
  wire intr_rx_break_err;
  wire intr_rx_timeout;
  wire intr_rx_parity_err;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if #(1) devmode_if(devmode);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  uart_if uart_if();

  // dut
  uart dut (
    .clk_i                (clk        ),
    .rst_ni               (rst_n      ),

    .tl_i                 (tl_if.h2d  ),
    .tl_o                 (tl_if.d2h  ),

    .cio_rx_i             (uart_if.uart_rx    ),
    .cio_tx_o             (uart_if.uart_tx    ),
    .cio_tx_en_o          (uart_if.uart_tx_en ),

    .intr_tx_watermark_o  (intr_tx_watermark ),
    .intr_rx_watermark_o  (intr_rx_watermark ),
    .intr_tx_overflow_o   (intr_tx_overflow  ),
    .intr_rx_overflow_o   (intr_rx_overflow  ),
    .intr_rx_frame_err_o  (intr_rx_frame_err ),
    .intr_rx_break_err_o  (intr_rx_break_err ),
    .intr_rx_timeout_o    (intr_rx_timeout   ),
    .intr_rx_parity_err_o (intr_rx_parity_err)
  );

  assign interrupts[TxWatermark] = intr_tx_watermark;
  assign interrupts[RxWatermark] = intr_rx_watermark;
  assign interrupts[TxOverflow]  = intr_tx_overflow;
  assign interrupts[RxOverflow]  = intr_rx_overflow;
  assign interrupts[RxFrameErr]  = intr_rx_frame_err;
  assign interrupts[RxBreakErr]  = intr_rx_break_err;
  assign interrupts[RxTimeout]   = intr_rx_timeout;
  assign interrupts[RxParityErr] = intr_rx_parity_err;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(tlul_assert_ctrl_vif)::set(null, "*.env", "tlul_assert_ctrl_vif",
        dut.tlul_assert_device.tlul_assert_ctrl_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual uart_if)::set(null, "*.env.m_uart_agent*", "vif", uart_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
