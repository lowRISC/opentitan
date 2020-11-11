// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test start bit length < 0.5 will be ignored
class uart_rx_start_bit_filter_vseq extends uart_smoke_vseq;
  `uvm_object_utils(uart_rx_start_bit_filter_vseq)

  `uvm_object_new

  // add noise before sending rx byte
  // when start bit is detected, design will check it again after 0.5 uart clock
  // if it's not low, consider it as glitch and ignore it
  virtual task send_rx_byte(byte data);
    uint64 uart_clk_period_ps = cfg.m_uart_agent_cfg.vif.uart_clk_period_ns * 1000;

    // monitor doesn't have start bit filter, need to disable it while driving filtered start bit
    cfg.m_uart_agent_cfg.en_rx_monitor = 0;
    repeat ($urandom_range(10, 100)) begin
      // drive 0 for up to 0.4 uart clk and 1 for 0.8 clk. Design samples start bit (0) first,
      // after 0.5 clk, design will sample 1 and should drop this start bit
      // need stable period > 0.5, use 0.8 clk to have enough margin
      cfg.m_uart_agent_cfg.vif.drive_uart_rx_glitch(
          .max_glitch_ps(uart_clk_period_ps * 0.4),
          .stable_ps_after_glitch(uart_clk_period_ps * 0.8));
    end
    cfg.m_uart_agent_cfg.en_rx_monitor = 1;
    csr_rd_check(.ptr(ral.status.rxidle), .compare_value(1));

    super.send_rx_byte(data);
  endtask

  // disable txidle check as it will also read rxidle which value is unexpected
  // during the long start bit glitch, rxidle will be low. mon/scb isn't supported
  // for checking this glitch for rxidle. Check it in test instead.
  virtual task spinwait_txidle();
  endtask

endclass : uart_rx_start_bit_filter_vseq
