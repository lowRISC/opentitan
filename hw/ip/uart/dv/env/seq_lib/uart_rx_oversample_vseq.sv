// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test reg uart.VAL
// 1. find the center of oversampled clock
// 2. drive 16 bits on RX pin based on 16x oversampled clk, then check the reg value
class uart_rx_oversample_vseq extends uart_tx_rx_vseq;
  `uvm_object_utils(uart_rx_oversample_vseq)
  uint num_bits;

  constraint en_rx_c {
    en_rx == 1;
  }

  // lower the freq so that there is enough time to read rx oversmapled value and check
  constraint baud_rate_extra_c {
    baud_rate <= BaudRate115200;
  }

  `uvm_object_new

  task body();
    int uart_xfer_bits;
    num_bits = ral.val.rx.get_n_bits();
    cfg.m_uart_agent_cfg.en_rx_monitor = 0;
    for (int i = 1; i <= num_trans; i++) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
      uart_init();

      find_oversampled_clk_center();
      // don't use big number here, the way TB measures cycle isn't the same as DUT
      // need to re-sync again after cerntain cycles
      repeat ($urandom_range(1, 3)) begin
        drive_rx_oversampled_val();
      end
      `uvm_info(`gfn, $sformatf("finished run %0d/%0d", i, num_trans), UVM_LOW)
    end

    // wait for a full uart transaction time to flush out the remaining rx transaction
    uart_xfer_bits = NUM_UART_XFER_BITS_WO_PARITY + cfg.m_uart_agent_cfg.en_parity;
    #(cfg.m_uart_agent_cfg.vif.uart_clk_period_ns * uart_xfer_bits);

    cfg.m_uart_agent_cfg.en_rx_monitor = 1;
    clear_fifos(.clear_rx_fifo(1), .clear_tx_fifo(0));
    // clear all interrupts as the driving of rx value in seq may trigger interrupt that scb
    // doesn't expect
    csr_wr(.ptr(ral.intr_state), .value('1));
  endtask : body

  // find the center of oversampled clk
  // 1. drive all 0s/1s and keep reading reg for the pattern w/o any delay
  // 2. after find the pattern, flip pattern[0] and keep polling reg for 0x0001/0xfffe
  // 3. after find it, then we know we're close to the edge of the clk
  // 4. Delay 0.4 * oversample_clk_period to get to the center of the clk
  virtual task find_oversampled_clk_center();
    bit [TL_DW-1:0] pattern;
    `uvm_info(`gfn, "finding oversample clk center", UVM_HIGH)
    randcase
      1: pattern = (1 << num_bits) - 1; // all 1s
      1: pattern = 0;
    endcase
    // drive constant value and find all 1s/0s pattern
    cfg.m_uart_agent_cfg.vif.uart_rx = pattern[0];
    csr_spinwait(.ptr(ral.val.rx), .exp_data(pattern));
    // flip a bit and find the clk edge
    pattern[0] = ~pattern[0];
    cfg.m_uart_agent_cfg.vif.uart_rx = pattern[0];
    csr_spinwait(.ptr(ral.val.rx), .exp_data(pattern));
    // move 0.4 clk into the clk center, as previous reg read consume some cycles
    #(get_oversampled_baud_clk_period_ns() *1ns * 0.4);
  endtask

  // drive N bits on RX pin based on oversampled clk, then check the reg value
  virtual task drive_rx_oversampled_val();
    bit [TL_DW-1:0] data;
    `uvm_info(`gfn, "Start drive rx oversampled value", UVM_HIGH)

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(data,
                                       data <= ((1 << num_bits) - 1);)
    // Most recent bit is bit 0
    for (int i = num_bits - 1; i >= 0; i--) begin
      cfg.m_uart_agent_cfg.vif.uart_rx = data[i];
      #(get_oversampled_baud_clk_period_ns() * 1ns);
    end
    cfg.m_uart_agent_cfg.vif.uart_rx = 1; // back to default value
    csr_rd_check(.ptr(ral.val.rx), .compare_value(data), .blocking(0));
  endtask

  virtual function real get_oversampled_baud_clk_period_ns();
    return cfg.m_uart_agent_cfg.vif.uart_clk_period_ns / num_bits;
  endfunction

endclass : uart_rx_oversample_vseq
