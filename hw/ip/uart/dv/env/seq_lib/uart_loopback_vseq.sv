// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test 2 kinds of loopback
// 1. system loopback, any outgoing bits to TX are received through RX
// 2. Line loopback, incoming bits (on RX) are forwarded to TX
class uart_loopback_vseq extends uart_tx_rx_vseq;
  `uvm_object_utils(uart_loopback_vseq)

  constraint en_tx_c {
    en_tx == 1;
  }

  constraint en_rx_c {
    en_rx == 1;
  }

  `uvm_object_new

  task body();
    for (int i = 1; i <= num_trans; i++) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
      uart_init();

      randcase
        1: drive_system_loopback();
        1: drive_line_loopback();
      endcase
      `uvm_info(`gfn, $sformatf("finished run %0d/%0d", i, num_trans), UVM_LOW)
    end
  endtask : body

  virtual task drive_system_loopback();
    byte unsigned tx_byte;
    `uvm_info(`gfn, "Start system loopback", UVM_HIGH)

    ral.ctrl.slpbk.set(1);
    csr_update(ral.ctrl);

    `DV_CHECK_STD_RANDOMIZE_FATAL(tx_byte)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_next_trans)
    cfg.clk_rst_vif.wait_clks(dly_to_next_trans);

    // drive tx data and expect to receive it rx fifo
    send_tx_byte(tx_byte);
    // wait for loopback to complete
    spinwait_txidle();
    spinwait_rxidle();
    csr_rd_check(.ptr(ral.rdata), .compare_value(tx_byte));
    // clear TxEmpty interrupt
    csr_wr(.ptr(ral.intr_state), .value(1 << TxEmpty));
    // check status is default value
    csr_rd_check(.ptr(ral.status), .compare_value(ral.status.get_reset()));

    ral.ctrl.slpbk.set(0);
    csr_update(ral.ctrl);
  endtask

  // when line loopback is enabled, RX data will be wired to TX w/o any synchronizer
  // drive RX with random data and random delay, and check same value at TX
  virtual task drive_line_loopback();
    `uvm_info(`gfn, "Start line loopback", UVM_HIGH)

    ral.ctrl.llpbk.set(1);
    csr_update(ral.ctrl);

    // disable monitor, as it can't handle these random data
    cfg.m_uart_agent_cfg.en_tx_monitor = 0;
    cfg.m_uart_agent_cfg.en_rx_monitor = 0;
    fork
      begin // isolation_fork
        fork
          // drive RX with random data and random delay
          repeat ($urandom_range(100, 1000)) begin
            cfg.m_uart_agent_cfg.vif.uart_rx = $urandom_range(0, 1);
            `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(dly_to_next_trans,
                                                  dly_to_next_trans > 0;)
            #(dly_to_next_trans * 1ns);
          end
          // RX has same value as TX without any synchronizer in the data path
          forever begin
            @(cfg.m_uart_agent_cfg.vif.uart_tx || cfg.m_uart_agent_cfg.vif.uart_rx);
            #1ps; // avoid race condition
            if (!cfg.under_reset) begin
              `DV_CHECK_EQ(cfg.m_uart_agent_cfg.vif.uart_tx, cfg.m_uart_agent_cfg.vif.uart_rx)
            end
          end
        join_any
        disable fork;
      end // isolation_fork
    join

    cfg.m_uart_agent_cfg.vif.uart_rx = 1; // back to default value
    cfg.m_uart_agent_cfg.en_tx_monitor = 1;
    cfg.m_uart_agent_cfg.en_rx_monitor = 1;

    // if noise filter is on, need 3 cycles delay to make sure internal rx value is 1, otherwise,
    // unexpected value (0) may be propagated to RX datapath
    if (en_noise_filter) cfg.clk_rst_vif.wait_clks(3);

    ral.ctrl.llpbk.set(0);
    csr_update(ral.ctrl);
  endtask

endclass : uart_loopback_vseq
