// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_uart_tx_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_uart_tx_vseq)
  `uvm_object_new

  virtual task connect_uart_agent(uint uart_idx = 0);
      `uvm_info(`gfn, $sformatf("Configuring and connecting UART agent to UART %0d ...", uart_idx),
        UVM_LOW)
      cfg.m_uart_agent_cfgs[uart_idx].set_parity(1'b0, 1'b0);
      cfg.m_uart_agent_cfgs[uart_idx].set_baud_rate(cfg.uart_baud_rate);
      cfg.m_uart_agent_cfgs[uart_idx].en_tx_monitor = 1;
      cfg.chip_vif.enable_uart(uart_idx, 1);
  endtask

  virtual task disconnect_uart_agent(uint uart_idx = 0);
      `uvm_info(`gfn, $sformatf("Disconnecting UART agent from UART %0d ...", uart_idx),
        UVM_LOW)
      cfg.chip_vif.enable_uart(uart_idx, 0);
      cfg.m_uart_agent_cfgs[uart_idx].en_tx_monitor = 0;
  endtask

  virtual task body();
    super.body();

    fork
      get_uart_tx_items();
    join_none

    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    connect_uart_agent();
  endtask

  virtual task post_start();
    super.post_start();
    disconnect_uart_agent();
  endtask
endclass
