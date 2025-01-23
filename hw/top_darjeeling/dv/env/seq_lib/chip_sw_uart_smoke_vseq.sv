// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_uart_smoke_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_uart_smoke_vseq)

  `uvm_object_new

  rand int uart_idx;

  constraint uart_idx_c {
    uart_idx inside {[0:NUM_UARTS-1]};
  }

  // The smoke test only uses UART0, but it may change in future. Disable this constraint in
  // extended classes.
  constraint uart_idx_smoke_c {
    uart_idx == 0;
  }

  virtual task body();
    super.body();
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest);
    configure_uart_agent(.uart_idx(uart_idx), .enable(1), .enable_rx_monitor(1));
  endtask

  virtual task post_start();
    super.post_start();
    // Disconnect the UART interface.
    cfg.m_uart_agent_cfgs[uart_idx].en_tx_monitor = 0;
    cfg.m_uart_agent_cfgs[uart_idx].en_rx_monitor = 0;
    // TODO: The SW test needs to release the pinmux to UART connection before we can disconnect the
    // UART interface from the chip IOs. Not doing so will result in X-prop.
    // configure_uart_agent(.uart_idx(uart_idx), .enable(0));
    // cfg.chip_vif.enable_uart(uart_idx, 0);
  endtask

endclass : chip_sw_uart_smoke_vseq
