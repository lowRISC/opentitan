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
    configure_and_connect_uart(uart_idx);
  endtask

  // Configures the UART agent and connects uart_if to the chip IOs for the given instance.
  virtual function void configure_and_connect_uart(int instance_num);
    `DV_CHECK_FATAL(instance_num inside {[0:NUM_UARTS-1]})
    `uvm_info(`gfn, $sformatf("Configuring and connecting UART%0d", instance_num), UVM_LOW)
    cfg.m_uart_agent_cfgs[instance_num].set_parity(1'b0, 1'b0);
    cfg.m_uart_agent_cfgs[instance_num].set_baud_rate(cfg.uart_baud_rate);
    cfg.chip_vif.enable_uart(instance_num, 1);
  endfunction

  virtual task post_start();
    super.post_start();
    // Disconnect the UART interface.
    cfg.chip_vif.enable_uart(uart_idx, 0);
  endtask

endclass : chip_sw_uart_smoke_vseq
