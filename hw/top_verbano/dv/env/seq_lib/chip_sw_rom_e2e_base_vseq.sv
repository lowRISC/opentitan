// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_rom_e2e_base_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_rom_e2e_base_vseq)
  `uvm_object_new

  virtual task connect_rom_uart_agent(uint uart_idx = ROM_CONSOLE_UART);
      `uvm_info(`gfn, $sformatf("Configuring and connecting UART agent to UART %0d ...", uart_idx),
        UVM_LOW)
      cfg.m_uart_agent_cfgs[uart_idx].set_parity(1'b0, 1'b0);
      cfg.m_uart_agent_cfgs[uart_idx].set_baud_rate(cfg.uart_baud_rate);
      cfg.m_uart_agent_cfgs[uart_idx].en_tx_monitor = 1;
      cfg.chip_vif.enable_uart(uart_idx, 1);
  endtask

  virtual task disconnect_rom_uart_agent(uint uart_idx = ROM_CONSOLE_UART);
      `uvm_info(`gfn, $sformatf("Disconnecting UART agent from UART %0d ...", uart_idx),
        UVM_LOW)
      cfg.chip_vif.enable_uart(uart_idx, 0);
      cfg.m_uart_agent_cfgs[uart_idx].en_tx_monitor = 0;
  endtask

  // Note: this task deletes the contents of the UART TX buffer.
  virtual task check_uart_output_msg(string exp_msg, uint uart_idx = ROM_CONSOLE_UART);
    string actual_msg;
    uart_tx_data_q.delete();

    // Wait until we receive the expected boot fault message length of bytes over UART0.
    `DV_WAIT(uart_tx_data_q.size() == exp_msg.len(),
      "Timeout waiting for UART FIFO to fill.", 200_000_000)
    `uvm_info(`gfn,
      $sformatf("Checking UART TX data matches '%s'...", exp_msg),
      UVM_LOW);
    actual_msg = {>>{uart_tx_data_q}};
    `DV_CHECK_STREQ(actual_msg, exp_msg)
  endtask

  virtual task rom_e2e_test_boot_fault_success(uint uart_idx = ROM_CONSOLE_UART);
    // ROM E2E tests that boot fault generate an alert that must be silenced before ending the test.
    apply_reset();
    override_test_status_and_finish(.passed(1'b1));
  endtask

  virtual task body();
    super.body();

    fork
      get_uart_tx_items(ROM_CONSOLE_UART);
    join_none

    // Wait for retention SRAM initialization to be done before hooking up the UART agent to
    // prevent X's propagating as a result of multiple drivers on pins IOC3 and IOC4 (due to DFT
    // strap sampling in TestUnlocked* and RMA lifecycle states). Once the retention SRAM is
    // initialized, we have made it to `rom_main()`.
    `DV_WAIT(cfg.chip_vif.sram_ret_init_done == 1,
             $sformatf({"Timeout occurred when waiting for SRAM initialization; ",
                        "Current sram_ret_init_done = 1'%0b, Timeout value = %0dns"},
                        cfg.chip_vif.sram_ret_init_done,
                        cfg.sw_test_timeout_ns),
             cfg.sw_test_timeout_ns)
  endtask

endclass : chip_sw_rom_e2e_base_vseq
