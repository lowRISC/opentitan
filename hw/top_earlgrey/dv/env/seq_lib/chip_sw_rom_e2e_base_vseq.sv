// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_rom_e2e_base_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_rom_e2e_base_vseq)
  `uvm_object_new

  string lc_state_2_rom_lcv[lc_ctrl_state_pkg::lc_state_e] = '{
      lc_ctrl_state_pkg::LcStTestUnlocked0: ROM_LCV_TEST_UNLOCKED0,
      lc_ctrl_state_pkg::LcStDev: ROM_LCV_DEV,
      lc_ctrl_state_pkg::LcStProd: ROM_LCV_PROD,
      lc_ctrl_state_pkg::LcStProdEnd: ROM_LCV_PROD_END,
      lc_ctrl_state_pkg::LcStRma: ROM_LCV_RMA};

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
    uart_tx_data_q.delete();

    // Wait until we receive the expected boot fault message length of bytes over UART0.
    `DV_WAIT(uart_tx_data_q.size() == exp_msg.len(),
      "Timeout waiting for UART FIFO to fill.", 200_000_000)
    `uvm_info(`gfn, "Checking the UART TX data matches expected boot fault msg ...", UVM_LOW)
    foreach (uart_tx_data_q[i]) begin
      `DV_CHECK_EQ(uart_tx_data_q[i], exp_msg[i],
        $sformatf("UART TX byte \"%s\" at index %d does not match \"%s\"",
          i, uart_tx_data_q[i], exp_msg[i]))
    end
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
    `DV_WAIT(cfg.chip_vif.sram_ret_init_done == 1)
  endtask

endclass : chip_sw_rom_e2e_base_vseq
