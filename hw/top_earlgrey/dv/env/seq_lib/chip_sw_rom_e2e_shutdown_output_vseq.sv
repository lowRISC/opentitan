// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_rom_e2e_shutdown_output_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_rom_e2e_shutdown_output_vseq)
  `uvm_object_new

  localparam uint UART0_IDX = 0;
  localparam string SRAM_INIT_DONE_HDL_PATH =
    "tb.dut.top_earlgrey.u_sram_ctrl_ret_aon.u_reg_regs.status_init_done_qs";

  event sram_init_done_event;

  // This matches the expected values in `sw/device/silicon_creator/rom/e2e/BUILD`. Note,
  // SystemVerilog does not support "\r" carriage return in a string literal, so we use the hex code
  // of "\x0d" instead. Also note, this cannot be a localparam as it turns out, our SV compiler
  // does not seem to have any knowledge of `lc_state_e` enum at the time when it is processing
  // localparams.
  string exp_boot_fault_msgs[lc_ctrl_state_pkg::lc_state_e] = '{
      lc_ctrl_state_pkg::LcStTestUnlocked0: "BFV:0142500d\x0d\nLCV:02108421\x0d\n",
      lc_ctrl_state_pkg::LcStDev:           "BFV:0142500d\x0d\nLCV:21084210\x0d\n",
      lc_ctrl_state_pkg::LcStProd:          "BFV:0142500d\x0d\nLCV:2318c631\x0d\n",
      lc_ctrl_state_pkg::LcStProdEnd:       "BFV:0142500d\x0d\nLCV:25294a52\x0d\n",
      lc_ctrl_state_pkg::LcStRma:           "BFV:0142500d\x0d\nLCV:2739ce73\x0d\n"};

  virtual task check_hdl_paths();
    int retval;
    retval = uvm_hdl_check_path(SRAM_INIT_DONE_HDL_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", SRAM_INIT_DONE_HDL_PATH))
  endtask

  virtual task wait_for_sram_init_done();
    int retval;
    bit sram_init_done;
    bit sram_init_done_prev;
    forever begin
      sram_init_done_prev = sram_init_done;
      retval = uvm_hdl_read(SRAM_INIT_DONE_HDL_PATH, sram_init_done);
      `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", SRAM_INIT_DONE_HDL_PATH))
      if (sram_init_done_prev == 0 && sram_init_done == 1) begin
        ->sram_init_done_event;
      end
      cfg.clk_rst_vif.wait_clks(1);
    end
  endtask

  virtual task body();
    check_hdl_paths();
    super.body();

    fork
      wait_for_sram_init_done();
      get_uart_tx_items(UART0_IDX);
    join_none

    foreach (exp_boot_fault_msgs[lc_state]) begin
      `uvm_info(`gfn, $sformatf("Backdoor overwriting the lifecycle state and applying POR ..."),
        UVM_LOW)
      cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(lc_state);
      apply_reset();

      // Wait for SRAM initialization to be done before hooking up the UART agent to prevent
      // X's propagating as a result of multiple drivers on pins IOC3 and IOC4 (due to DFT strap
      // sampling in TestUnlocked* and RMA lifecycel states).
      `DV_WAIT(sram_init_done_event.triggered)

      // Clean out the UART FIFO.
      `uvm_info(`gfn, $sformatf("UART TX queue (before):"), UVM_LOW)
      uart_tx_data_q.delete();

      `uvm_info(`gfn, $sformatf("Configuring and connecting UART agent to UART0 ..."), UVM_LOW)
      cfg.m_uart_agent_cfgs[UART0_IDX].set_parity(1'b0, 1'b0);
      cfg.m_uart_agent_cfgs[UART0_IDX].set_baud_rate(cfg.uart_baud_rate);
      cfg.m_uart_agent_cfgs[UART0_IDX].en_tx_monitor = 1;
      cfg.m_uart_agent_cfgs[UART0_IDX].en_rx_monitor = 1;
      cfg.chip_vif.enable_uart(UART0_IDX, 1);

      // Wait until we receive the expected boot fault message length of bytes over UART0.
      `DV_WAIT(uart_tx_data_q.size() == exp_boot_fault_msgs[lc_state].len())
      `uvm_info(`gfn, "Checking the UART TX data matches expected boot fault msg ...", UVM_LOW)
      foreach (uart_tx_data_q[i]) begin
        `DV_CHECK_EQ(uart_tx_data_q[i], exp_boot_fault_msgs[lc_state][i],
          $sformatf("UART TX byte \"%s\" at index %d does not match \"%s\"",
            i, uart_tx_data_q[i], exp_boot_fault_msgs[lc_state][i]))
      end

      // Disconnect the UART interface before POR_N to avoid multiple driver issue on UART pins.
      cfg.chip_vif.enable_uart(UART0_IDX, 0);
      cfg.m_uart_agent_cfgs[UART0_IDX].en_tx_monitor = 0;
      cfg.m_uart_agent_cfgs[UART0_IDX].en_rx_monitor = 0;
    end

    // Test passed.
    override_test_status_and_finish(.passed(1'b1));
  endtask

endclass : chip_sw_rom_e2e_shutdown_output_vseq
