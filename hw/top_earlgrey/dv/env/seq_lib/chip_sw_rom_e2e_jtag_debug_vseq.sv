// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_rom_e2e_jtag_debug_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_rom_e2e_jtag_debug_vseq)
  `uvm_object_new

  virtual task pre_start();
    cfg.chip_vif.tap_straps_if.drive(JtagTapRvDm);
    super.pre_start();
  endtask

  virtual task body();
    string elf_file = {cfg.sw_images[SwTypeRom], ".elf"};
    string uart_msg_via_mem_access = "OK!";
    string uart_msg_via_call = "GDB-OK!";
    string uart_msg_received;
    breakpoint_t breakpoints[$];
    byte status;

    super.body();
    cfg.sw_test_status_vif.can_pass_only_in_test = 0;

    // The steps in this test closely follow the gdb steps, which are encoded
    // in a host-side (Rust) test harness located at
    // sw/host/tests/rom/e2e_openocd_debug_test/src/main.rs

    // Halt the CPU before the first instruction is executed. The chip just came out of POR - so
    // there is no need to issue an NDM reset again. Just wait for lc_ready signal and immediately
    // issue a halt req.
    cfg.debugger.set_elf_file(elf_file);
    `DV_WAIT(cfg.chip_vif.pinmux_lc_hw_debug_en)
    cfg.chip_vif.aon_clk_por_rst_if.wait_clks(1);
    cfg.debugger.set_dmactive(1);
    cfg.debugger.set_haltreq(1);
    cfg.debugger.wait_cpu_halted();
    cfg.debugger.set_haltreq(0);

    // Verify that we are in ROM's reset vector.
    begin
      bit result;
      longint unsigned addr, size;
      result = dv_utils_pkg::sw_symbol_get_addr_size(.elf_file(elf_file),
          .symbol("_rom_interrupt_vector_asm"), .does_not_exist_ok(0), .addr(addr), .size(size));
      `DV_CHECK(result)
      addr += 32 * 4;  // 33rd entry in the reset vector.
      `uvm_info(`gfn, $sformatf("CPU reset vector: 0x%0h", addr), UVM_LOW)
      cfg.debugger.check_pc(.exp_addr(addr));
    end

    // Single step and verify we are in `_rom_start_boot` (this is where the reset vector jumps to).
    cfg.debugger.step();
    cfg.debugger.check_pc(.exp_symbol("_rom_start_boot"));
    cfg.debugger.check_debug_cause(jtag_rv_debugger_pkg::RvDebugCauseStep);

    cfg.debugger.info_breakpoints(breakpoints);
    `DV_CHECK(breakpoints.size() == 0)

    `uvm_info(`gfn, "Run until we check whether ROM execution is enabled", UVM_LOW)
    cfg.debugger.add_breakpoint(.symbol("kRomStartBootMaybeHalt"));
    cfg.debugger.continue_execution();
    cfg.chip_vif.cpu_clk_rst_if.wait_clks(200);
    cfg.debugger.wait_cpu_halted();
    cfg.debugger.check_pc(.exp_symbol("kRomStartBootMaybeHalt"));
    cfg.debugger.check_debug_cause(jtag_rv_debugger_pkg::RvDebugCauseTrigger);

    `uvm_info(`gfn, "Set all but one available breakpoints", UVM_LOW)
    cfg.debugger.add_breakpoint(.symbol("rom_main"));
    cfg.debugger.add_breakpoint(.symbol("uart_init"));
    cfg.debugger.info_breakpoints(breakpoints);
    `DV_CHECK(breakpoints.size() == 3)

    `uvm_info(`gfn, "Pretend execution is enabled", UVM_LOW)
    cfg.debugger.write_pc(.symbol("kRomStartBootExecEn"));

    `uvm_info(`gfn, "Continue until watchdog config", UVM_LOW)
    cfg.debugger.add_breakpoint(.symbol("kRomStartWatchdogEnabled"));
    cfg.debugger.info_breakpoints(breakpoints);
    `DV_CHECK(breakpoints.size() == 4)
    cfg.debugger.continue_execution();
    cfg.chip_vif.cpu_clk_rst_if.wait_clks(200);
    cfg.debugger.wait_cpu_halted();
    cfg.debugger.check_pc(.exp_symbol("kRomStartWatchdogEnabled"));
    cfg.debugger.check_debug_cause(jtag_rv_debugger_pkg::RvDebugCauseTrigger);

    `uvm_info(`gfn, "Disable watchdog config", UVM_LOW)
    cfg.debugger.mem_write(.addr(ral.aon_timer_aon.wdog_ctrl.get_address()),
                           .value_q({0}),
                           .status(status));
    `DV_CHECK_EQ(status, 0)
    cfg.debugger.delete_breakpoint(.index(3));
    cfg.debugger.info_breakpoints(breakpoints);
    `DV_CHECK(breakpoints.size() == 3)

    `uvm_info(`gfn, "Continue until rom_main", UVM_LOW)
    cfg.debugger.continue_execution();
    cfg.chip_vif.cpu_clk_rst_if.wait_clks(200);
    cfg.debugger.wait_cpu_halted();
    cfg.debugger.check_pc(.exp_symbol("rom_main"));
    cfg.debugger.check_debug_cause(jtag_rv_debugger_pkg::RvDebugCauseTrigger);

    `uvm_info(`gfn, "Continue until uart_init", UVM_LOW)
    cfg.debugger.continue_execution();
    cfg.chip_vif.cpu_clk_rst_if.wait_clks(200);
    cfg.debugger.wait_cpu_halted();
    cfg.debugger.check_pc(.exp_symbol("uart_init"));
    cfg.debugger.check_debug_cause(jtag_rv_debugger_pkg::RvDebugCauseTrigger);
    cfg.debugger.finish();
    configure_uart_agent(.uart_idx(ROM_CONSOLE_UART), .enable(1));
    fork get_uart_tx_items(ROM_CONSOLE_UART); join_none

    `uvm_info(`gfn, "Read and write GPRs and selected CPU CSRs", UVM_LOW)
    test_cpu_gprs_csrs_access();

    `uvm_info(`gfn, "Read and write memory (both SRAM and device)", UVM_LOW)
    test_chip_mem_access();

    `uvm_info(`gfn, "Manually write bytes to UART0", UVM_LOW)
    foreach (uart_msg_via_mem_access[i]) begin
      cfg.debugger.mem_write(.addr(ral.uart0.wdata.get_address()),
                             .value_q({BUS_DW'(uart_msg_via_mem_access[i])}),
                             .status(status));
      `DV_CHECK_EQ(status, 0)
    end

    `uvm_info(`gfn, "Execute code from GDB with `call` command", UVM_LOW)
    foreach (uart_msg_via_call[i]) begin
      cfg.debugger.call(.symbol("uart_putchar"), .args({BUS_DW'(uart_msg_via_call[i])}));
    end

    `uvm_info(`gfn, "Verify UART messages received over the TX port", UVM_LOW)
    configure_uart_agent(.uart_idx(ROM_CONSOLE_UART), .enable(0));
    `DV_WAIT(uart_tx_data_q.size() == (uart_msg_via_mem_access.len() + uart_msg_via_call.len()))
    uart_msg_received = {>>{uart_tx_data_q}};
    `DV_CHECK_STREQ(uart_msg_received, {uart_msg_via_mem_access, uart_msg_via_call})

    `uvm_info(`gfn, "Have the CPU write pass pattern", UVM_LOW)
    cfg.debugger.mem_write(.addr(SW_DV_TEST_STATUS_ADDR),
                           .value_q({sw_test_status_pkg::SwTestStatusPassed}),
                           .status(status));
    `DV_CHECK_EQ(status, 0)

    `uvm_info(`gfn, "Silence the CPU by jumping to boot halted loop", UVM_LOW)
    cfg.debugger.write_pc(.symbol("kRomStartBootHalted"));
    cfg.debugger.continue_execution();
  endtask

  // Write-read check CPU GPRs and CSRs.
  //
  // Save and restore original values at the end, since it may corrupt the flow of execution.
  task test_cpu_gprs_csrs_access();
    logic [BUS_DW-1:0] orig_data[jtag_rv_debugger_pkg::abstract_cmd_regno_t];
    logic [BUS_DW-1:0] new_data[jtag_rv_debugger_pkg::abstract_cmd_regno_t];
    jtag_rv_debugger_pkg::abstract_cmd_err_e status;
    jtag_rv_debugger_pkg::abstract_cmd_regno_t csrs[$] = '{
      // Hand-picked CSRs that are RW.
      jtag_rv_debugger_pkg::RvCoreCsrDScratch0,
      jtag_rv_debugger_pkg::RvCoreCsrDScratch1,
      ibex_pkg::CSR_MSCRATCH,
      ibex_pkg::CSR_MCYCLEH,
      ibex_pkg::CSR_MINSTRETH
    };

    // Add the X1-X31 GPRs starting at RA. Skip S0 and A0 since it is actively used by the CPU.
    for (jtag_rv_debugger_pkg::abstract_cmd_regno_t gpr = jtag_rv_debugger_pkg::RvCoreCsrGprRa;
         gpr <= jtag_rv_debugger_pkg::RvCoreCsrGprT6;
         gpr++) begin
      if (gpr inside {jtag_rv_debugger_pkg::RvCoreCsrGprS0,
                      jtag_rv_debugger_pkg::RvCoreCsrGprA0}) continue;
      csrs.push_back(gpr);
    end
    `uvm_info(`gfn, $sformatf("Testing CPU registers:\n%p", csrs), UVM_MEDIUM)

    // Read original CSR values.
    csrs.shuffle();
    foreach (csrs[i]) begin
      logic [BUS_DW-1:0] value_q[$];
      cfg.debugger.abstract_cmd_reg_read(.regno(csrs[i]), .value_q(value_q), .status(status));
      `DV_CHECK_EQ(status, jtag_rv_debugger_pkg::AbstractCmdErrNone)
      orig_data[csrs[i]] = value_q[0];
    end

    // Write new random values.
    csrs.shuffle();
    foreach (csrs[i]) begin
      logic [BUS_DW-1:0] data;
      `DV_CHECK_STD_RANDOMIZE_FATAL(data)
      cfg.debugger.abstract_cmd_reg_write(.regno(csrs[i]), .value_q({data}), .status(status));
      `DV_CHECK_EQ(status, jtag_rv_debugger_pkg::AbstractCmdErrNone)
      new_data[csrs[i]] = data;
    end

    // Read CSRs and verify new values.
    csrs.shuffle();
    foreach (csrs[i]) begin
      logic [BUS_DW-1:0] value_q[$];
      cfg.debugger.abstract_cmd_reg_read(.regno(csrs[i]), .value_q(value_q), .status(status));
      `DV_CHECK_EQ(status, jtag_rv_debugger_pkg::AbstractCmdErrNone)
      `DV_CHECK_EQ(value_q[0], new_data[csrs[i]], $sformatf("for CSR 0x%0h", csrs[i]))
    end

    // Restore original values.
    csrs.shuffle();
    foreach (csrs[i]) begin
      cfg.debugger.abstract_cmd_reg_write(.regno(csrs[i]), .value_q({orig_data[csrs[i]]}),
                                          .status(status));
      `DV_CHECK_EQ(status, jtag_rv_debugger_pkg::AbstractCmdErrNone)
    end

    // Read CSRs and verify restored values.
    csrs.shuffle();
    foreach (csrs[i]) begin
      logic [BUS_DW-1:0] value_q[$];
      cfg.debugger.abstract_cmd_reg_read(.regno(csrs[i]), .value_q(value_q), .status(status));
      `DV_CHECK_EQ(status, jtag_rv_debugger_pkg::AbstractCmdErrNone)
      `DV_CHECK_EQ(value_q[0], orig_data[csrs[i]], $sformatf("for CSR 0x%0h", csrs[i]))
    end
  endtask

  // Write-read check the SRAM main and ret memories.
  //
  // Since we have taken full control of the CPU execution using the debugger, it is not necessary
  // to save and restore the SRAM addresses we write to as a part of this task.
  task test_chip_mem_access();
    byte status;
    logic [BUS_DW-1:0] test_addrs[$];
    logic [BUS_DW-1:0] test_data[$];
    addr_range_t sram_main = '{
        start_addr: top_earlgrey_pkg::TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR,
        end_addr: top_earlgrey_pkg::TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR +
                  top_earlgrey_pkg::TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_SIZE_BYTES - 1

    };
    addr_range_t sram_ret = '{
        start_addr: top_earlgrey_pkg::TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR,
        end_addr: top_earlgrey_pkg::TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR +
                  top_earlgrey_pkg::TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES - 1

    };

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(test_addrs,
        test_addrs.size() inside {[5:20]};
        foreach (test_addrs[i]) {
          test_addrs[i] inside {[sram_main.start_addr:sram_main.end_addr]} ||
          test_addrs[i] inside {[sram_ret.start_addr:sram_ret.end_addr]};
          test_addrs[i][1:0] == '0;
        }
    )
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(test_data, test_data.size() == test_addrs.size();)
    foreach (test_addrs[i]) begin
      logic [BUS_DW-1:0] value_q[$];
      cfg.debugger.mem_write(.addr(test_addrs[i]), .value_q({test_data[i]}), .status(status));
      `DV_CHECK_EQ(status, 0)
    end
    foreach (test_addrs[i]) begin
      logic [BUS_DW-1:0] value_q[$];
      cfg.debugger.mem_read(.addr(test_addrs[i]), .value_q(value_q), .status(status));
      `DV_CHECK_EQ(status, 0)
      `DV_CHECK_EQ(value_q[0], test_data[i], $sformatf("for addr 0x%0h", test_addrs[i]))
    end
  endtask

endclass
