// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_rom_e2e_jtag_inject_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_rom_e2e_jtag_inject_vseq)
  `uvm_object_new

  virtual task pre_start();
    cfg.chip_vif.tap_straps_if.drive(JtagTapRvDm);
    super.pre_start();
  endtask

  virtual task body();
    string elf_file = {cfg.sw_images[SwTypeDebug], ".elf"};
    logic [BUS_DW-1:0] value_q[$];
    jtag_rv_debugger_pkg::abstract_cmd_err_e abs_status;
    byte status;
    logic [BUS_AW-1:0] sram_program_sp, sram_program_gp, sram_program_start;

    super.body();

    cfg.sw_test_status_vif.can_pass_only_in_test = 0;

    // The steps in this test closely follow the gdb steps, which are encoded
    // in a host-side (Rust) test harness located at
    // sw/host/tests/rom/e2e_openocd_debug_test/src/main.rs

    // Let the chip power up and allow the ROM to execute upto an arbitrary point.
    `DV_WAIT(cfg.chip_vif.pwrmgr_fast_pwr_state_active)
    begin
      uint32_t cpu_cycles;
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(cpu_cycles,
          cpu_cycles dist {
            0             :/ 3,
            [1:1000]      :/ 3,
            [1000:10000]  :/ 2,
            [10000:20000] :/ 2
          };
      )
      cfg.chip_vif.cpu_clk_rst_if.wait_clks(cpu_cycles);
    end

    // Halt the CPU.
    cfg.debugger.set_elf_file(elf_file);
    cfg.debugger.set_dmactive(1);
    cfg.debugger.set_haltreq(1);
    cfg.debugger.wait_cpu_halted();
    cfg.debugger.set_haltreq(0);

    `uvm_info(`gfn, "Disable the watchdog timer", UVM_LOW)
    cfg.debugger.mem_read(.addr(ral.aon_timer_aon.wdog_ctrl.get_address()),
                          .value_q(value_q),
                          .status(status));
    `DV_CHECK_EQ(status, 0)
    void'(ral.aon_timer_aon.wdog_ctrl.predict(.value(value_q[0]), .kind(UVM_PREDICT_DIRECT)));
    if (`gmv(ral.aon_timer_aon.wdog_ctrl.enable)) begin
      `uvm_info(`gfn, "WDOG is enabled. Disabling it", UVM_LOW)
      cfg.debugger.mem_write(.addr(ral.aon_timer_aon.wdog_ctrl.get_address()),
                             .value_q({0}),
                             .status(status));
      `DV_CHECK_EQ(status, 0)
      `uvm_info(`gfn, "Reset the WDOG count", UVM_LOW)
      cfg.debugger.mem_write(.addr(ral.aon_timer_aon.wdog_count.get_address()),
                             .value_q({0}),
                             .status(status));
      `DV_CHECK_EQ(status, 0)
      `uvm_info(`gfn, "Clear the interrupt (if any) by writing to INTR_STATE", UVM_LOW)
      cfg.debugger.mem_write(.addr(ral.aon_timer_aon.intr_state.get_address()),
                             .value_q({0}),
                             .status(status));
      `DV_CHECK_EQ(status, 0)
    end else begin
      `uvm_info(`gfn, "WDOG is not enabled.", UVM_LOW)
    end

    // See additional notes on the PMP configuration in the GDB script referenced above.
    `uvm_info(`gfn, "Configure the PMP unit", UVM_LOW)
    // "Write "L NAPOT X W R" to pmp{0,1,2,3}cfg in pmpcfg0. Crucially, this value is no less
    // permissive than whatever the current value is."
    cfg.debugger.abstract_cmd_reg_write(.regno(dm::CSR_PMPCFG0), .value_q({'h9f9f9f9f}),
                                        .status(abs_status));
    `DV_CHECK_EQ(abs_status, jtag_rv_debugger_pkg::AbstractCmdErrNone)
    cfg.debugger.abstract_cmd_reg_write(.regno(dm::CSR_PMPADDR0), .value_q({'hffffffff}),
                                        .status(abs_status));
    `DV_CHECK_EQ(abs_status, jtag_rv_debugger_pkg::AbstractCmdErrNone)

    begin
      longint unsigned addr, size;
      bit result;
      result = dv_utils_pkg::sw_symbol_get_addr_size(.elf_file(elf_file),
          .symbol("_stack_end"), .does_not_exist_ok(0), .addr(addr), .size(size));
      `DV_CHECK(result)
      sram_program_sp = BUS_AW'(addr);
      result = dv_utils_pkg::sw_symbol_get_addr_size(.elf_file(elf_file),
          .symbol("__global_pointer$"), .does_not_exist_ok(0), .addr(addr), .size(size));
      `DV_CHECK(result)
      sram_program_gp = BUS_AW'(addr);
      result = dv_utils_pkg::sw_symbol_get_addr_size(.elf_file(elf_file),
          .symbol("sram_main"), .does_not_exist_ok(0), .addr(addr), .size(size));
      `DV_CHECK(result)
      sram_program_start = BUS_AW'(addr);
    end

    `uvm_info(`gfn, "Load the SRAM program onto the device", UVM_LOW)
    cfg.debugger.load_image(.vmem_file({cfg.sw_images[SwTypeDebug], ".32.vmem"}),
                            .addr(sram_program_start));

    `uvm_info(`gfn, "Update registers before calling functions", UVM_LOW)
    cfg.debugger.abstract_cmd_reg_write(.regno(jtag_rv_debugger_pkg::RvCoreCsrGprSp),
                                        .value_q({sram_program_sp}),
                                        .status(abs_status));
    `DV_CHECK_EQ(abs_status, jtag_rv_debugger_pkg::AbstractCmdErrNone)
    cfg.debugger.abstract_cmd_reg_write(.regno(jtag_rv_debugger_pkg::RvCoreCsrGprGp),
                                        .value_q({sram_program_gp}),
                                        .status(abs_status));
    `DV_CHECK_EQ(abs_status, jtag_rv_debugger_pkg::AbstractCmdErrNone)

    `uvm_info(`gfn, "Invalidate the icache", UVM_LOW)
    cfg.debugger.call(.symbol("icache_invalidate"));

    `uvm_info(`gfn, "Call sram_main (it writes the PASS pattern to the DV monitor)", UVM_LOW)
    cfg.debugger.call(.symbol("sram_main"), .noreturn_function(1));
  endtask

endclass
