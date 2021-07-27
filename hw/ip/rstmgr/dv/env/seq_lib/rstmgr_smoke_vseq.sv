// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class rstmgr_smoke_vseq extends rstmgr_base_vseq;
  `uvm_object_utils(rstmgr_smoke_vseq)

  `uvm_object_new

  task body();
    // The rstmgr is ready for CSR accesses.
    logic [TL_DW-1:0] value;
    ibex_pkg::crash_dump_t cpu_dump;

    cpu_dump = '{current_pc: 32'hdead_beef, next_pc: 32'hbeef_dead, last_data_addr: 32'haaaa_aaaa,
                 exception_addr: 32'h5555_5555};
    set_cpu_dump_info(cpu_dump);

    // Send a reset for low power exit.
    // Expect reset info to be POR.
    csr_rd_check(.ptr(ral.reset_info), .compare_value(32'h1));
    check_cpu_dump_info('0);

    // Clear reset_info register.
    csr_wr(.ptr(ral.reset_info), .value('1));

    // Send low power entry reset.
    set_reset_cause(pwrmgr_pkg::LowPwrEntry);
    set_pwrmgr_rst_reqs(.rst_lc_req('1), .rst_sys_req('1));
    set_rstreqs(3'b1);
    `uvm_info(`gfn, $sformatf("Sending reset for low power"), UVM_LOW)
    cfg.io_div4_clk_rst_vif.wait_clks(10);
    csr_rd_check(.ptr(ral.reset_info), .compare_value(32'h2),
                 .err_msg("Expected reset info to be low power"));
    // Pwrmgr drops reset requests.
    `uvm_info(`gfn, $sformatf("Clearing reset for low power"), UVM_LOW)
    set_reset_cause(pwrmgr_pkg::ResetNone);
    set_pwrmgr_rst_reqs(.rst_lc_req('0), .rst_sys_req('0));

    // Clear reset_info register.
    csr_wr(.ptr(ral.reset_info), .value('1));
    cfg.io_div4_clk_rst_vif.wait_clks(10);

    // Send HwReq.
    // Enable cpu_info capture.
    // TODO Also enable alert_info recording and send alert_info.
    csr_wr(.ptr(ral.cpu_info_ctrl.en), .value(1'b1));
    cpu_dump = '{current_pc: 32'h0, next_pc: 32'h444, last_data_addr: 32'h888,
                 exception_addr: 32'hccc};
    `uvm_info(`gfn, $sformatf("Setting cpu_dump_i to %p", cpu_dump), UVM_LOW)
    set_cpu_dump_info(cpu_dump);

    set_reset_cause(pwrmgr_pkg::HwReq);
    set_pwrmgr_rst_reqs(.rst_lc_req('1), .rst_sys_req('1));
    `uvm_info(`gfn, $sformatf("Sending hw req reset"), UVM_LOW)

    cfg.io_div4_clk_rst_vif.wait_clks(10);
    csr_rd_check(.ptr(ral.reset_info), .compare_value(32'h8));
    // Pwrmgr drops reset requests.
    `uvm_info(`gfn, $sformatf("Clearing hw req reset"), UVM_LOW)
    set_reset_cause(pwrmgr_pkg::ResetNone);
    set_pwrmgr_rst_reqs(.rst_lc_req('0), .rst_sys_req('0));
    check_cpu_dump_info(cpu_dump);

    // Clear reset_info register.
    csr_wr(.ptr(ral.reset_info), .value('1));

    cpu_dump = '{current_pc: 32'haaaa_cccc, next_pc: 32'hbbbb_8888, last_data_addr: 32'hcccc_4444,
                 exception_addr: 32'hdddd_0000};
    `uvm_info(`gfn, $sformatf("Setting cpu_dump_i to %p", cpu_dump), UVM_LOW)
    set_cpu_dump_info(cpu_dump);

    // Send debug reset.
    set_ndmreset_req(1'b1);
    `uvm_info(`gfn, $sformatf("Sending ndm reset"), UVM_LOW)
    cfg.io_div4_clk_rst_vif.wait_clks(10);
    csr_rd_check(.ptr(ral.reset_info), .compare_value(32'h4));

    set_ndmreset_req(1'b0);
    `uvm_info(`gfn, $sformatf("Clearing ndm reset"), UVM_LOW)
    check_cpu_dump_info(cpu_dump);

    // Clear reset_info register.
    csr_wr(.ptr(ral.reset_info), .value('1));

    // Testing software resets.
    begin : sw_rst
      logic [6:0] regen;
      logic [6:0] maybe_ctrl_n;
      logic [6:0] initial_value;
      logic [6:0] actual_ctrl_n;
      ibex_pkg::crash_dump_t not_captured_cpu_dump;

      not_captured_cpu_dump = '{current_pc: 'x, next_pc: 'x, last_data_addr: 'x, exception_addr: 'x};
      set_cpu_dump_info(not_captured_cpu_dump);
      csr_rd(.ptr(ral.sw_rst_ctrl_n), .value(initial_value));
      // Send a software reset via CSR writes. Enable 1, 3, 5, and 6.
      regen = 7'h6a;
      csr_wr(.ptr(ral.sw_rst_regen), .value(regen));
      `uvm_info(`gfn, $sformatf("sw_rst_regen set to 0x%0h", regen), UVM_LOW)
      // And enable reset at bit 1.
      maybe_ctrl_n = 7'h78;
      csr_wr(.ptr(ral.sw_rst_ctrl_n), .value(maybe_ctrl_n));
      `uvm_info(`gfn, $sformatf("sw_rst_ctrl_n set to 0x%0x", maybe_ctrl_n), UVM_LOW)
      actual_ctrl_n = initial_value & ~regen | maybe_ctrl_n & regen;
      csr_rd_check(.ptr(ral.sw_rst_ctrl_n), .compare_value(actual_ctrl_n),
                   .err_msg("actual sw_rst_ctrl_n"));

      // And check that the reset outputs match the actual ctrl_n settings.
      `DV_CHECK_EQ(cfg.rstmgr_vif.resets_o.rst_spi_device_n[1], actual_ctrl_n[0])
      `DV_CHECK_EQ(cfg.rstmgr_vif.resets_o.rst_spi_host0_n[1], actual_ctrl_n[1])
      `DV_CHECK_EQ(cfg.rstmgr_vif.resets_o.rst_spi_host1_n[1], actual_ctrl_n[2])
      `DV_CHECK_EQ(cfg.rstmgr_vif.resets_o.rst_usb_n[1], actual_ctrl_n[3])
      `DV_CHECK_EQ(cfg.rstmgr_vif.resets_o.rst_i2c0_n[1], actual_ctrl_n[4])
      `DV_CHECK_EQ(cfg.rstmgr_vif.resets_o.rst_i2c1_n[1], actual_ctrl_n[5])
      `DV_CHECK_EQ(cfg.rstmgr_vif.resets_o.rst_i2c2_n[1], actual_ctrl_n[6])
      check_cpu_dump_info(cpu_dump);
    end
    cfg.io_div4_clk_rst_vif.wait_clks(100);
  endtask : body

endclass : rstmgr_smoke_vseq
