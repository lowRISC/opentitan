// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class rstmgr_smoke_vseq extends rstmgr_base_vseq;
  `uvm_object_utils(rstmgr_smoke_vseq)

  `uvm_object_new

  rand ibex_pkg::crash_dump_t  cpu_dump;
  rand logic [NumHwResets-1:0] rstreqs;
  rand logic [NumSwResets-1:0] sw_rst_regen;
  rand logic [NumSwResets-1:0] sw_rst_ctrl_n;

  constraint rstreqs_non_zero_c {rstreqs != '0;}
  constraint sw_rst_regen_non_trivial_c {sw_rst_regen != '0 && sw_rst_regen != '1;}
  constraint sw_rst_some_reset_n {sw_rst_regen & ~sw_rst_ctrl_n != '0;}

  task body();
    // The rstmgr is ready for CSR accesses.
    logic [TL_DW-1:0] value;

    set_cpu_dump_info(cpu_dump);

    // Send a reset for low power exit.
    // Expect reset info to be POR.
    csr_rd_check(.ptr(ral.reset_info), .compare_value(32'h1),
                 .err_msg("expected reset_info to indicate POR"));
    check_cpu_dump_info('0);

    // Clear reset_info register.
    csr_wr(.ptr(ral.reset_info), .value('1));

    // Send low power entry reset.
    set_reset_cause(pwrmgr_pkg::LowPwrEntry);
    set_pwrmgr_rst_reqs(.rst_lc_req('1), .rst_sys_req('1));
    set_rstreqs(rstreqs);
    `uvm_info(`gfn, $sformatf("Sending reset for low power"), UVM_LOW)
    cfg.io_div4_clk_rst_vif.wait_clks(10);
    csr_rd_check(.ptr(ral.reset_info), .compare_value(32'h2),
                 .err_msg("Expected reset info to indicate low power"));
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
    `uvm_info(`gfn, $sformatf("Setting cpu_dump_i to %p", cpu_dump), UVM_LOW)
    set_cpu_dump_info(cpu_dump);

    set_reset_cause(pwrmgr_pkg::HwReq);
    set_pwrmgr_rst_reqs(.rst_lc_req('1), .rst_sys_req('1));
    `uvm_info(`gfn, $sformatf("Sending hw req reset"), UVM_LOW)

    cfg.io_div4_clk_rst_vif.wait_clks(10);
    csr_rd_check(.ptr(ral.reset_info), .compare_value({rstreqs, 3'h0}),
                 .err_msg("Expected reset_info to match pwrmgr_rstreqs"));
    // Pwrmgr drops reset requests.
    `uvm_info(`gfn, $sformatf("Clearing hw req reset"), UVM_LOW)
    set_reset_cause(pwrmgr_pkg::ResetNone);
    set_pwrmgr_rst_reqs(.rst_lc_req('0), .rst_sys_req('0));
    check_cpu_dump_info(cpu_dump);

    // Clear reset_info register.
    csr_wr(.ptr(ral.reset_info), .value('1));

    `DV_CHECK_RANDOMIZE_FATAL(this)
    `uvm_info(`gfn, $sformatf("Setting cpu_dump_i to %p", cpu_dump), UVM_LOW)
    set_cpu_dump_info(cpu_dump);

    // Send debug reset.
    set_ndmreset_req(1'b1);
    `uvm_info(`gfn, $sformatf("Sending ndm reset"), UVM_LOW)
    cfg.io_div4_clk_rst_vif.wait_clks(10);
    csr_rd_check(.ptr(ral.reset_info), .compare_value(32'h4),
                 .err_msg("Expected reset_info to indicate ndm reset"));

    set_ndmreset_req(1'b0);
    `uvm_info(`gfn, $sformatf("Clearing ndm reset"), UVM_LOW)
    check_cpu_dump_info(cpu_dump);

    // Clear reset_info register.
    csr_wr(.ptr(ral.reset_info), .value('1));

    // Testing software resets.
    begin : sw_rst
      logic [NumSwResets-1:0] exp_ctrl_n;
      const logic [NumSwResets-1:0] sw_rst_all_ones = '1;
      ibex_pkg::crash_dump_t not_captured_cpu_dump;

      not_captured_cpu_dump = '{current_pc: '1, next_pc: '1, last_data_addr: '1,
                                exception_addr: '1};
      set_cpu_dump_info(not_captured_cpu_dump);

      csr_rd_check(.ptr(ral.sw_rst_ctrl_n), .compare_value(sw_rst_all_ones),
                   .err_msg("expected no reset on"));
      csr_wr(.ptr(ral.sw_rst_regen), .value(sw_rst_regen));
      `uvm_info(`gfn, $sformatf("sw_rst_regen set to 0x%0h", sw_rst_regen), UVM_LOW)
      csr_rd_check(.ptr(ral.sw_rst_regen), .compare_value(sw_rst_regen),
                   .err_msg("Expected sw_rst_regen to reflect rw0c"));

      // Check sw_rst_regen can not be set to all ones again because it is rw0c.
      csr_wr(.ptr(ral.sw_rst_regen), .value('1));
      csr_rd_check(.ptr(ral.sw_rst_regen), .compare_value(sw_rst_regen),
                   .err_msg("Expected sw_rst_regen block raising individual bits because rw0c"));

      // Check that the regen disabled bits block corresponding updated to ctrl_n.
      csr_wr(.ptr(ral.sw_rst_ctrl_n), .value(sw_rst_regen));
      csr_rd_check(.ptr(ral.sw_rst_ctrl_n), .compare_value(sw_rst_all_ones),
                   .err_msg("Expected sw_rst_ctrl_n not to change"));

      csr_wr(.ptr(ral.sw_rst_ctrl_n), .value(sw_rst_ctrl_n));
      `uvm_info(`gfn, $sformatf("Attempted to set sw_rst_ctrl_n to 0x%0x", sw_rst_ctrl_n), UVM_LOW)
      exp_ctrl_n = ~sw_rst_regen | sw_rst_ctrl_n;
      // And check that the reset outputs match the actual ctrl_n settings.
      // Allow for domain crossing delay.
      cfg.io_div2_clk_rst_vif.wait_clks(3);
      check_software_reset_csr_and_pins(exp_ctrl_n);
      check_cpu_dump_info(cpu_dump);

      csr_wr(.ptr(ral.sw_rst_ctrl_n), .value('1));
      csr_rd_check(.ptr(ral.sw_rst_ctrl_n), .compare_value(sw_rst_all_ones),
                   .err_msg("Expected sw_rst_ctrl_n to be set"));
    end
  endtask : body

endclass : rstmgr_smoke_vseq
