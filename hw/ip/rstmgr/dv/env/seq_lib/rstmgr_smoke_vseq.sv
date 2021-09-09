// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the different kinds of reset: POR, low power wakeup, hardware reset, debug_mode reset,
// and software initiated peripheral resets.
class rstmgr_smoke_vseq extends rstmgr_base_vseq;
  `uvm_object_utils(rstmgr_smoke_vseq)

  `uvm_object_new

  rand ibex_pkg::crash_dump_t cpu_dump;
  rand alert_pkg::alert_crashdump_t alert_dump;
  rand logic [pwrmgr_pkg::TotalResetWidth-1:0] rstreqs;
  rand logic [NumSwResets-1:0] sw_rst_regen;
  rand logic [NumSwResets-1:0] sw_rst_ctrl_n;

  constraint rstreqs_non_zero_c {rstreqs != '0;}
  constraint sw_rst_regen_non_trivial_c {sw_rst_regen != '0 && sw_rst_regen != '1;}
  constraint sw_rst_some_reset_n {sw_rst_regen & ~sw_rst_ctrl_n != '0;}

  task body();
    // The rstmgr is ready for CSR accesses.
    logic [TL_DW-1:0] value;
    set_alert_and_cpu_info_for_capture(alert_dump, cpu_dump);

    // Expect reset info to be POR.
    csr_rd_check(.ptr(ral.reset_info), .compare_value(32'h1),
                 .err_msg("expected reset_info to indicate POR"));
    check_alert_and_cpu_info_after_reset(.alert_dump('0), .cpu_dump('0), .enable(1'b1));

    // Clear reset_info register, no need to re-enable cpu and alert info capture.
    csr_wr(.ptr(ral.reset_info), .value('1));

    // Send low power entry reset.
    send_reset(pwrmgr_pkg::LowPwrEntry, rstreqs);
    csr_rd_check(.ptr(ral.reset_info), .compare_value(32'h2),
                 .err_msg("Expected reset info to indicate low power"));
    check_alert_and_cpu_info_after_reset(alert_dump, cpu_dump, 1'b0);

    // Clear reset_info register.
    csr_wr(.ptr(ral.reset_info), .value('1));
    cfg.io_div4_clk_rst_vif.wait_clks(10);

    // Send HwReq.
    // Enable alert_info and cpu_info capture.
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(alert_dump);
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(cpu_dump);
    set_alert_and_cpu_info_for_capture(alert_dump, cpu_dump);

    send_reset(pwrmgr_pkg::HwReq, rstreqs);
    csr_rd_check(.ptr(ral.reset_info), .compare_value({rstreqs, 3'h0}),
                 .err_msg("Expected reset_info to match pwrmgr_rstreqs"));
    check_alert_and_cpu_info_after_reset(alert_dump, cpu_dump, 1'b0);

    // Clear reset_info register.
    csr_wr(.ptr(ral.reset_info), .value('1));

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(alert_dump);
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(cpu_dump);
    set_alert_and_cpu_info_for_capture(alert_dump, cpu_dump);

    // Send debug reset.
    send_ndm_reset();
    csr_rd_check(.ptr(ral.reset_info), .compare_value(32'h4),
                 .err_msg("Expected reset_info to indicate ndm reset"));
    check_alert_and_cpu_info_after_reset(alert_dump, cpu_dump, 1'b0);

    // Clear reset_info register.
    csr_wr(.ptr(ral.reset_info), .value('1));

    // Testing software resets.
    begin : sw_rst
      logic [NumSwResets-1:0] exp_ctrl_n;
      const logic [NumSwResets-1:0] sw_rst_all_ones = '1;
      alert_pkg::alert_crashdump_t bogus_alert_dump = '1;
      ibex_pkg::crash_dump_t bogus_cpu_dump = '1;

      set_alert_and_cpu_info_for_capture(bogus_alert_dump, bogus_cpu_dump);
      csr_rd_check(.ptr(ral.sw_rst_ctrl_n[0]), .compare_value(sw_rst_all_ones),
                   .err_msg("expected no reset on"));
      csr_wr(.ptr(ral.sw_rst_regen[0]), .value(sw_rst_regen));
      `uvm_info(`gfn, $sformatf("sw_rst_regen set to 0x%0h", sw_rst_regen), UVM_LOW)
      csr_rd_check(.ptr(ral.sw_rst_regen[0]), .compare_value(sw_rst_regen),
                   .err_msg("Expected sw_rst_regen to reflect rw0c"));

      // Check sw_rst_regen can not be set to all ones again because it is rw0c.
      csr_wr(.ptr(ral.sw_rst_regen[0]), .value('1));
      csr_rd_check(.ptr(ral.sw_rst_regen[0]), .compare_value(sw_rst_regen),
                   .err_msg("Expected sw_rst_regen block raising individual bits because rw0c"));

      // Check that the regen disabled bits block corresponding updated to ctrl_n.
      csr_wr(.ptr(ral.sw_rst_ctrl_n[0]), .value(sw_rst_regen));
      csr_rd_check(.ptr(ral.sw_rst_ctrl_n[0]), .compare_value(sw_rst_all_ones),
                   .err_msg("Expected sw_rst_ctrl_n not to change"));

      csr_wr(.ptr(ral.sw_rst_ctrl_n[0]), .value(sw_rst_ctrl_n));
      `uvm_info(`gfn, $sformatf("Attempted to set sw_rst_ctrl_n to 0x%0x", sw_rst_ctrl_n), UVM_LOW)
      exp_ctrl_n = ~sw_rst_regen | sw_rst_ctrl_n;
      // And check that the reset outputs match the actual ctrl_n settings.
      // Allow for domain crossing delay.
      cfg.io_div2_clk_rst_vif.wait_clks(3);
      check_software_reset_csr_and_pins(exp_ctrl_n);
      check_alert_and_cpu_info_after_reset(alert_dump, cpu_dump, 1'b1);

      csr_wr(.ptr(ral.sw_rst_ctrl_n[0]), .value('1));
      csr_rd_check(.ptr(ral.sw_rst_ctrl_n[0]), .compare_value(sw_rst_all_ones),
                   .err_msg("Expected sw_rst_ctrl_n to be set"));
    end
  endtask : body

endclass : rstmgr_smoke_vseq
