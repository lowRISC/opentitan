// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the different kinds of reset: POR, low power wakeup, hardware reset, debug_mode reset,
// and software initiated peripheral resets.
class rstmgr_smoke_vseq extends rstmgr_base_vseq;
  `uvm_object_utils(rstmgr_smoke_vseq)

  `uvm_object_new

  constraint rstreqs_non_zero_c {rstreqs != '0;}
  constraint sw_rst_regwen_non_trivial_c {sw_rst_regwen != '0 && sw_rst_regwen != '1;}
  constraint sw_rst_some_reset_n {sw_rst_regwen & ~sw_rst_ctrl_n != '0;}

  task body();
    // Expect reset info to be POR.
    check_reset_info(1, "expected reset_info to be POR");
    check_alert_and_cpu_info_after_reset(.alert_dump('0), .cpu_dump('0), .enable(1'b0));

    // Clear reset_info register, and enable cpu and alert info capture.
    csr_wr(.ptr(ral.reset_info), .value('1));
    set_alert_and_cpu_info_for_capture(alert_dump, cpu_dump);

    send_scan_reset();
    // Scan reset triggers an AON reset (and all others).
    wait(cfg.rstmgr_vif.resets_o.rst_por_aon_n == '1);

    check_reset_info(1, "expected reset_info to be POR for scan reset");
    // Alert and cpu info settings were reset. Check and re-enable them.
    check_alert_and_cpu_info_after_reset(.alert_dump('0), .cpu_dump('0), .enable(1'b0));
    set_alert_and_cpu_info_for_capture(alert_dump, cpu_dump);

    // Clear reset_info register.
    csr_wr(.ptr(ral.reset_info), .value('1));

    // Send low power entry reset.
    send_reset(pwrmgr_pkg::LowPwrEntry, '0);
    check_reset_info(2, "expected reset_info to indicate low power");
    check_alert_and_cpu_info_after_reset(alert_dump, cpu_dump, 1'b1);

    // Clear reset_info register.
    csr_wr(.ptr(ral.reset_info), .value('1));
    cfg.io_div4_clk_rst_vif.wait_clks(10);

    // Send HwReq.
    // Enable alert_info and cpu_info capture.
    `DV_CHECK_RANDOMIZE_FATAL(this)
    set_alert_and_cpu_info_for_capture(alert_dump, cpu_dump);

    send_reset(pwrmgr_pkg::HwReq, rstreqs);
    check_reset_info({rstreqs, 4'h0}, $sformatf(
                     "expected reset_info to match 0x%x", {rstreqs, 4'h0}));
    check_alert_and_cpu_info_after_reset(alert_dump, cpu_dump, 1'b0);

    // Clear reset_info register.
    csr_wr(.ptr(ral.reset_info), .value('1));
    `DV_CHECK_RANDOMIZE_FATAL(this)

    set_alert_and_cpu_info_for_capture(alert_dump, cpu_dump);

    // Send debug reset.
    send_ndm_reset();
    check_reset_info(4, "Expected reset_info to indicate ndm reset");
    check_alert_and_cpu_info_after_reset(alert_dump, cpu_dump, 1'b1);

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
      csr_wr(.ptr(ral.sw_rst_regwen[0]), .value(sw_rst_regwen));
      `uvm_info(`gfn, $sformatf("sw_rst_regwen set to 0x%0h", sw_rst_regwen), UVM_LOW)
      csr_rd_check(.ptr(ral.sw_rst_regwen[0]), .compare_value(sw_rst_regwen));

      // Check sw_rst_regwen can not be set to all ones again because it is rw0c.
      csr_wr(.ptr(ral.sw_rst_regwen[0]), .value('1));
      csr_rd_check(.ptr(ral.sw_rst_regwen[0]), .compare_value(sw_rst_regwen),
                   .err_msg("Expected sw_rst_regwen block raising individual bits because rw0c"));

      // Check that the regwen disabled bits block corresponding updated to ctrl_n.
      csr_wr(.ptr(ral.sw_rst_ctrl_n[0]), .value(sw_rst_regwen));
      csr_rd_check(.ptr(ral.sw_rst_ctrl_n[0]), .compare_value(sw_rst_all_ones),
                   .err_msg("Expected sw_rst_ctrl_n not to change"));

      check_sw_rst_ctrl_n(sw_rst_ctrl_n, sw_rst_regwen, 1);
    end
    check_alert_and_cpu_info_after_reset(alert_dump, cpu_dump, 1'b1);
  endtask : body

endclass : rstmgr_smoke_vseq
