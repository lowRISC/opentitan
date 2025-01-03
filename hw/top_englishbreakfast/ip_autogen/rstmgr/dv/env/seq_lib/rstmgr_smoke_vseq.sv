// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the different kinds of reset: POR, low power wakeup, hardware reset, debug_mode reset,
// and software initiated peripheral resets.
class rstmgr_smoke_vseq extends rstmgr_base_vseq;

  `uvm_object_utils(rstmgr_smoke_vseq)

  `uvm_object_new

  constraint rstreqs_non_zero_c {rstreqs != '0;}
  constraint sw_rst_regwen_non_trivial_c {sw_rst_regwen != '0 && sw_rst_regwen != '1;}
  constraint sw_rst_some_reset_c {sw_rst_regwen & ~sw_rst_ctrl_n != '0;}

  local task wait_between_resets();
    cfg.io_div4_clk_rst_vif.wait_clks(10);
  endtask

  task body();
    uvm_reg_data_t exp_reg;
    bit is_standalone = is_running_sequence("rstmgr_smoke_vseq");
    // Expect reset info to be POR when running the sequence standalone.
    if (is_standalone) begin
      check_reset_info(1, "expected reset_info to be POR");
      check_alert_and_cpu_info_after_reset(.alert_dump('0), .cpu_dump('0), .enable(1'b0));
    end
    csr_wr(.ptr(ral.reset_info), .value('1));
    set_alert_and_cpu_info_for_capture(alert_dump, cpu_dump);

    send_scan_reset();
    // Scan reset triggers an AON reset (and all others).
    wait(&cfg.rstmgr_vif.resets_o.rst_por_aon_n);

    check_reset_info(1, "expected reset_info to be POR for scan reset");
    // Alert and cpu info settings were reset. Check and re-enable them.
    check_alert_and_cpu_info_after_reset(.alert_dump('0), .cpu_dump('0), .enable(1'b0));
    wait_between_resets();

    set_alert_and_cpu_info_for_capture(alert_dump, cpu_dump);

    csr_wr(.ptr(ral.reset_info), .value('1));

    // Send low power entry reset.
    send_lowpower_reset();
    exp_reg = csr_utils_pkg::get_csr_val_with_updated_field(ral.reset_info.low_power_exit, '0, 1);
    check_reset_info(exp_reg, "expected reset_info to indicate low power");
    check_alert_and_cpu_info_after_reset(alert_dump, cpu_dump, 1'b1);
    wait_between_resets();

    csr_wr(.ptr(ral.reset_info), .value('1));

    // Send HwReq.
    // Enable alert_info and cpu_info capture.
    `DV_CHECK_RANDOMIZE_FATAL(this)
    set_alert_and_cpu_info_for_capture(alert_dump, cpu_dump);

    send_hw_reset(rstreqs);
    exp_reg = csr_utils_pkg::get_csr_val_with_updated_field(ral.reset_info.hw_req, '0, rstreqs);
    check_reset_info(exp_reg, $sformatf("expected reset_info to match 0x%x", exp_reg));
    check_alert_and_cpu_info_after_reset(alert_dump, cpu_dump, 1'b0);
    wait_between_resets();

    csr_wr(.ptr(ral.reset_info), .value('1));

    `DV_CHECK_RANDOMIZE_FATAL(this)
    set_alert_and_cpu_info_for_capture(alert_dump, cpu_dump);

    `DV_CHECK_RANDOMIZE_FATAL(this)
    set_alert_and_cpu_info_for_capture(alert_dump, cpu_dump);

    // Send sw reset.
    csr_wr(.ptr(ral.reset_req), .value(MuBi4True));
    send_sw_reset();
    exp_reg = csr_utils_pkg::get_csr_val_with_updated_field(ral.reset_info.sw_reset, '0, 1);
    check_reset_info(exp_reg, "Expected reset_info to indicate sw reset");
    check_alert_and_cpu_info_after_reset(alert_dump, cpu_dump, 0);
    wait_between_resets();

    csr_wr(.ptr(ral.reset_info), .value('1));

    // Testing software resets: only run this when the sequence is run standalone, since
    // setting sw_rst_regwen is irreversible.
    if (is_standalone) begin : sw_rst
      logic [NumSwResets-1:0] exp_ctrl_n;
      const logic [NumSwResets-1:0] sw_rst_all_ones = '1;
      alert_crashdump_t bogus_alert_dump = '1;
      cpu_crash_dump_t bogus_cpu_dump = '1;

      set_alert_and_cpu_info_for_capture(bogus_alert_dump, bogus_cpu_dump);
      rstmgr_csr_rd_check_unpack(.ptr(ral.sw_rst_ctrl_n), .compare_value(sw_rst_all_ones),
                                 .err_msg("expected no reset on"));
      rstmgr_csr_wr_unpack(.ptr(ral.sw_rst_regwen), .value(sw_rst_regwen));
      `uvm_info(`gfn, $sformatf("sw_rst_regwen set to 0x%0h", sw_rst_regwen), UVM_LOW)
      rstmgr_csr_rd_check_unpack(.ptr(ral.sw_rst_regwen), .compare_value(sw_rst_regwen));

      // This is probably also tested by common CSR tests.
      // Check sw_rst_regwen can not be set to all ones again because it is rw0c.
      rstmgr_csr_wr_unpack(.ptr(ral.sw_rst_regwen), .value({NumSwResets{1'b1}}));
      rstmgr_csr_rd_check_unpack(.ptr(ral.sw_rst_regwen), .compare_value(sw_rst_regwen),
           .err_msg("Expected sw_rst_regwen block raising individual bits because rw0c"));

      // Check that the regwen disabled bits block corresponding updated to ctrl_n.
      rstmgr_csr_wr_unpack(.ptr(ral.sw_rst_ctrl_n), .value(sw_rst_regwen));
      rstmgr_csr_rd_check_unpack(.ptr(ral.sw_rst_ctrl_n), .compare_value(sw_rst_all_ones),
                                 .err_msg("Expected sw_rst_ctrl_n not to change"));

      check_sw_rst_ctrl_n(sw_rst_ctrl_n, sw_rst_regwen, 1);
      check_alert_and_cpu_info_after_reset(alert_dump, cpu_dump, 1'b1);
    end : sw_rst
    // This clears the info registers to cancel side-effects into other sequences with stress tests.
    clear_alert_and_cpu_info();
  endtask : body

endclass : rstmgr_smoke_vseq
