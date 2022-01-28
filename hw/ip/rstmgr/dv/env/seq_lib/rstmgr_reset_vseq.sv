// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the reset_info CSR settings for random resets.
class rstmgr_reset_vseq extends rstmgr_base_vseq;
  `uvm_object_utils(rstmgr_reset_vseq)

  `uvm_object_new

  rand logic enable_alert_info;
  rand logic enable_cpu_info;

  constraint sw_reset_c {
    sw_reset dist {
      1 := 1,
      0 := 3
    };
  }
  constraint scan_reset_c {
    solve sw_reset before scan_reset;
    if (sw_reset == 0) {
      scan_reset dist {
        1 := 1,
        0 := 3
      };
    } else {
      scan_reset == 0;
    }
  }
  constraint low_power_reset_c {
    solve scan_reset before low_power_reset;
    if (scan_reset == 0) {
      low_power_reset dist {
        1 := 1,
        0 := 3
      };
    } else {
      low_power_reset == 0;
    }
  }
  constraint ndm_reset_c {
    solve low_power_reset before ndm_reset;
    if (low_power_reset == 0) {
      ndm_reset dist {
        1 := 1,
        0 := 3
      };
    } else {
      ndm_reset == 0;
    }
  }
  constraint rstreqs_c {
    solve ndm_reset before rstreqs;
    if (ndm_reset == 0) {rstreqs != '0;} else {rstreqs == '0;}
  }

  task body();
    int expected_reset_info;
    alert_pkg::alert_crashdump_t prev_alert_dump = '0;
    ibex_pkg::crash_dump_t prev_cpu_dump = '0;

    // Expect reset info to be POR when running the sequence standalone.
    if (is_running_sequence("rstmgr_reset_vseq")) begin
      check_reset_info(1, "expected reset_info to be POR");
      check_alert_and_cpu_info_after_reset(.alert_dump('0), .cpu_dump('0), .enable(1'b0));
    end

    // Clear reset_info register, and enable cpu and alert info capture.
    csr_wr(.ptr(ral.reset_info), .value('1));

    for (int i = 0; i < num_trans; ++i) begin
      logic  [TL_DW-1:0] value;
      string             reset_type;
      logic              expected_info_enable;
      logic              expected_info_update;

      `uvm_info(`gfn, "Starting new round", UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      set_alert_info_for_capture(alert_dump, enable_alert_info);
      set_cpu_info_for_capture(cpu_dump, enable_cpu_info);
      csr_wr(.ptr(ral.reset_info), .value('1));

      if (scan_reset) begin
        // This resets the info registers, which means the previous info contents become zero.
        expected_reset_info = 1;
        expected_info_enable = 0;
        expected_info_update = 0;
        prev_alert_dump = '0;
        prev_cpu_dump = '0;
        send_scan_reset();
        reset_type = "scan reset POR";
      end else if (low_power_reset) begin
        expected_reset_info  = 2;
        expected_info_enable = 1;
        expected_info_update = 1;
        send_reset(pwrmgr_pkg::LowPwrEntry, 0);
        reset_type = "low power reset";
      end else if (ndm_reset) begin
        expected_reset_info  = 4;
        expected_info_enable = 1;
        expected_info_update = 1;
        send_ndm_reset();
        reset_type = "ndm reset";
      end else if (sw_reset) begin
        expected_reset_info  = 8;
        expected_info_enable = 0;
        expected_info_update = 1;
        send_sw_reset();
        reset_type = "sw reset reset";
      end else if (rstreqs) begin
        expected_reset_info  = {'0, rstreqs, 4'b0};
        expected_info_enable = 0;
        expected_info_update = 1;
        send_reset(pwrmgr_pkg::HwReq, rstreqs);
        reset_type = "hw reset";
      end

      cfg.clk_rst_vif.wait_clks(8);
      wait(cfg.rstmgr_vif.resets_o.rst_lc_n);
      check_reset_info(expected_reset_info, reset_type);

      if (expected_info_update && enable_alert_info) begin
        check_alert_info_after_reset(alert_dump, enable_alert_info && expected_info_enable);
        prev_alert_dump = alert_dump;
      end else begin
        check_alert_info_after_reset(prev_alert_dump, enable_alert_info && expected_info_enable);
      end

      if (expected_info_update && enable_cpu_info) begin
        check_cpu_info_after_reset(cpu_dump, enable_cpu_info && expected_info_enable);
        prev_cpu_dump = cpu_dump;
      end else begin
        check_cpu_info_after_reset(prev_cpu_dump, enable_cpu_info && expected_info_enable);
      end
    end
    csr_wr(.ptr(ral.reset_info), .value('1));
    // This clears the info registers to cancel side-effects into other sequences with stress tests.
    clear_alert_and_cpu_info();
  endtask

endclass : rstmgr_reset_vseq
