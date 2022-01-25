// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the reset_info CSR settings for random resets.
class rstmgr_reset_vseq extends rstmgr_base_vseq;
  `uvm_object_utils(rstmgr_reset_vseq)

  `uvm_object_new

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
    // Expect reset info to be POR.
    check_reset_info(1, "expected reset_info to be POR");
    check_alert_and_cpu_info_after_reset(.alert_dump('0), .cpu_dump('0), .enable(1'b0));

    // Clear reset_info register, and enable cpu and alert info capture.
    csr_wr(.ptr(ral.reset_info), .value('1));

    for (int i = 0; i < num_trans; ++i) begin
      logic [TL_DW-1:0] value;
      `uvm_info(`gfn, "Starting new round", UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      set_alert_and_cpu_info_for_capture(alert_dump, cpu_dump);
      csr_wr(.ptr(ral.reset_info), .value('1));
      if (scan_reset) begin
        expected_reset_info = 1;
        send_scan_reset();
      end else if (low_power_reset) begin
        expected_reset_info = 2;
        send_reset(pwrmgr_pkg::LowPwrEntry, 0);
      end else if (ndm_reset) begin
        expected_reset_info = 4;
        send_ndm_reset();
      end else if (sw_reset) begin
        expected_reset_info = 8;
        send_sw_reset();
      end else if (rstreqs) begin
        expected_reset_info = {'0, rstreqs, 4'b0};
        send_reset(pwrmgr_pkg::HwReq, rstreqs);
      end

      cfg.clk_rst_vif.wait_clks(8);
      wait(cfg.rstmgr_vif.resets_o.rst_lc_n);
      csr_rd_check(.ptr(ral.reset_info), .compare_value(expected_reset_info));
    end
  endtask

endclass : rstmgr_reset_vseq
