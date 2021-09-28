// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The frequency vseq exercises the frequency measurement counters. More details
// in the clkmgr_testplan.hjson file.
class clkmgr_frequency_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_frequency_vseq)

  `uvm_object_new

  rand int cycles_off[ClkMesrUsb + 1];
  constraint cycles_off_c {
    foreach (cycles_off[clk])
    cycles_off[clk] dist {
      [-4 : -2] := 2,
      0         := 4,
      [2 : 4]   := 2
    };
  }

  task enable_frequency_measurement(clk_mesr_e which, int min_threshold, int max_threshold);
    case (which)
      ClkMesrIo: begin
        ral.io_measure_ctrl.en.set(1);
        ral.io_measure_ctrl.min_thresh.set(min_threshold);
        ral.io_measure_ctrl.max_thresh.set(max_threshold);
        csr_update(.csr(ral.io_measure_ctrl));
      end
      ClkMesrIoDiv2: begin
        ral.io_div2_measure_ctrl.en.set(1);
        ral.io_div2_measure_ctrl.min_thresh.set(min_threshold);
        ral.io_div2_measure_ctrl.max_thresh.set(max_threshold);
        csr_update(.csr(ral.io_div2_measure_ctrl));
      end
      ClkMesrIoDiv4: begin
        ral.io_div4_measure_ctrl.en.set(1);
        ral.io_div4_measure_ctrl.min_thresh.set(min_threshold);
        ral.io_div4_measure_ctrl.max_thresh.set(max_threshold);
        csr_update(.csr(ral.io_div4_measure_ctrl));
      end
      ClkMesrMain: begin
        ral.main_measure_ctrl.en.set(1);
        ral.main_measure_ctrl.min_thresh.set(min_threshold);
        ral.main_measure_ctrl.max_thresh.set(max_threshold);
        csr_update(.csr(ral.main_measure_ctrl));
      end
      ClkMesrUsb: begin
        ral.usb_measure_ctrl.en.set(1);
        ral.usb_measure_ctrl.min_thresh.set(min_threshold);
        ral.usb_measure_ctrl.max_thresh.set(max_threshold);
        csr_update(.csr(ral.usb_measure_ctrl));
      end
    endcase
  endtask

  task body();
    logic [TL_DW-1:0] value;
    int expected_ratios[clk_mesr_e] = '{
      ClkMesrIo: IoClkHz / AonClkHz,
      ClkMesrIoDiv2: IoClkHz / 2 / AonClkHz,
      ClkMesrIoDiv4: IoClkHz / 4 / AonClkHz,
      ClkMesrMain: MainClkHz / AonClkHz,
      ClkMesrUsb: UsbClkHz / AonClkHz
    };
    update_csrs_with_reset_values();
    csr_wr(.ptr(ral.measure_ctrl_regwen), .value(1));

    // Make sure the aon clock is running as slow as it is meant to.
    cfg.aon_clk_rst_vif.set_freq_khz(AonClkHz / 1_000);

    // Set the thresholds to get no error.
    foreach (expected_ratios[clk]) begin
      enable_frequency_measurement(clk, expected_ratios[clk] - 1, expected_ratios[clk] + 1);
    end
    cfg.aon_clk_rst_vif.wait_clks(4);
    csr_rd_check(.ptr(ral.recov_err_code), .compare_value('0),
                 .err_msg("Expected no measurement errors"));
    // And clear errors.
    csr_wr(.ptr(ral.recov_err_code), .value('1));

    for (int i = 0; i < num_trans; ++i) begin
      logic [ClkMesrUsb:0] expected_recov_err = '0;
      `DV_CHECK_RANDOMIZE_FATAL(this)
      foreach (expected_ratios[clk]) begin
        int center_ratio = expected_ratios[clk] + cycles_off[clk];
        if (cycles_off[clk]) begin
          cfg.scoreboard.set_exp_alert(.alert_name("recov_fault"), .max_delay(40000));
          expected_recov_err[clk] = 1;
        end
        enable_frequency_measurement(clk, center_ratio - 1, center_ratio + 1);
      end
      cfg.aon_clk_rst_vif.wait_clks(4);
      csr_rd_check(.ptr(ral.recov_err_code), .compare_value(expected_recov_err),
                   .err_msg("Mismatch in recoverable errors"));
      // And clear errors.
      csr_wr(.ptr(ral.recov_err_code), .value('1));
    end
  endtask

endclass
