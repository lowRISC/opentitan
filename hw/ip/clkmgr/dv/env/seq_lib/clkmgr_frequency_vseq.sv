// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The frequency vseq exercises the frequency measurement counters. More details
// in the clkmgr_testplan.hjson file.
class clkmgr_frequency_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_frequency_vseq)

  `uvm_object_new

  // This is measured in aon clocks, and is pretty tight.
  localparam int CyclesToGetOneMeasurement = 2;
  // This is measured in clkmgr clk_i clocks. It is set to cover worse case delays.
  // The clk_i frequency is randomized for IPs, but the clkmgr is hooked to io_div4, which would
  // allow a tighter number of cycles.
  // TODO(maturana) Connect clkmgr's clk_i to the powerup io_div4 clock, as is in the chip.
  localparam int CyclesForErrUpdate = 16;

  // The min ands max offsets from the expected counts. Notice the count occasionally matches
  // expected_counts - 1, so the offsets are set carefully to avoid spurious results.
  //
  // The exp_alert cip feature requires a single alert at a time, so we set at most one of the
  // clocks to fail measurement.
  rand int clk_tested;
  constraint clk_tested_c {clk_tested inside {[ClkMesrIo : ClkMesrUsb]};}

  typedef enum int {
    MesrLow,
    MesrRight,
    MesrHigh
  } mesr_e;
  rand mesr_e mesr;
  rand int min_offset;
  rand int max_offset;

  constraint thresholds_c {
    solve clk_tested before mesr;
    solve mesr before min_offset, max_offset;
    if (mesr == MesrLow) {
      min_offset inside {[-4 : -2]};
      max_offset inside {[-4 : -2]};
      min_offset <= max_offset;
    } else
    if (mesr == MesrRight) {
      min_offset == -1;
      max_offset == 1;
    } else
    if (mesr == MesrHigh) {
      min_offset inside {[2 : 4]};
      max_offset inside {[2 : 4]};
      min_offset <= max_offset;
    }
  }

  task disable_frequency_measurement(clk_mesr_e which);
    `uvm_info(`gfn, $sformatf("Disabling frequency measurement for %0s", which.name), UVM_MEDIUM)
    case (which)
      ClkMesrIo: begin
        csr_wr(.ptr(ral.io_measure_ctrl.en), .value(0));
      end
      ClkMesrIoDiv2: begin
        csr_wr(.ptr(ral.io_div2_measure_ctrl.en), .value(0));
      end
      ClkMesrIoDiv4: begin
        csr_wr(.ptr(ral.io_div4_measure_ctrl.en), .value(0));
      end
      ClkMesrMain: begin
        csr_wr(.ptr(ral.main_measure_ctrl.en), .value(0));
      end
      ClkMesrUsb: begin
        csr_wr(.ptr(ral.usb_measure_ctrl.en), .value(0));
      end
    endcase
  endtask

  task enable_frequency_measurement(clk_mesr_e which, int min_threshold, int max_threshold);
    `uvm_info(`gfn, $sformatf(
              "Enabling frequency measurement for %0s, min=%0d, max=%0d, expected=%0d",
              which.name,
              min_threshold,
              max_threshold,
              ExpectedCounts[which]
              ), UVM_MEDIUM)
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

  // This waits a number of cycles so that:
  // - only one measurement completes, or we could end up with multiple alerts which cause trouble
  //   for the cip exp_alert functionality, and,
  // - the measurement has had time to update the recov_err_code CSR.
  task wait_before_read_recov_err_code();
    // Wait for one measurement (takes an extra cycle to really start).
    cfg.aon_clk_rst_vif.wait_clks(CyclesToGetOneMeasurement);
    // Wait for the result to propagate to the recov_err_code CSR.
    cfg.clk_rst_vif.wait_clks(CyclesForErrUpdate);
  endtask

  task body();
    logic [TL_DW-1:0] value;
    update_csrs_with_reset_values();
    csr_wr(.ptr(ral.measure_ctrl_regwen), .value(1));

    // Make sure the aon clock is running as slow as it is meant to.
    cfg.aon_clk_rst_vif.set_freq_khz(AonClkHz / 1_000);

    // Set the thresholds to get no error.
    foreach (ExpectedCounts[clk]) begin
      clk_mesr_e clk_mesr = clk_mesr_e'(clk);
      enable_frequency_measurement(clk_mesr, ExpectedCounts[clk] - 1, ExpectedCounts[clk]);
    end
    wait_before_read_recov_err_code();
    csr_rd_check(.ptr(ral.recov_err_code), .compare_value('0),
                 .err_msg("Expected no measurement errors"));
    foreach (ExpectedCounts[clk]) begin
      clk_mesr_e clk_mesr = clk_mesr_e'(clk);
      disable_frequency_measurement(clk_mesr);
    end
    cfg.aon_clk_rst_vif.wait_clks(2);
    // And clear errors.
    csr_wr(.ptr(ral.recov_err_code), .value('1));

    `uvm_info(`gfn, $sformatf("Will run %0d rounds", num_trans), UVM_MEDIUM)
    for (int i = 0; i < num_trans; ++i) begin
      logic [ClkMesrUsb:0] actual_recov_err = '0;
      logic [ClkMesrUsb:0] expected_recov_err = '0;
      `DV_CHECK_RANDOMIZE_FATAL(this)
      foreach (ExpectedCounts[clk]) begin
        clk_mesr_e clk_mesr = clk_mesr_e'(clk);
        int min_threshold;
        int max_threshold;
        int expected = ExpectedCounts[clk];
        if (clk == clk_tested) begin
          min_threshold = expected + min_offset;
          max_threshold = expected + max_offset;
          if (min_threshold > expected || max_threshold < expected - 1) begin
            cfg.scoreboard.set_exp_alert(.alert_name("recov_fault"), .max_delay(4000));
            expected_recov_err[clk] = 1;
          end
        end else begin
          min_threshold = expected - 1;
          max_threshold = expected;
        end
        enable_frequency_measurement(clk_mesr, min_threshold, max_threshold);
      end
      wait_before_read_recov_err_code();
      csr_rd(.ptr(ral.recov_err_code), .value(actual_recov_err));
      if (actual_recov_err != expected_recov_err) begin
        logic [ClkMesrUsb:0] mismatch_recov_err = actual_recov_err ^ expected_recov_err;
        foreach (mismatch_recov_err[clk]) begin
          clk_mesr_e clk_mesr = clk_mesr_e'(clk);
          if (mismatch_recov_err[clk]) begin
            `uvm_info(`gfn, $sformatf(
                      "Mismatch for %0s, expected %b, actual %b",
                      clk_mesr.name,
                      expected_recov_err[clk],
                      actual_recov_err[clk]
                      ), UVM_LOW)
          end
        end
        `uvm_error(`gfn, $sformatf(
                   "Mismatch for recov_err, expected 0b%b, got 0x%b",
                   expected_recov_err,
                   actual_recov_err
                   ))
      end
      foreach (ExpectedCounts[clk]) begin
        clk_mesr_e clk_mesr = clk_mesr_e'(clk);
        disable_frequency_measurement(clk_mesr);
      end
      cfg.aon_clk_rst_vif.wait_clks(2);
      // And clear errors.
      csr_wr(.ptr(ral.recov_err_code), .value('1));
    end
  endtask

endclass
