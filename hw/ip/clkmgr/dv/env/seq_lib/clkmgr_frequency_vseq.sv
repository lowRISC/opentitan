// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The frequency vseq exercises the frequency measurement counters. More details
// in the clkmgr_testplan.hjson file.
class clkmgr_frequency_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_frequency_vseq)

  `uvm_object_new

  // This is measured in aon clocks. This is cannot be too precise because of a synchronizer.
  localparam int CyclesToGetMeasurements = 6;

  // The aon cycles between measurements, to make sure the previous measurement settles.
  localparam int CyclesBetweenMeasurements = 6;

  // This is measured in clkmgr clk_i clocks. It is set to cover worst case delays.
  // The clk_i frequency is randomized for IPs, but the clkmgr is hooked to io_div4, which would
  // allow a tighter number of cycles. Leaving the clk_i random probably provides more cases,
  // so leaving it as is.
  localparam int CyclesForErrUpdate = 16;

  // The min ands max offsets from the expected counts. Notice the count occasionally matches
  // expected_counts +- 2 because of CDC synchronizers, so the offsets are set carefully to
  // avoid spurious results.
  //
  // The exp_alert cip feature requires a single alert at a time, so we set at most one of the
  // clocks to fail measurement.
  rand int clk_tested;
  constraint clk_tested_c {clk_tested inside {[ClkMesrIo : ClkMesrUsb]};}

  // If cause_saturation is active, force the initial measurement count of clk_tested to a high
  // value so the counter will saturate.
  rand bit cause_saturation;

  typedef enum int {
    MesrLow,
    MesrRight,
    MesrHigh
  } mesr_e;
  rand mesr_e mesr;
  rand int min_offset;
  rand int max_offset;

  mubi4_t calib_rdy;

  constraint thresholds_c {
    solve clk_tested before mesr;
    solve mesr before min_offset, max_offset;
    if (mesr == MesrLow) {
      min_offset inside {[-5 : -3]};
      max_offset inside {[-5 : -3]};
      min_offset <= max_offset;
    } else
    if (mesr == MesrRight) {
      min_offset == -2;
      max_offset == 2;
    } else
    if (mesr == MesrHigh) {
      min_offset inside {[3 : 5]};
      max_offset inside {[3 : 5]};
      min_offset <= max_offset;
    }
  }

  constraint all_clk_en_c {
    io_ip_clk_en == 1;
    main_ip_clk_en == 1;
    usb_ip_clk_en == 1;
  }

  function void post_randomize();
    calib_rdy = get_rand_mubi4_val(6, 2, 2);
    `uvm_info(`gfn, $sformatf("randomize: calib_rdy=0x%x", calib_rdy), UVM_MEDIUM)
    super.post_randomize();
  endfunction

  // Keep saturating the count on aon negedges if needed.
  local task maybe_saturate_count(bit saturate, clk_mesr_e clk_tested);
    forever begin
      @cfg.aon_clk_rst_vif.cbn;
      if (saturate) cfg.clkmgr_vif.force_high_starting_count(clk_mesr_e'(clk_tested));
    end
  endtask

  // This waits a number of cycles so that:
  // - at least one measurement completes, and,
  // - the measurement has had time to update the recov_err_code CSR.
  task wait_before_read_recov_err_code(bit expect_alert);
    // Wait for one measurement (takes an extra cycle to really start).
    cfg.aon_clk_rst_vif.wait_clks(CyclesToGetMeasurements);
    // Wait for the result to propagate to the recov_err_code CSR.
    cfg.clk_rst_vif.wait_clks(CyclesForErrUpdate);
  endtask

  // If clocks become uncalibrated measure_ctrl_regwen is re-enabled.
  task check_measure_ctrl_regwen_for_calib_rdy();
    logic value;
    csr_wr(.ptr(ral.measure_ctrl_regwen), .value(0));
    cfg.clkmgr_vif.update_calib_rdy(MuBi4False);
    cfg.clk_rst_vif.wait_clks(20);
    calibration_lost_checks();
  endtask

  task body();
    logic [TL_DW-1:0] value;
    int prior_alert_count;
    int current_alert_count;

    csr_wr(.ptr(ral.measure_ctrl_regwen), .value(1));

    // Disable alert checks since we cannot make sure a single alert will fire: there is too
    // much uncertainty on the cycles for one measurement to complete due to synchronizers.
    // This test will instead check whether alerts fire using the alert count.
    cfg.scoreboard.do_alert_check = 0;

    // Make sure the aon clock is running as slow as it is meant to.
    cfg.aon_clk_rst_vif.set_freq_khz(AonClkHz / 1_000);
    control_ip_clocks();
    // Wait so the frequency change takes effect.
    cfg.aon_clk_rst_vif.wait_clks(2);

    // Set the thresholds to get no error.
    foreach (ExpectedCounts[clk]) begin
      clk_mesr_e clk_mesr = clk_mesr_e'(clk);
      enable_frequency_measurement(clk_mesr, ExpectedCounts[clk] - 2, ExpectedCounts[clk] + 2);
    end
    wait_before_read_recov_err_code('0);
    csr_rd_check(.ptr(ral.recov_err_code), .compare_value('0),
                 .err_msg("Expected no measurement errors"));
    foreach (ExpectedCounts[clk]) begin
      clk_mesr_e clk_mesr = clk_mesr_e'(clk);
      disable_frequency_measurement(clk_mesr);
    end
    cfg.aon_clk_rst_vif.wait_clks(CyclesBetweenMeasurements);
    // And clear errors.
    csr_wr(.ptr(ral.recov_err_code), .value('1));

    `uvm_info(`gfn, $sformatf("Will run %0d rounds", num_trans), UVM_MEDIUM)
    for (int i = 0; i < num_trans; ++i) begin
      clkmgr_recov_err_t actual_recov_err = '{default: '0};
      logic [ClkMesrUsb:0] expected_recov_meas_err = '0;
      bit expect_alert = 0;
      `DV_CHECK_RANDOMIZE_FATAL(this)
      // Update calib_rdy input: if calibration is not ready the measurements
      // don't happen, so we should not get faults.
      cfg.clkmgr_vif.update_calib_rdy(calib_rdy);
      `uvm_info(`gfn, $sformatf(
                "Updating calib_rdy to 0x%x, predicted regwen 0x%x",
                calib_rdy,
                ral.measure_ctrl_regwen.get()
                ), UVM_MEDIUM)
      `uvm_info(`gfn, "New round", UVM_MEDIUM)
      // Allow calib_rdy to generate side-effects.
      cfg.clk_rst_vif.wait_clks(3);
      if (calib_rdy == MuBi4False) calibration_lost_checks();
      prior_alert_count = cfg.scoreboard.get_alert_count("recov_fault");
      if (cause_saturation) `uvm_info(`gfn, "Will cause saturation", UVM_MEDIUM)
      foreach (ExpectedCounts[clk]) begin
        clk_mesr_e clk_mesr = clk_mesr_e'(clk);
        int min_threshold;
        int max_threshold;
        int expected = ExpectedCounts[clk];
        if (clk == clk_tested) begin
          min_threshold = expected + min_offset;
          max_threshold = expected + max_offset;
          if (calib_rdy != MuBi4False &&
              (min_threshold > expected || max_threshold < expected - 1 || cause_saturation)) begin
            `uvm_info(`gfn, $sformatf(
                      "Expect %0s to get a %0s error%0s",
                      clk_mesr.name,
                      (cause_saturation ? "fast" : (min_threshold > expected ? "slow" : "fast")),
                      (cause_saturation ? " due to saturation" : "")
                      ), UVM_MEDIUM)
            expect_alert = 1;
            expected_recov_meas_err[clk] = 1;
          end
        end else begin
          min_threshold = expected - 2;
          max_threshold = expected + 2;
        end
        enable_frequency_measurement(clk_mesr, min_threshold, max_threshold);
      end

      fork
        begin : wait_for_measurements
          fork
            maybe_saturate_count(cause_saturation, clk_mesr_e'(clk_tested));
            wait_before_read_recov_err_code(expect_alert);
          join_any
          disable fork;
        end
      join

      csr_rd(.ptr(ral.recov_err_code), .value(actual_recov_err));
      `uvm_info(`gfn, $sformatf("Expected recov err register=0x%x", expected_recov_meas_err),
                UVM_MEDIUM)
      if (!cfg.under_reset && actual_recov_err.measures != expected_recov_meas_err) begin
        report_recov_error_mismatch("measurement", expected_recov_meas_err,
                                    actual_recov_err.measures);
      end
      if (actual_recov_err.timeouts != '0) begin
        `uvm_error(`gfn, $sformatf(
                   "Unexpected recoverable timeout error 0b%b", actual_recov_err.timeouts))
      end
      if (actual_recov_err.shadow_update != 0) begin
        `uvm_error(`gfn, "Unexpected recoverable shadow update error")
      end
      // Check alerts.
      current_alert_count = cfg.scoreboard.get_alert_count("recov_fault");
      if (expect_alert) begin
        if (!cfg.under_reset) begin
          `DV_CHECK_NE(current_alert_count, prior_alert_count, "expected some alerts to fire")
        end
      end else begin
        `DV_CHECK_EQ(current_alert_count, prior_alert_count, "expected no alerts to fire")
      end

      foreach (ExpectedCounts[clk]) begin
        clk_mesr_e clk_mesr = clk_mesr_e'(clk);
        disable_frequency_measurement(clk_mesr);
      end

      // Wait enough time for measurements to complete, and for alerts to get processed
      // by the alert agents so expected alerts are properly wound down.
      cfg.aon_clk_rst_vif.wait_clks(CyclesBetweenMeasurements);
      // And clear errors.
      csr_wr(.ptr(ral.recov_err_code), .value('1));
      cfg.aon_clk_rst_vif.wait_clks(12);
    end
    // And finally, check that unsetting calib_rdy causes meaesure_ctrl_regwen to be set to 1.
    check_measure_ctrl_regwen_for_calib_rdy();
  endtask

endclass
