// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The frequency timeout vseq exercises the frequency measurement counters. More details
// in the clkmgr_testplan.hjson file.
class clkmgr_frequency_timeout_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_frequency_timeout_vseq)

  `uvm_object_new

  // This is measured in aon clocks. We need to have a few rounds of measurement for timeouts to
  // trigger, since they synchronize to the aon clock, and they wait for a few number of AON
  // cycles before declaring a timeout.
  localparam int CyclesToGetOneMeasurement = 12;

  // If cause_timeout is set, turn off clk_timeout so it gets a timeout.
  rand bit cause_timeout;
  constraint cause_timeout_c {
    cause_timeout dist {
      1 := 4,
      0 := 1
    };
  }
  rand int clk_timeout;
  constraint clk_timeout_c {clk_timeout inside {[ClkMesrIo : ClkMesrUsb]};}

  constraint all_clk_en_c {
    io_ip_clk_en == 1;
    main_ip_clk_en == 1;
    usb_ip_clk_en == 1;
  }

  // The clock that will be disabled.
  clk_mesr_e clk_mesr_timeout;

  // This waits a number of AON cycles so that the timeout can get detected.
  task wait_before_read_recov_err_code();
    cfg.aon_clk_rst_vif.wait_clks(CyclesToGetOneMeasurement);
  endtask

  // Get things back in normal order.
  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    super.apply_resets_concurrently(reset_duration_ps);
    if (cause_timeout) disturb_measured_clock(.clk(clk_mesr_timeout), .enable(1'b1));
  endtask

  task body();
    logic [TL_DW-1:0] value;
    int prior_alert_count;
    int current_alert_count;
    csr_wr(.ptr(ral.measure_ctrl_regwen), .value(1));

    // Make sure the aon clock is running as slow as it is meant to.
    cfg.aon_clk_rst_vif.set_freq_khz(AonClkHz / 1_000);
    control_ip_clocks();
    // Wait so the frequency change takes effect.
    cfg.aon_clk_rst_vif.wait_clks(2);

    // Disable cip scoreboard exp_alert checks since they need very fine control, making checks
    // really cumbersome. Instead we rely on the alert count to detect if alert were triggered.
    cfg.scoreboard.do_alert_check = 0;

    `uvm_info(`gfn, $sformatf("Will run %0d rounds", num_trans), UVM_MEDIUM)
    for (int i = 0; i < num_trans; ++i) begin
      clkmgr_recov_err_t actual_recov_err = '{default: '0};
      logic [ClkMesrUsb:0] expected_recov_timeout_err = '0;
      bit expect_alert = 0;
      `DV_CHECK_RANDOMIZE_FATAL(this)
      `uvm_info(`gfn, "New round", UVM_MEDIUM)

      foreach (ExpectedCounts[clk]) begin
        clk_mesr_e clk_mesr = clk_mesr_e'(clk);
        int min_threshold;
        int max_threshold;
        int expected = ExpectedCounts[clk];
        min_threshold = expected - 2;
        max_threshold = expected + 2;
        enable_frequency_measurement(clk_mesr, min_threshold, max_threshold);
      end

      prior_alert_count = cfg.scoreboard.get_alert_count("recov_fault");
      // Allow some cycles for measurements to start before turning off the clocks, since the
      // measurement control CSRs are controlled by the clocks we intend to stop.
      cfg.aon_clk_rst_vif.wait_clks(4);
      clk_mesr_timeout = clk_mesr_e'(clk_timeout);

      if (cause_timeout) begin
        `uvm_info(`gfn, $sformatf("Will cause a timeout for clk %0s", clk_mesr_timeout.name()),
                  UVM_MEDIUM)
        if (clk_mesr_timeout inside {ClkMesrIo, ClkMesrIoDiv2, ClkMesrIoDiv4}) begin
          // All these clocks are derived from io so that gets disabled, and all derived
          // clocks will get a timeout.
          expected_recov_timeout_err[ClkMesrIo] = 1;
          expected_recov_timeout_err[ClkMesrIoDiv2] = 1;
          expected_recov_timeout_err[ClkMesrIoDiv4] = 1;
        end else begin
          expected_recov_timeout_err[clk_mesr_timeout] = 1;
        end
        disturb_measured_clock(.clk(clk_mesr_timeout), .enable(1'b0));
      end
      wait_before_read_recov_err_code();
      if (cause_timeout) begin
        disturb_measured_clock(.clk(clk_mesr_e'(clk_timeout)), .enable(1'b1));
      end
      csr_rd(.ptr(ral.recov_err_code), .value(actual_recov_err));
      `uvm_info(`gfn, $sformatf("Got recov err register=0x%x", actual_recov_err), UVM_MEDIUM)
      if (actual_recov_err.measures) begin
        report_recov_error_mismatch("measurement", recov_bits_t'(0), actual_recov_err.measures);
      end
      if (!cfg.under_reset && actual_recov_err.timeouts != expected_recov_timeout_err) begin
        report_recov_error_mismatch("timeout", expected_recov_timeout_err,
                                    actual_recov_err.timeouts);
      end
      if (actual_recov_err.shadow_update != 0) begin
        `uvm_error(`gfn, "Unexpected recoverable shadow update error")
      end
      // And check that the alert count increased if there was a timeout.
      current_alert_count = cfg.scoreboard.get_alert_count("recov_fault");
      if (cause_timeout) begin
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
      cfg.aon_clk_rst_vif.wait_clks(6);
      // And clear errors.
      csr_wr(.ptr(ral.recov_err_code), .value('1));
      cfg.aon_clk_rst_vif.wait_clks(2);
    end
  endtask : body

endclass
