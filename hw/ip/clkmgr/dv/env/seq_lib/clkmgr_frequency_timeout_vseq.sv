// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The frequency vseq exercises the frequency measurement counters. More details
// in the clkmgr_testplan.hjson file.
class clkmgr_frequency_timeout_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_frequency_timeout_vseq)

  `uvm_object_new

  // This is measured in aon clocks. We need to have a few rounds of measurement for timeouts to
  // trigger, since they synchronize to the aon clock.
  localparam int CyclesToGetOneMeasurement = 6;

  // This is measured in clkmgr clk_i clocks. It is set to cover worst case delays.
  // The clk_i frequency is randomized for IPs, but the clkmgr is hooked to io_div4, which would
  // allow a tighter number of cycles. Leaving the clk_i random probably provides more cases,
  // so leaving it as is.
  localparam int CyclesForErrUpdate = 16;

  // If cause_timeout is set, turn off clk_timeout so it gets a timeout.
  rand bit cause_timeout;
  constraint cause_timeout_c {cause_timeout dist {1 := 4, 0 := 1};}
  rand int clk_timeout;
  constraint clk_timeout_c {clk_timeout inside {[ClkMesrIo : ClkMesrUsb]};}

  // This waits a number of cycles so that:
  // - only one measurement completes, or we could end up with multiple alerts which cause trouble
  //   for the cip exp_alert functionality, and,
  // - the measurement has had time to update the recov_err_code CSR.
  task wait_before_read_recov_err_code();
    cfg.aon_clk_rst_vif.wait_clks(CyclesToGetOneMeasurement);
    cfg.clk_rst_vif.wait_clks(CyclesForErrUpdate);
  endtask

  task body();
    logic [TL_DW-1:0] value;
    int prior_alert_count;
    int current_alert_count;
    update_csrs_with_reset_values();
    csr_wr(.ptr(ral.measure_ctrl_regwen), .value(1));

    // Make sure the aon clock is running as slow as it is meant to.
    cfg.aon_clk_rst_vif.set_freq_khz(AonClkHz / 1_000);
    // Disable cip scoreboard exp_alert checks since they need very fine control, making checks
    // really cumbersome. Instead we rely on the alert count to detect if alert were triggered.
    cfg.scoreboard.do_alert_check = 0;

    `uvm_info(`gfn, $sformatf("Will run %0d rounds", num_trans), UVM_MEDIUM)
    for (int i = 0; i < num_trans; ++i) begin
      logic [2*(ClkMesrUsb+1)-1:0] actual_recov_err = '0;
      logic [ClkMesrUsb:0] expected_recov_timeout_err = '0;
      bit expect_alert = 0;
      `DV_CHECK_RANDOMIZE_FATAL(this)
      `uvm_info(`gfn, "New round", UVM_MEDIUM)

      foreach (ExpectedCounts[clk]) begin
        clk_mesr_e clk_mesr = clk_mesr_e'(clk);
        int min_threshold;
        int max_threshold;
        int expected = ExpectedCounts[clk];
        min_threshold = expected - 1;
        max_threshold = expected + 1;
        enable_frequency_measurement(clk_mesr, min_threshold, max_threshold);
      end

      prior_alert_count = cfg.scoreboard.get_alert_count("recov_fault");
      if (cause_timeout) begin
        clk_mesr_e clk_mesr_timeout = clk_mesr_e'(clk_timeout);
        `uvm_info(`gfn, $sformatf("Will cause a timeout for clk %0s", clk_mesr_timeout.name()),
                  UVM_MEDIUM)
        expected_recov_timeout_err[clk_timeout] = 1;
        disturb_measured_clock(.clk(clk_mesr_e'(clk_timeout)), .enable(1'b0));
      end
      wait_before_read_recov_err_code();
      if (cause_timeout) disturb_measured_clock(.clk(clk_mesr_e'(clk_timeout)), .enable(1'b1));

      csr_rd(.ptr(ral.recov_err_code), .value(actual_recov_err));
      `uvm_info(`gfn, $sformatf("Got recov err register=0x%x", actual_recov_err), UVM_MEDIUM)
      if (actual_recov_err[ClkMesrUsb:0]) begin
        report_recov_error_mismatch("measurement", recov_bits_t'(0),
                                    actual_recov_err[ClkMesrUsb:0]);
      end
      if (actual_recov_err[ClkMesrUsb+1+:ClkMesrUsb+1] != expected_recov_timeout_err) begin
        report_recov_error_mismatch("timeout", expected_recov_timeout_err,
                                    actual_recov_err[ClkMesrUsb+1+:ClkMesrUsb+1]);
      end
      // And check that the alert count increased if there was a timeout.
      current_alert_count = cfg.scoreboard.get_alert_count("recov_fault");
      if (cause_timeout) begin
        `DV_CHECK_NE(current_alert_count, prior_alert_count, "expected some alerts to fire")
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
  endtask

endclass
