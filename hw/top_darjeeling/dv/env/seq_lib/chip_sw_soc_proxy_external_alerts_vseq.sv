// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_soc_proxy_external_alerts_vseq extends chip_sw_base_vseq;

  `uvm_object_utils(chip_sw_soc_proxy_external_alerts_vseq)

  `uvm_object_new

  task pre_start();
    expect_fatal_alerts = 1'b1;
    super.pre_start();
  endtask

  task await_soc_proxy_wkup_internal_req();
    `uvm_info(`gfn, $sformatf("Waiting for internal wakeup request."), UVM_MEDIUM)
    `DV_SPINWAIT_EXIT(
      // Wait thread: wait for internal wakeup request.
      forever begin
        cfg.chip_vif.cpu_clk_rst_if.wait_clks(1);
        if (cfg.chip_vif.signal_probe_soc_proxy_wkup_internal_req(
                .kind(dv_utils_pkg::SignalProbeSample)) == 1'b1) break;
      end
      ,
      // Exit thread: allow at most 20 AON clock cycles for internal wakeup request.
      cfg.chip_vif.aon_clk_por_rst_if.wait_clks(20);
      `dv_error("Internal wakeup request did not follow within required time!")
    )
  endtask

  virtual task body();
    super.body();

    // Allow one more SW execution than fatal alerts, since a reset will be triggered after every
    // fatal alert.
    cfg.sw_test_status_vif.set_num_iterations(soc_proxy_pkg::NumFatalExternalAlerts + 1);

    // Test external fatal alerts one after the other.  Note that the `<=` intentionally means that
    // this loop starts one time more than there are fatal alerts.  However, in the last iteration
    // the loop body terminates early, immediately after the check for the last fatal alert.
    for (int unsigned i = 0; i <= soc_proxy_pkg::NumFatalExternalAlerts; i++) begin
      logic [2 * soc_proxy_pkg::NumFatalExternalAlerts - 1:0] alert_rsp;
      logic [2 * soc_proxy_pkg::NumFatalExternalAlerts - 1:0] alert_req =
          {soc_proxy_pkg::NumFatalExternalAlerts{2'b01}};
      alert_req[2 * i +: 2] = 2'b10;

      // If this is not the first fatal alert, wait for the CPU to confirm that the expected alert
      // was registered before the latest reset.
      if (i > 0) begin
        int unsigned exp_alert_id =
            top_darjeeling_pkg::TopDarjeelingAlertIdSocProxyFatalAlertExternal0 + i - 1;
        `uvm_info(`gfn, $sformatf("Waiting for alert ID %0d.", exp_alert_id), UVM_MEDIUM)
        `DV_WAIT(cfg.sw_logger_vif.printed_log ==
                 $sformatf("Alert ID %0d registered before latest reset.", exp_alert_id))
      end

      // If this is the 'extra' iteration (see comment above), terminate loop now.
      if (i == soc_proxy_pkg::NumFatalExternalAlerts) break;

      // Wait until the CPU has configured Alert Handler.
      `uvm_info(`gfn, $sformatf("Waiting for alert handler config."), UVM_MEDIUM)
      `DV_WAIT(cfg.sw_logger_vif.printed_log == "Alert handler configured.")

      // Trigger the alert.
      `uvm_info(`gfn, $sformatf("Triggering fatal alert %0d.", i), UVM_LOW)
      void'(cfg.chip_vif.signal_probe_soc_fatal_alert_req(.kind(dv_utils_pkg::SignalProbeForce),
                                                          .value(alert_req)));

      // Ensure that the alert gets acknowledged.
      cfg.chip_vif.cpu_clk_rst_if.wait_clks(2);
      alert_rsp =
          cfg.chip_vif.signal_probe_soc_fatal_alert_rsp(.kind(dv_utils_pkg::SignalProbeSample));
      `DV_CHECK_EQ(alert_rsp, alert_req, "Alert response incorrect!")

      // Ensure that an internal wakeup request is raised.
      await_soc_proxy_wkup_internal_req();

      // Ensure that a reset is asserted (after Alert Handler escalates to Power Manager).
      `DV_SPINWAIT(cfg.chip_vif.cpu_clk_rst_if.wait_for_reset(.wait_negedge(1'b1),
                                                              .wait_posedge(1'b0));,
                   "Timeout waiting for reset assertion after escalation!")
      `uvm_info(`gfn, $sformatf("CPU reset asserted."), UVM_MEDIUM)

      // Release the alert.
      void'(cfg.chip_vif.signal_probe_soc_fatal_alert_req(.kind(dv_utils_pkg::SignalProbeRelease)));

      // Wait for reset release.
      `DV_SPINWAIT(cfg.chip_vif.cpu_clk_rst_if.wait_for_reset(.wait_negedge(1'b0),
                                                              .wait_posedge(1'b1));,
                   "Timeout waiting for reset release!")
      `uvm_info(`gfn, $sformatf("CPU reset released."), UVM_MEDIUM)
    end

    // Test recoverable alerts one after the other.
    for (int unsigned i = 0; i < soc_proxy_pkg::NumRecovExternalAlerts; i++) begin
      logic [2 * soc_proxy_pkg::NumRecovExternalAlerts - 1:0] alert_rsp;
      int unsigned exp_alert_id =
          top_darjeeling_pkg::TopDarjeelingAlertIdSocProxyRecovAlertExternal0 + i;
      logic [2 * soc_proxy_pkg::NumRecovExternalAlerts - 1:0] alert_req =
          {soc_proxy_pkg::NumRecovExternalAlerts{2'b01}};
      alert_req[2 * i +: 2] = 2'b10;

      // Wait until the CPU has configured Alert Handler.
      `uvm_info(`gfn, $sformatf("Waiting for alert handler config."), UVM_MEDIUM)
      `DV_WAIT(cfg.sw_logger_vif.printed_log == "Alert handler configured.")

      // Trigger the alert.
      `uvm_info(`gfn, $sformatf("Triggering recoverable alert %0d.", i), UVM_LOW)
      void'(cfg.chip_vif.signal_probe_soc_recov_alert_req(.kind(dv_utils_pkg::SignalProbeForce),
                                                          .value(alert_req)));

      // Ensure that the alert gets acknowledged.
      cfg.chip_vif.cpu_clk_rst_if.wait_clks(2);
      alert_rsp =
          cfg.chip_vif.signal_probe_soc_recov_alert_rsp(.kind(dv_utils_pkg::SignalProbeSample));
      `DV_CHECK_EQ(alert_rsp, alert_req, "Alert response incorrect!")

      fork
        begin
          // Ensure that an internal wakeup request is raised.
          await_soc_proxy_wkup_internal_req();
        end
        begin
          // Wait for SW to confirm the alert.
          `uvm_info(`gfn, $sformatf("Waiting for alert ID %0d.", exp_alert_id), UVM_MEDIUM)
          `DV_WAIT(cfg.sw_logger_vif.printed_log == $sformatf("Alert ID %0d is cause.",
                                                              exp_alert_id))
        end
      join

      // Release the alert.
      void'(cfg.chip_vif.signal_probe_soc_recov_alert_req(.kind(dv_utils_pkg::SignalProbeRelease)));
    end
  endtask

endclass
