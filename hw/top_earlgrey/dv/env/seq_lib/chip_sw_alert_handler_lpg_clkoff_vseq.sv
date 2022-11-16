// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_alert_handler_lpg_clkoff_vseq extends
      chip_sw_alert_handler_shorten_ping_wait_cycle_vseq;
  `uvm_object_utils(chip_sw_alert_handler_lpg_clkoff_vseq)

  `uvm_object_new

  typedef alert_id_e alert_ids_t[];

  // The list of IPs tested in this test. This enumeration must match the array in
  // sw/device/tests/alert_handler_lpg_clkoff_test.c::kPeripherals[].
  alert_ids_t IpAlertsUnderTest[string] = '{
      "AES":       '{TopEarlgreyAlertIdAesRecovCtrlUpdateErr, TopEarlgreyAlertIdAesFatalFault},
      "HMAC":      '{TopEarlgreyAlertIdHmacFatalFault},
      "KMAC":      '{TopEarlgreyAlertIdKmacRecovOperationErr, TopEarlgreyAlertIdKmacFatalFaultErr},
      "OTBN":      '{TopEarlgreyAlertIdOtbnFatal, TopEarlgreyAlertIdOtbnRecov},
      "SPI_HOST0": '{TopEarlgreyAlertIdSpiHost0FatalFault},
      "SPI_HOST1": '{TopEarlgreyAlertIdSpiHost1FatalFault},
      "USB":       '{TopEarlgreyAlertIdUsbdevFatalFault}
   };

  virtual function void write_test_done_to_sw(int idx);
    sw_symbol_backdoor_overwrite("kTestIp", {<<8{idx}});
  endfunction

  virtual task body();
    int i = 0;
    super.body();
    foreach (IpAlertsUnderTest[ip_name]) begin

      // Wait for design to turn off the IP clock.
      `uvm_info(`gfn, $sformatf("Waiting for alert ping %0s", ip_name), UVM_LOW)
      `DV_WAIT(cfg.sw_logger_vif.printed_log == $sformatf("Turn off %0s clock", ip_name))

      fork begin : isolation_fork
        alert_ids_t list_of_alerts = IpAlertsUnderTest[ip_name];
        foreach (list_of_alerts[j]) begin
          automatic alert_id_e alert_idx = list_of_alerts[j];
          fork
            begin
              bit [alert_pkg::NAlerts-1:0] alert_reqs;
              // Wait for alert_handler to send the ping request(s) to prim_alert_receiver.
              // If the alert_reqs were not set in certain timeout limit, the SW wait function
              // will timeout.
              while (alert_reqs[alert_idx] == 0) begin
                @(negedge cfg.chip_vif.alerts_if.clk);
                alert_reqs = cfg.chip_vif.signal_probe_alert_handler_ping_reqs(SignalProbeSample);
                @(posedge cfg.chip_vif.alerts_if.clk);
              end
              `uvm_info(`gfn, $sformatf("Alert ping %0s triggered", alert_idx.name), UVM_LOW)
            end
          join_none
        end
        wait fork;
        `uvm_info(`gfn, $sformatf("All alerts pings triggered in %0s", ip_name), UVM_LOW)

        // Write ip index + 1 because the default value for `kTestIp` is 0.
        i++;
        write_test_done_to_sw(i);
      end join
    end
  endtask

endclass
