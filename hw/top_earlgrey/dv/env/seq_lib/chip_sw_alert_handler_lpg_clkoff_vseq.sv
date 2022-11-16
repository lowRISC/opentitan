// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_alert_handler_lpg_clkoff_vseq extends
      chip_sw_alert_handler_shorten_ping_wait_cycle_vseq;
  `uvm_object_utils(chip_sw_alert_handler_lpg_clkoff_vseq)

  `uvm_object_new

  parameter uint NUM_IPS = 7;

  typedef struct {
    string name;
    alert_id_e alert_idxs[$];
  } ip_info_t;

  // The list of IPs tested in this test. This enumeration must match the array in
  // sw/device/tests/alert_handler_lpg_clkoff_test.c::kPeripherals[].
  ip_info_t ip_test_infos[NUM_IPS] = {
    {
      name: "AES",
      alert_idxs: {TopEarlgreyAlertIdAesRecovCtrlUpdateErr, TopEarlgreyAlertIdAesFatalFault}
    },
    {
      name: "HMAC",
      alert_idxs: {TopEarlgreyAlertIdHmacFatalFault}
    },
    {
      name: "KMAC",
      alert_idxs: {TopEarlgreyAlertIdKmacRecovOperationErr, TopEarlgreyAlertIdKmacFatalFaultErr}
    },
    {
      name: "OTBN",
      alert_idxs: {TopEarlgreyAlertIdKmacFatalFaultErr, TopEarlgreyAlertIdOtbnRecov}
    },
    {
      name: "SPI_HOST0",
      alert_idxs: {TopEarlgreyAlertIdSpiHost0FatalFault}
    },
    {
      name: "SPI_HOST1",
      alert_idxs: {TopEarlgreyAlertIdSpiHost1FatalFault}
    },
    {
      name: "USB",
      alert_idxs: {TopEarlgreyAlertIdUsbdevFatalFault}
    }
  };

  virtual function void write_test_done_to_sw(int idx);
    sw_symbol_backdoor_overwrite("kTestIp", {<<8{idx}});
  endfunction

  virtual task body();
    super.body();
    for (int i = 0; i < NUM_IPS; i++) begin
      string ip_name = ip_test_infos[i].name;

      // Wait for design to turn off the IP clock.
      `DV_WAIT(cfg.sw_logger_vif.printed_log == $sformatf("Turn off %0s clock", ip_name))

      fork begin : isolation_fork
        foreach (ip_test_infos[i].alert_idxs[j]) begin
          automatic alert_id_e alert_idx = ip_test_infos[i].alert_idxs[j];
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
        write_test_done_to_sw(i+1);
      end join
    end
  endtask

endclass
