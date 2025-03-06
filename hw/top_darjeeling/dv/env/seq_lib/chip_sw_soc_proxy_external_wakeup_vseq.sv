// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_soc_proxy_external_wakeup_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_soc_proxy_external_wakeup_vseq)

  `uvm_object_new

  virtual task body();
    super.body();

    // Wait until SW reaches the test state.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Power Manager configured.")
    `uvm_info(`gfn, $sformatf("Waiting for WFI"), UVM_LOW)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)
    cfg.chip_vif.aon_clk_por_rst_if.wait_clks(1);

    // Trigger the external wakeup request.
    `uvm_info(`gfn, $sformatf("Triggering external wakeup request"), UVM_LOW)
    void'(cfg.chip_vif.signal_probe_soc_wkup_async(.kind(dv_utils_pkg::SignalProbeForce),
                                                   .value(1'b1)));

    // Wait for software to confirm external wakeup request.
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "External wakeup request detected.")

    // Release the external wakeup request.
    void'(cfg.chip_vif.signal_probe_soc_wkup_async(.kind(dv_utils_pkg::SignalProbeRelease)));
  endtask
endclass
