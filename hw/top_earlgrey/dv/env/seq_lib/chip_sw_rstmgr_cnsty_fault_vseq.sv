// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This triggers a TopEarlgreyAlertIdRstmgrAonFatalCnstyFault fault and checks
// the expected behavior. The test strategy is to cause an unexpected child lc
// reset via force, which will cause the reset consistency checkers to fail and
// cause a fatal error.

class chip_sw_rstmgr_cnsty_fault_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_rstmgr_cnsty_fault_vseq)

  `uvm_object_new

  virtual task body();
    sec_cm_pkg::sec_cm_base_if_proxy if_proxy;
    // This is a specific rstmgr_leaf_rst that generates lc_reset.
    string if_path = "*rstmgr_aon.u_d0_spi_host0*";
    int alert_id = TopEarlgreyAlertIdRstmgrAonFatalCnstyFault;
    bit [7:0] sw_alert_num[];

    // This sequence will trigger a fatal sec_cm failure.
    super.body();

    `uvm_info(`gfn, $sformatf(
              "Will inject fault for %s, expecting alert %0d", if_path, alert_id),
              UVM_MEDIUM)

    // Disable scoreboard tl error checks since we will trigger faults which cannot be predicted.
    cfg.en_scb_tl_err_chk = 0;

    // Let SW know the expected alert.
    sw_alert_num = {alert_id};
    sw_symbol_backdoor_overwrite("kExpectedAlertNumber", sw_alert_num);

    if_proxy = sec_cm_pkg::find_sec_cm_if_proxy(.path(if_path), .is_regex(1));
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Ready for fault injection",
             "Timeout waiting for fault injection request.")

    `uvm_info(`gfn, $sformatf(
              "Injecting fault for IP %s, with alert %0d", if_proxy.path, alert_id), UVM_MEDIUM)
    if_proxy.inject_fault();
  endtask
endclass
