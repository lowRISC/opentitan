// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This is base sequence for top level fault injection.
// User can set following parameters
// if_path : hierarchical path to inject fault
// alert_id : alert to be triggerred. Use enum
//            defined in hw/top_earlgrey/rtl/autogen/top_earlgrey_pkg.sv

class chip_sw_fault_base_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_fault_base_vseq)
  `uvm_object_new

  string if_path;
  int    alert_id;
  sec_cm_pkg::sec_cm_base_if_proxy if_proxy;

  // This function should be overriden and set if_path and alert_id.
  virtual function void set_fault_parameters();
  endfunction : set_fault_parameters

  virtual task wait_event();
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Ready for fault injection",
             "Timeout waiting for fault injection request.")
  endtask : wait_event

  virtual task body();
    bit [7:0] sw_alert_num[];

    // This sequence will trigger a fatal sec_cm failure.
    super.body();
    set_fault_parameters();
    `uvm_info(`gfn, $sformatf(
              "Will inject fault for %s, expecting alert %0d", if_path, alert_id),
              UVM_MEDIUM)

    // Disable scoreboard tl error checks since we will trigger faults which cannot be predicted.
    cfg.en_scb_tl_err_chk = 0;

    // Let SW know the expected alert.
    sw_alert_num = {alert_id};
    sw_symbol_backdoor_overwrite("kExpectedAlertNumber", sw_alert_num);

    if_proxy = sec_cm_pkg::find_sec_cm_if_proxy(.path(if_path), .is_regex(1));
    wait_event();
    `uvm_info(`gfn, $sformatf(
              "Injecting fault for IP %s, with alert %0d", if_proxy.path, alert_id), UVM_MEDIUM)
    if_proxy.inject_fault();

  endtask : body

endclass
