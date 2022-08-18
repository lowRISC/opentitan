// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_clkmgr_escalation_reset_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_clkmgr_escalation_reset_vseq)

  `uvm_object_new

  virtual task body();
    sec_cm_pkg::sec_cm_base_if_proxy if_proxy;

    // This sequence will trigger a fatal sec_cm failure.
    super.body();

    `uvm_info(`gfn, "Waiting to inject error", UVM_MEDIUM)
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Ready for error injection",
             "Timeout waiting for error injection request.")

    // TODO: Find a better way to pass the path. Referencing full chip hierarchies in UVM code
    // is generally not a good idea.
    if_proxy = sec_cm_pkg::find_sec_cm_if_proxy(
        "tb.dut.top_earlgrey.u_clkmgr_aon.u_clk_main_aes_trans.u_idle_cnt");
    if_proxy.inject_fault();
   endtask
endclass
