// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_clkmgr_escalation_reset_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_clkmgr_escalation_reset_vseq)

  `uvm_object_new

  virtual task body();
    // This sequence will trigger a fatal sec_cm failure.
    super.body();

    `uvm_info(`gfn, "Waiting to inject error", UVM_MEDIUM)
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Ready for error injection",
             "Timeout waiting for error injection request.")
    cfg.clkmgr_prim_count_vif.if_proxy.inject_fault();
   endtask
endclass
