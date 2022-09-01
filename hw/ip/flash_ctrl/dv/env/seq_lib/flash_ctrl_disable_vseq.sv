// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test flash access disable feature by
// Global escalation : Set lc_escalate_en to On
// sw command (flash_ctrl.DIS)
class flash_ctrl_disable_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_disable_vseq)
  `uvm_object_new


  virtual task body();
    bit exp_err;

    send_rand_ops();
    set_flash_disable(exp_err);

    if (exp_err) begin
       `uvm_info("SEQ", $sformatf("assa disable is set"), UVM_MEDIUM)
       csr_utils_pkg::wait_no_outstanding_access();
       cfg.m_tl_agent_cfg.check_tl_errs = 0;
       
    end
    `uvm_info("SEQ", $sformatf("assa disable txn start"), UVM_MEDIUM)
    // mp error or tlul error expected
    
    send_rand_ops(1, exp_err);

  endtask // body

  task set_flash_disable(ref bit exp_err);
    cfg.flash_ctrl_vif.lc_escalate_en = lc_ctrl_pkg::On;

    exp_err = (cfg.flash_ctrl_vif.lc_escalate_en == lc_ctrl_pkg::On);
  endtask
endclass
