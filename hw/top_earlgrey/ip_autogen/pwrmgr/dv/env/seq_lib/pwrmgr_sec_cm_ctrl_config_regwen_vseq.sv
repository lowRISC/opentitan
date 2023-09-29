// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Decription:
// Create low power transition and wakeup a few times.
// When PWRMGR.CONTROL.LOW_POWER_HINT is set,
// issue random write to PWRMGR.CONTROL and check
// PWRMGR.CONTROL value is not changed.
class pwrmgr_sec_cm_ctrl_config_regwen_vseq extends pwrmgr_wakeup_vseq;
  `uvm_object_utils(pwrmgr_sec_cm_ctrl_config_regwen_vseq)

  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    cfg.disable_csr_rd_chk = 1;
  endtask : pre_start

  task proc_illegal_ctrl_access();
    uvm_reg_data_t wdata, expdata;
    cfg.clk_rst_vif.wait_clks(1);
    wait(cfg.pwrmgr_vif.lowpwr_cfg_wen == 0);

    repeat ($urandom_range(1, 5)) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(wdata)
      expdata = ral.control.get();
      `uvm_info(`gfn, $sformatf("csr start %x", ral.control.get()), UVM_HIGH)
      csr_wr(.ptr(ral.control), .value(wdata));
      csr_rd_check(.ptr(ral.control), .compare_value(expdata));
      `uvm_info(`gfn, "csr done", UVM_HIGH)
    end
  endtask : proc_illegal_ctrl_access

  virtual task wait_for_csr_to_propagate_to_slow_domain();
    proc_illegal_ctrl_access();
    super.wait_for_csr_to_propagate_to_slow_domain();
  endtask
endclass : pwrmgr_sec_cm_ctrl_config_regwen_vseq
