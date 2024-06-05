// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Decription:
// Create low power transition and wakeup a few times.
// When PWRMGR.CONTROL.LOW_POWER_HINT is set and core_sleep is high,
// issue random write to PWRMGR.CONTROL and check
// PWRMGR.CONTROL value is not changed, except for LOW_POWER_HINT.
class pwrmgr_sec_cm_ctrl_config_regwen_vseq extends pwrmgr_wakeup_vseq;
  `uvm_object_utils(pwrmgr_sec_cm_ctrl_config_regwen_vseq)

  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    cfg.disable_csr_rd_chk = 1;
  endtask : pre_start

  task proc_illegal_ctrl_access();
    uvm_reg_data_t wdata, expdata, compare_mask;
    // CONTROL.LOW_POWER_HINT is hardware-writeable, so mask it from checking.
    // It gets cleared very quickly.
    compare_mask = '1;
    compare_mask = compare_mask - ral.control.low_power_hint.get_field_mask();

    cfg.clk_rst_vif.wait_clks(1);
    wait(cfg.pwrmgr_vif.lowpwr_cfg_wen == 0);

    repeat ($urandom_range(1, 5)) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(wdata)
      expdata = ral.control.get();
      `uvm_info(`gfn, $sformatf("csr start %x", ral.control.get()), UVM_HIGH)
      csr_wr(.ptr(ral.control), .value(wdata));
      csr_rd_check(.ptr(ral.control), .compare_value(expdata), .compare_mask(compare_mask));
      `uvm_info(`gfn, "csr done", UVM_HIGH)
    end
  endtask : proc_illegal_ctrl_access

  virtual task initiate_low_power_transition();
    super.initiate_low_power_transition();
    // The access checks can only happen if the bus is powered and the clock
    // is active.
    if ((ral.control.main_pd_n.get_mirrored_value() == 1'b1) &&
        (ral.control.io_clk_en.get_mirrored_value() == 1'b1)) begin
      proc_illegal_ctrl_access();
    end
  endtask
endclass : pwrmgr_sec_cm_ctrl_config_regwen_vseq
