// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Based on the `sysrst_ctrl_combo_detect_ec_rst_vseq`, this sequence will configure
// a pre-condition to enable the combo-detection.
class sysrst_ctrl_combo_detect_ec_rst_with_pre_cond_vseq extends
      sysrst_ctrl_combo_detect_ec_rst_vseq;
  `uvm_object_utils(sysrst_ctrl_combo_detect_ec_rst_with_pre_cond_vseq)

  `uvm_object_new

  uint pre_cond_detect_timer = 1;

  virtual task drive_input();
    // Wait for the pre_condition debounce and detect time to be satisfied.
    cfg.clk_aon_rst_vif.wait_clks(debounce_timer + pre_cond_detect_timer + 1);
    super.drive_input();
  endtask

  task body();
    `uvm_info(`gfn, "Starting to setup pre-conditions", UVM_LOW)

    // Enable pwrb_in to trigger pre-condition.
    ral.com_pre_sel_ctl[0].pwrb_in_sel.set(1'b1);
    csr_update(ral.com_pre_sel_ctl[0]);

    // Configure the pre_condition detect timer.
    csr_wr(ral.com_pre_det_ctl[0], pre_cond_detect_timer);

    super.body();
  endtask : body

endclass : sysrst_ctrl_combo_detect_ec_rst_with_pre_cond_vseq
