// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class adc_ctrl_common_vseq extends adc_ctrl_base_vseq;
  `uvm_object_utils(adc_ctrl_common_vseq)

  constraint num_trans_c {num_trans inside {[1 : 2]};}
  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    // Disable ADC_CTRL FSM assertions
    `DV_ASSERT_CTRL_REQ("ADC_CTRL_FSM_A_CTRL", 0)
  endtask

  virtual task post_start();
    super.post_start();
    // Re-enable ADC_CTRL FSM assertions
    `DV_ASSERT_CTRL_REQ("ADC_CTRL_FSM_A_CTRL", 1)
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
    // Make sure we have valid values in np_sample_cnt lp_sample_cnt to stop assertions firing
    // Write the reset values
    csr_wr(ral.adc_sample_ctl, ral.adc_sample_ctl.get_reset());
    csr_wr(ral.adc_lp_sample_ctl, ral.adc_lp_sample_ctl.get_reset());
    // Short delay to prevent register CDC assertions triggering at the end of test
    cfg.clk_aon_rst_vif.wait_clks(3);
  endtask : body

endclass
