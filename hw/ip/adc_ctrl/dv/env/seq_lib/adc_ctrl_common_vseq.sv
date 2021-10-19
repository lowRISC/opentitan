// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class adc_ctrl_common_vseq extends adc_ctrl_base_vseq;
  `uvm_object_utils(adc_ctrl_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task body();
    run_common_vseq_wrapper(num_trans);
    // Short delay to prevent register CDC assertions triggering at the end of test
    cfg.clk_aon_rst_vif.wait_clks(3);
  endtask : body

endclass
