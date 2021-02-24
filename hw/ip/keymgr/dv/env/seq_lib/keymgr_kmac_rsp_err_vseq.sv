// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test these 2 types error cases, also combine with hw/sw invalid input
// 1. invalid kmac operation - The KMAC module itself reported an error.
// 2. invalid output - The data return from KMAC is all 0’s or all 1’s.
class keymgr_kmac_rsp_err_vseq extends keymgr_hwsw_invalid_input_vseq;
  `uvm_object_utils(keymgr_kmac_rsp_err_vseq)
  `uvm_object_new

  // enable key_version error with 1/5 chance
  constraint is_key_version_err_c {
    is_key_version_err dist {0 :/ 9, 1 :/ 1};
  }

  // enable HW invalid input
  constraint num_invalid_hw_input_c {
    num_invalid_hw_input dist {0     :/ 18,
                               1     :/ 1,
                               [2:6] :/ 1};
  }

  task pre_start();
    cfg.m_keymgr_kmac_agent_cfg.error_rsp_pct = 20;

    // fatal alert will be triggered, need reset to clear it
    do_reset_at_end_of_seq = 1;
    super.pre_start();
  endtask

endclass : keymgr_kmac_rsp_err_vseq
