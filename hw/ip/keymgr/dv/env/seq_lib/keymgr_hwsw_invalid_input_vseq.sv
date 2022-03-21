// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test below HW invalid input, also combine with SW invalid input
// 1. During Initialized state, creator seed, device ID and health state data is checked for all 0's
// and all 1's.
// 2. During CreatorRootKey state, the owner seed is checked for all 0's and all 1's.
class keymgr_hwsw_invalid_input_vseq extends keymgr_sw_invalid_input_vseq;
  `uvm_object_utils(keymgr_hwsw_invalid_input_vseq)
  `uvm_object_new

  // enable key_version error with 1/5 chance
  constraint is_key_version_err_c {
    is_key_version_err dist {0 :/ 4, 1 :/ 1};
  }

  // enable HW invalid input
  constraint num_invalid_hw_input_c {
    num_invalid_hw_input dist {0     :/ 1,
                               1     :/ 1,
                               [2:6] :/ 1};
  }

  // disable checker in seq, only check in scb
  virtual function bit get_check_en();
    return 0;
  endfunction

  task body();
    // invalid HW input may cause unstable data on kmac interface
    $assertoff(0, "tb.keymgr_kmac_intf.req_data_if.H_DataStableWhenValidAndNotReady_A");
    super.body();
  endtask : body
endclass : keymgr_hwsw_invalid_input_vseq
