// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test SW invalid input error by setting key_version > current_max_key_ver
class keymgr_sw_invalid_input_vseq extends keymgr_random_vseq;
  `uvm_object_utils(keymgr_sw_invalid_input_vseq)
  `uvm_object_new

  // enable key_version error with 1/3 chance
  constraint is_key_version_err_c {
    is_key_version_err dist {0 :/ 2, 1 :/ 1};
  }

endclass : keymgr_sw_invalid_input_vseq
