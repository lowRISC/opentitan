// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Attempt second transition before reset
class lc_ctrl_state_post_trans_vseq extends lc_ctrl_errors_vseq;

  `uvm_object_utils(lc_ctrl_state_post_trans_vseq)
  `uvm_object_new

  constraint num_trans_c {num_trans inside {[10 : 15]};}
  constraint post_trans_c {
    err_inj.post_trans_err == 1;
    // Allow for post_trans_err plus one other error
    // 50% just post_trans_err
    // 50% post_trans_err plus another error for first tranistion attempt
    $countones(
        err_inj
    ) dist {
      1 := 1,
      2 := 1
    };
  }

  constraint lc_state_failure_c {}

endclass
