// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// State failure test sequence
class lc_ctrl_state_failure_vseq extends lc_ctrl_errors_vseq;
  `uvm_object_utils(lc_ctrl_state_failure_vseq)

  `uvm_object_new

  constraint num_trans_c {num_trans inside {[50 : 100]};}

  constraint lc_state_failure_c {
    $onehot(
        {
          err_inj.state_err,
          err_inj.state_illegal_err,
          err_inj.state_backdoor_err,
          err_inj.count_err,
          err_inj.count_illegal_err,
          err_inj.count_backdoor_err,
          err_inj.lc_fsm_backdoor_err,
          err_inj.kmac_fsm_backdoor_err,
          err_inj.otp_lc_data_i_valid_err
        }
    );

  }
endclass
