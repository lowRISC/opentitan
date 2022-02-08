// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Error injection and checks for:
// Invalid transition
// Transition count = 24
// Clock bypass invalid response
// Flash RMA invalid response
// Incorrect token for transition
// OTP partition error

class lc_ctrl_lc_errors_vseq extends lc_ctrl_errors_vseq;

  `uvm_object_utils(lc_ctrl_lc_errors_vseq)
  `uvm_object_new

  constraint num_trans_c {num_trans inside {[50 : 100]};}

  constraint lc_errors_c {
    $onehot(
        {
          err_inj.transition_err,
          err_inj.transition_count_err,
          err_inj.clk_byp_error_rsp,
          err_inj.flash_rma_error_rsp,
          err_inj.token_mismatch_err,
          err_inj.token_invalid_err,
          err_inj.token_response_err,
          err_inj.otp_partition_err
        }
    );
  }
endclass
