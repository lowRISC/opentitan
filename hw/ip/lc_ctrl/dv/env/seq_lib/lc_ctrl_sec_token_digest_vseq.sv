// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Token mux error injection test

class lc_ctrl_sec_token_digest_vseq extends lc_ctrl_errors_vseq;

  `uvm_object_utils(lc_ctrl_sec_token_digest_vseq)
  `uvm_object_new

  constraint num_trans_c {num_trans inside {[50 : 100]};}

  // Enable err_inj.token_mismatch_err and disable the others
  constraint lc_errors_c {
    err_inj.transition_err == 0;
    err_inj.transition_count_err == 0;
    err_inj.clk_byp_error_rsp == 0;
    err_inj.flash_rma_error_rsp == 0;
    err_inj.token_response_err == 0;
    err_inj.token_invalid_err == 0;
    err_inj.otp_partition_err == 0;
  }

  constraint lc_token_digest_c {
    $onehot(
        {
          // Either wrong token for transition
          err_inj.token_mismatch_err,
          // Or bit errors in token during state transition
          err_inj.token_mux_digest_err
        }
    );
  }



endclass
