// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// MUBI inputs error injection test

class lc_ctrl_sec_mubi_vseq extends lc_ctrl_errors_vseq;

  `uvm_object_utils(lc_ctrl_sec_mubi_vseq)
  `uvm_object_new

  constraint num_trans_c {num_trans inside {[50 : 100]};}

  constraint mubi_err_inj_c {
    $onehot(
        {
          err_inj.clk_byp_rsp_mubi_err,
          err_inj.flash_rma_rsp_mubi_err,
          err_inj.otp_secrets_valid_mubi_err,
          err_inj.otp_test_tokens_valid_mubi_err,
          err_inj.otp_rma_token_valid_mubi_err
        }
    );
  }

endclass
