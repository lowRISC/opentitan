// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence creates the following check failure scenarios:
// 1. Check timeout
// 2. Correctable ECC check error
// 3. TODO: add when support
class otp_ctrl_check_fail_vseq extends otp_ctrl_dai_errs_vseq;
  `uvm_object_utils(otp_ctrl_check_fail_vseq)

  `uvm_object_new

  constraint ecc_chk_err_c {
    // TODO: currently only max to 1 error bits, once implemetned ECC in mem_bkdr_if, we can
    // fully randomize num of error bits
    $countones(ecc_chk_err_mask) dist {0 :/ 1,
                                       1 :/ 1};
  }

  // 50% chance of having a check timeout
  constraint check_timeout_val_c {
    $countones(ecc_chk_err_mask) == 0 -> check_timeout_val dist {[1 : CHK_TIMEOUT_CYC] :/ 1,
                                                                 [100_000 :'1]         :/ 1};
    $countones(ecc_chk_err_mask) == 1 -> check_timeout_val inside {[100_000 :'1]};
  }

endclass
