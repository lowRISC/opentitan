// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence creates the following check failure scenarios:
// 1. Check timeout
// 2. Correctable ECC check error
// 3. TODO: add when support
class otp_ctrl_check_fail_vseq extends otp_ctrl_dai_lock_vseq;
  `uvm_object_utils(otp_ctrl_check_fail_vseq)

  `uvm_object_new

  constraint ecc_otp_err_c {
    ecc_otp_err inside {OtpEccCorrErr, OtpNoEccErr};
  }

  constraint ecc_chk_err_c {
    // TODO: currently only max to 1 error bits, once implemetned ECC in mem_bkdr_util, we can
    // fully randomize num of error bits
    ecc_chk_err dist {OtpNoEccErr   :/ 1,
                      OtpEccCorrErr :/ 1};
  }

  // 50% chance of having a check timeout
  constraint check_timeout_val_c {
    check_timeout_val dist {[1 : CHK_TIMEOUT_CYC] :/ 1,
                            [100_000 :'1]         :/ 1};
  }

endclass
