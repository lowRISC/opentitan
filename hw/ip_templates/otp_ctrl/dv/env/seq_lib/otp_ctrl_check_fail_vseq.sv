// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence creates the following check failure scenarios:
// 1. Check timeout
// 2. Correctable ECC check error
// 3. Uncorrectable ECC error
class otp_ctrl_check_fail_vseq extends otp_ctrl_dai_lock_vseq;
  `uvm_object_utils(otp_ctrl_check_fail_vseq)

  `uvm_object_new

  constraint ecc_otp_err_c {
    ecc_otp_err inside {OtpEccCorrErr, OtpNoEccErr};
  }

  constraint ecc_chk_err_c {
    ecc_chk_err dist {OtpNoEccErr   :/ 1,
                      OtpEccCorrErr :/ 1,
                      OtpEccUncorrErr :/1 };
  }

  // 50% chance of having a check timeout
  // Because of the regwen, even though we constrain the timeout value, it might not apply to the
  // DUT.
  constraint check_timeout_val_c {
    check_timeout_val dist {[1 : CHK_TIMEOUT_CYC] :/ 1,
                            [100_000 :'1]         :/ 1};
  }

endclass
