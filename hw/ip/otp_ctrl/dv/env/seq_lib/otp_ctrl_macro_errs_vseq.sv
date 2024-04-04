// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// otp_ctrl_marco_errs_vseq is create OTP macro errors including:
// - ECC correctable errors
// - ECC uncorrectable errors
class otp_ctrl_macro_errs_vseq extends otp_ctrl_dai_lock_vseq;
  `uvm_object_utils(otp_ctrl_macro_errs_vseq)

  `uvm_object_new

  constraint ecc_otp_err_c {
    ecc_otp_err inside {OtpEccCorrErr, OtpEccUncorrErr};
  }

  function void pre_randomize();
    this.no_access_err_c.constraint_mode(0);
  endfunction

endclass
