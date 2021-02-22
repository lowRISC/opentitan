// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// otp_ctrl_marco_errs_vseq is create OTP macro errors including:
// - ECC correctable errors
// - ECC uncorrectable errors
class otp_ctrl_macro_errs_vseq extends otp_ctrl_dai_errs_vseq;
  `uvm_object_utils(otp_ctrl_macro_errs_vseq)

  `uvm_object_new

  constraint ecc_err_c {
    // TODO: currently only max to 2 error bits, once implemetned ECC in mem_bkdr_if, we can
    // fully randomize num of error bits
    $countones(ecc_err_mask) dist  {0 :/ 2,
                                    1 :/ 1,
                                    2 :/ 1};
  }

endclass
