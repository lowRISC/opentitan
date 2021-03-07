// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence creates the following check failure scenarios:
// 1. Check timeout
// 2. TODO: add when support
class otp_ctrl_check_fail_vseq extends otp_ctrl_dai_errs_vseq;
  `uvm_object_utils(otp_ctrl_check_fail_vseq)

  `uvm_object_new

  // 50% chance of having a check timeout
  constraint check_timeout_val_c {
    check_timeout_val dist {[1 : CHK_TIMEOUT_CYC] :/ 1,
                            [100_000 :'1]         :/ 1};
  }
endclass
