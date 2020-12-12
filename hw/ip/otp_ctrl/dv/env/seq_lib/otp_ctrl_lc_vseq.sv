// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// otp_ctrl_lc_vseq is developed to generate lc_otp transitions
class otp_ctrl_lc_vseq extends otp_ctrl_smoke_vseq;
  `uvm_object_utils(otp_ctrl_lc_vseq)

  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    do_lc_trans = 1;
  endtask
endclass
