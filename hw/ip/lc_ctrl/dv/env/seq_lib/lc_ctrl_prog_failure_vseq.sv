// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence triggers prog_failure alert by setting the error bit in otp_program_rsp
// Then check in scb if the alert is triggered correctly
class lc_ctrl_prog_failure_vseq extends lc_ctrl_errors_vseq;
  `uvm_object_utils(lc_ctrl_prog_failure_vseq)

  `uvm_object_new

  constraint otp_prog_err_c {err_inj.otp_prog_err == 1;}

endclass
