// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// interface for input data from OTP
interface lc_ctrl_if(input clk, input rst_n);

  import lc_ctrl_pkg::*;
  import otp_ctrl_pkg::*;

  otp_ctrl_pkg::otp_lc_data_t otp_i;

  task automatic init();
    otp_i.valid = 1;
    otp_i.state = LcStRaw;
    otp_i.count = LcCntRaw;
    otp_i.test_unlock_token = 0;
    otp_i.test_exit_token = 0;
    otp_i.rma_token = 0;
    otp_i.id_state = LcIdBlank;
  endtask

endinterface
