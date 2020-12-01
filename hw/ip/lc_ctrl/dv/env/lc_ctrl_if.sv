// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// interface for input data from OTP
interface lc_ctrl_if(input clk, input rst_n);

  import lc_ctrl_pkg::*;
  import otp_ctrl_pkg::*;

  otp_ctrl_pkg::otp_lc_data_t otp_i;

  task automatic init(lc_ctrl_pkg::lc_state_e lc_state = LcStRaw,
                      lc_ctrl_pkg::lc_cnt_e   lc_cnt = LcCntRaw);
    otp_i.valid = 1;
    otp_i.state = lc_state;
    otp_i.count = lc_cnt;
    otp_i.test_unlock_token = 0;
    otp_i.test_exit_token = 0;
    otp_i.rma_token = 0;
    otp_i.id_state = LcIdBlank;
  endtask

endinterface
