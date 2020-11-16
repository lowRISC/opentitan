// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// interface for input data from LC, OTP and flash
interface keymgr_if(input clk, input rst_n);

  import keymgr_pkg::*;

  lc_data_t lc;
  otp_data_t otp;
  flash_ctrl_pkg::keymgr_flash_t flash;

  hw_key_req_t kmac_key;
  hw_key_req_t hmac_key;
  hw_key_req_t aes_key;

  task automatic init();
    lc    = LC_DATA_DEFAULT;
    otp   = OTP_DATA_DEFAULT;
    flash = FLASH_KEY_DEFAULT;
  endtask
endinterface
