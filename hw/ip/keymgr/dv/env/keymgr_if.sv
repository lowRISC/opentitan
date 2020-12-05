// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// interface for input data from LC, OTP and flash
interface keymgr_if(input clk, input rst_n);

  import keymgr_pkg::*;

  lc_data_t lc;
  otp_data_t otp;
  otp_ctrl_pkg::otp_keymgr_key_t otp_key;
  flash_ctrl_pkg::keymgr_flash_t flash;

  hw_key_req_t kmac_key;
  hw_key_req_t hmac_key;
  hw_key_req_t aes_key;

  task automatic init();
    lc      = LC_DATA_DEFAULT;
    otp     = OTP_DATA_DEFAULT;
    otp_key = otp_ctrl_pkg::OTP_KEYMGR_KEY_DEFAULT;
    flash   = flash_ctrl_pkg::KEYMGR_FLASH_DEFAULT;


  endtask
endinterface
