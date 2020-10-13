// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// interface for input data from LC, OTP and flash
interface keymgr_input_data_if();

  import keymgr_pkg::*;

  lc_data_t lc                         = keymgr_pkg::LC_DATA_DEFAULT;
  otp_data_t otp                       = keymgr_pkg::OTP_DATA_DEFAULT;
  flash_ctrl_pkg::keymgr_flash_t flash = keymgr_pkg::FLASH_KEY_DEFAULT;

endinterface
