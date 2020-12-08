// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This interface collect the broadcast output data from OTP
interface otp_ctrl_output_data_if();
  import otp_ctrl_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_part_pkg::*;

  otp_hw_cfg_t     otp_hw_cfg;
  otp_keymgr_key_t keymgr_key;
  otp_lc_data_t    lc_data;

endinterface
