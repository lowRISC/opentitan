// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface sram_ctrl_exec_if;
  string path = "exec_if";

  lc_ctrl_pkg::lc_tx_t lc_hw_debug_en;

  otp_ctrl_pkg::otp_en_t otp_en_sram_ifetch;

  // LC escalation signal must be stable before reset ends
  task automatic init();
    lc_hw_debug_en = lc_ctrl_pkg::Off;
    otp_en_sram_ifetch = otp_ctrl_part_pkg::OTP_HW_CFG_DEFAULT;
  endtask

  task automatic drive_lc_hw_debug_en(bit [3:0] hw_debug_en);
    lc_hw_debug_en = lc_ctrl_pkg::lc_tx_t'(hw_debug_en);
  endtask

  task automatic drive_otp_en_sram_ifetch(bit [7:0] en_sram_ifetch);
    otp_en_sram_ifetch = otp_ctrl_pkg::otp_en_t'(en_sram_ifetch);
  endtask

endinterface
