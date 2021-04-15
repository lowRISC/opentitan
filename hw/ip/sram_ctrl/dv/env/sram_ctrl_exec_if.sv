// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface sram_ctrl_exec_if;
  string path = "exec_if";

  lc_ctrl_pkg::lc_tx_t lc_hw_debug_en;

  otp_ctrl_part_pkg::otp_hw_cfg_t otp_hw_cfg;

  // LC escalation signal must be stable before reset ends
  task automatic init();
    lc_hw_debug_en = lc_ctrl_pkg::Off;
    otp_hw_cfg = otp_ctrl_part_pkg::OTP_HW_CFG_DEFAULT;
  endtask

  task automatic drive_lc_hw_debug_en(bit [3:0] hw_debug_en);
    lc_hw_debug_en = lc_ctrl_pkg::lc_tx_t'(hw_debug_en);
  endtask

  // The only field that matters of the otp_cfg is the `en_sram_ifetch` value
  task automatic drive_otp_hw_cfg(bit [7:0] en_sram_ifetch);
    otp_ctrl_part_pkg::otp_hw_cfg_t rand_cfg;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(rand_cfg, rand_cfg.data.en_sram_ifetch == en_sram_ifetch;, , path)
    otp_hw_cfg = rand_cfg;
  endtask

endinterface
