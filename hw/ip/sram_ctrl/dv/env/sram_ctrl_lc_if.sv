// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface sram_ctrl_lc_if;
  lc_ctrl_pkg::lc_tx_t lc_esc_en;

  // LC escalation signal must be stable before reset ends
  task automatic init();
    lc_esc_en = lc_ctrl_pkg::Off;
  endtask

  task automatic drive_lc_esc_en(lc_ctrl_pkg::lc_tx_t esc_en);
    lc_esc_en = esc_en;
  endtask

endinterface
