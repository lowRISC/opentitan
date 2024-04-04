// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface that gets bound into aon_timer_core to track its input and output signals. The names
// are kept in sync with the signals on aon_timer_core, so the ports can be connected with a .*

interface aon_timer_core_if (
  input logic                      clk_aon_i,
  input logic                      rst_aon_ni,

  input lc_ctrl_pkg::lc_tx_t [2:0] lc_escalate_en_i,
  input logic                      sleep_mode_i,

  // Register read outputs
  input logic                      wkup_enable_o,
  input logic [11:0]               wkup_prescaler_o,
  input logic [31:0]               wkup_thold_o,
  input logic [31:0]               wkup_count_o,
  input logic                      wdog_enable_o,
  input logic                      wdog_pause_o,
  input logic [31:0]               wdog_bark_thold_o,
  input logic [31:0]               wdog_bite_thold_o,
  input logic [31:0]               wdog_count_o,

  // Register write inputs
  input logic                      wkup_ctrl_reg_wr_i,
  input logic [12:0]               wkup_ctrl_wr_data_i,
  input logic                      wkup_thold_reg_wr_i,
  input logic [31:0]               wkup_thold_wr_data_i,
  input logic                      wkup_count_reg_wr_i,
  input logic [31:0]               wkup_count_wr_data_i,
  input logic                      wdog_ctrl_reg_wr_i,
  input logic [1:0]                wdog_ctrl_wr_data_i,
  input logic                      wdog_bark_thold_reg_wr_i,
  input logic [31:0]               wdog_bark_thold_wr_data_i,
  input logic                      wdog_bite_thold_reg_wr_i,
  input logic [31:0]               wdog_bite_thold_wr_data_i,
  input logic                      wdog_count_reg_wr_i,
  input logic [31:0]               wdog_count_wr_data_i,

  input logic                      wkup_intr_o,
  input logic                      wdog_intr_o,
  input logic                      wdog_reset_req_o
);


endinterface
