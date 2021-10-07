// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0



package clkmgr_pkg;

  typedef enum int {
    HintMainAes = 0,
    HintMainHmac = 1,
    HintMainKmac = 2,
    HintIoDiv4Otbn = 3,
    HintMainOtbn = 4
  } hint_names_e;

  // clocks generated and broadcast
  typedef struct packed {
    logic clk_io_div4_powerup;
    logic clk_aon_powerup;
    logic clk_main_powerup;
    logic clk_io_powerup;
    logic clk_usb_powerup;
    logic clk_io_div2_powerup;
    logic clk_aon_infra;
    logic clk_aon_secure;
    logic clk_aon_peri;
    logic clk_aon_timers;
    logic clk_main_aes;
    logic clk_main_hmac;
    logic clk_main_kmac;
    logic clk_main_otbn;
    logic clk_io_div4_otbn;
    logic clk_io_div4_infra;
    logic clk_main_infra;
    logic clk_io_div4_secure;
    logic clk_main_secure;
    logic clk_usb_secure;
    logic clk_io_div4_timers;
    logic clk_io_div4_peri;
    logic clk_io_div2_peri;
    logic clk_io_peri;
    logic clk_usb_peri;
  } clkmgr_out_t;

  // clock gating indication for alert handler
  typedef struct packed {
    lc_ctrl_pkg::lc_tx_t io_div4_powerup;
    lc_ctrl_pkg::lc_tx_t aon_powerup;
    lc_ctrl_pkg::lc_tx_t main_powerup;
    lc_ctrl_pkg::lc_tx_t io_powerup;
    lc_ctrl_pkg::lc_tx_t usb_powerup;
    lc_ctrl_pkg::lc_tx_t io_div2_powerup;
    lc_ctrl_pkg::lc_tx_t aon_infra;
    lc_ctrl_pkg::lc_tx_t aon_secure;
    lc_ctrl_pkg::lc_tx_t aon_peri;
    lc_ctrl_pkg::lc_tx_t aon_timers;
    lc_ctrl_pkg::lc_tx_t main_aes;
    lc_ctrl_pkg::lc_tx_t main_hmac;
    lc_ctrl_pkg::lc_tx_t main_kmac;
    lc_ctrl_pkg::lc_tx_t main_otbn;
    lc_ctrl_pkg::lc_tx_t io_div4_otbn;
    lc_ctrl_pkg::lc_tx_t io_div4_infra;
    lc_ctrl_pkg::lc_tx_t main_infra;
    lc_ctrl_pkg::lc_tx_t io_div4_secure;
    lc_ctrl_pkg::lc_tx_t main_secure;
    lc_ctrl_pkg::lc_tx_t usb_secure;
    lc_ctrl_pkg::lc_tx_t io_div4_timers;
    lc_ctrl_pkg::lc_tx_t io_div4_peri;
    lc_ctrl_pkg::lc_tx_t io_div2_peri;
    lc_ctrl_pkg::lc_tx_t io_peri;
    lc_ctrl_pkg::lc_tx_t usb_peri;
  } clkmgr_cg_en_t;

  parameter int NumOutputClk = 25;


  typedef struct packed {
    logic [5-1:0] idle;
  } clk_hint_status_t;

  parameter clk_hint_status_t CLK_HINT_STATUS_DEFAULT = '{
    idle: {5{1'b1}}
  };

endpackage // clkmgr_pkg
