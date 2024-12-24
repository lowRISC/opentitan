// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0



package clkmgr_pkg;

  typedef enum int {
    HintMainAes = 0
  } hint_names_e;

  // clocks generated and broadcast
  typedef struct packed {
    logic clk_io_div4_powerup;
    logic clk_aon_powerup;
    logic clk_main_powerup;
    logic clk_io_powerup;
    logic clk_usb_powerup;
    logic clk_io_div2_powerup;
    logic clk_aon_secure;
    logic clk_aon_peri;
    logic clk_aon_timers;
    logic clk_main_aes;
    logic clk_main_infra;
    logic clk_io_div4_infra;
    logic clk_io_infra;
    logic clk_usb_infra;
    logic clk_io_div4_secure;
    logic clk_main_secure;
    logic clk_io_div4_timers;
    logic clk_io_div4_peri;
    logic clk_io_div2_peri;
    logic clk_io_peri;
    logic clk_usb_peri;
  } clkmgr_out_t;

  // clock gating indication for alert handler
  typedef struct packed {
    prim_mubi_pkg::mubi4_t io_div4_powerup;
    prim_mubi_pkg::mubi4_t aon_powerup;
    prim_mubi_pkg::mubi4_t main_powerup;
    prim_mubi_pkg::mubi4_t io_powerup;
    prim_mubi_pkg::mubi4_t usb_powerup;
    prim_mubi_pkg::mubi4_t io_div2_powerup;
    prim_mubi_pkg::mubi4_t aon_secure;
    prim_mubi_pkg::mubi4_t aon_peri;
    prim_mubi_pkg::mubi4_t aon_timers;
    prim_mubi_pkg::mubi4_t main_aes;
    prim_mubi_pkg::mubi4_t main_infra;
    prim_mubi_pkg::mubi4_t io_div4_infra;
    prim_mubi_pkg::mubi4_t io_infra;
    prim_mubi_pkg::mubi4_t usb_infra;
    prim_mubi_pkg::mubi4_t io_div4_secure;
    prim_mubi_pkg::mubi4_t main_secure;
    prim_mubi_pkg::mubi4_t io_div4_timers;
    prim_mubi_pkg::mubi4_t io_div4_peri;
    prim_mubi_pkg::mubi4_t io_div2_peri;
    prim_mubi_pkg::mubi4_t io_peri;
    prim_mubi_pkg::mubi4_t usb_peri;
  } clkmgr_cg_en_t;

  parameter int NumOutputClk = 21;


  typedef struct packed {
    logic [1-1:0] idle;
  } clk_hint_status_t;

  parameter clk_hint_status_t CLK_HINT_STATUS_DEFAULT = '{
    idle: {1{1'b1}}
  };

endpackage // clkmgr_pkg
