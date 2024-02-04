// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


package clkmgr_pkg;

  typedef struct packed {
    logic test_en;
  } clk_dft_t;

  parameter clk_dft_t CLK_DFT_DEFAULT = '{
    test_en: 1'b0
  };

  typedef struct packed {
  logic clk_fixed_powerup;
  logic clk_main_powerup;
  logic clk_usb_48mhz_powerup;
  logic clk_main_aes;
  logic clk_main_hmac;
  logic clk_main_infra;
  logic clk_fixed_infra;
  logic clk_fixed_secure;
  logic clk_main_secure;
  logic clk_fixed_timers;
  logic clk_proc_main;
  logic clk_fixed_peri;
  logic clk_usb_48mhz_peri;

  } clkmgr_out_t;

  typedef struct packed {
    logic [2-1:0] idle;
  } clk_hint_status_t;

  parameter clk_hint_status_t CLK_HINT_STATUS_DEFAULT = '{
    idle: {2{1'b1}}
  };


endpackage // clkmgr_pkg
