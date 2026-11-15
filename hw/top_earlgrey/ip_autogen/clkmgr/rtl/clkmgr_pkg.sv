// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package clkmgr_pkg;

  typedef enum int {
    HintMainAes = 0,
    HintMainHmac = 1,
    HintMainKmac = 2,
    HintMainOtbn = 3
  } hint_names_e;

  // Clocks broadcast. Each partition outputs the clocks of the modules on its side.
  typedef struct packed {
    logic clk_io_div4_powerup;
    logic clk_aon_gated_powerup;
    logic clk_main_powerup;
    logic clk_io_powerup;
    logic clk_usb_powerup;
    logic clk_aon_gated_peri;
    logic clk_main_aes;
    logic clk_main_hmac;
    logic clk_main_kmac;
    logic clk_main_otbn;
    logic clk_io_div4_infra;
    logic clk_main_infra;
    logic clk_usb_infra;
    logic clk_io_infra;
    logic clk_io_div4_secure;
    logic clk_main_secure;
    logic clk_io_div4_timers;
    logic clk_io_div4_peri;
    logic clk_io_peri;
    logic clk_usb_peri;
    logic clk_io_spi_host1;
  } clkmgr_out_primary_t;

  typedef struct packed {
    logic clk_io_div4_powerup;
    logic clk_aon_powerup;
    logic clk_aon_secure;
    logic clk_aon_peri;
    logic clk_aon_timers;
    logic clk_io_div4_infra;
    logic clk_io_div4_secure;
    logic clk_io_div4_timers;
    logic clk_io_div4_peri;
  } clkmgr_out_secondary_t;

  // Clock gating indications for the alert handlers. The primary partition outputs all of them.
  // The secondary partition's indications cross to it in intraip_s2p.
  typedef struct packed {
    prim_mubi_pkg::mubi4_t io_div4_powerup;
    prim_mubi_pkg::mubi4_t aon_powerup;
    prim_mubi_pkg::mubi4_t aon_gated_powerup;
    prim_mubi_pkg::mubi4_t main_powerup;
    prim_mubi_pkg::mubi4_t io_powerup;
    prim_mubi_pkg::mubi4_t usb_powerup;
    prim_mubi_pkg::mubi4_t aon_secure;
    prim_mubi_pkg::mubi4_t aon_gated_peri;
    prim_mubi_pkg::mubi4_t aon_peri;
    prim_mubi_pkg::mubi4_t aon_timers;
    prim_mubi_pkg::mubi4_t main_aes;
    prim_mubi_pkg::mubi4_t main_hmac;
    prim_mubi_pkg::mubi4_t main_kmac;
    prim_mubi_pkg::mubi4_t main_otbn;
    prim_mubi_pkg::mubi4_t io_div4_infra;
    prim_mubi_pkg::mubi4_t main_infra;
    prim_mubi_pkg::mubi4_t usb_infra;
    prim_mubi_pkg::mubi4_t io_infra;
    prim_mubi_pkg::mubi4_t io_div4_secure;
    prim_mubi_pkg::mubi4_t main_secure;
    prim_mubi_pkg::mubi4_t io_div4_timers;
    prim_mubi_pkg::mubi4_t io_div4_peri;
    prim_mubi_pkg::mubi4_t io_peri;
    prim_mubi_pkg::mubi4_t usb_peri;
    prim_mubi_pkg::mubi4_t io_spi_host1;
  } clkmgr_cg_en_primary_t;

  parameter int NumOutputClk = 25;


  typedef struct packed {
    logic [4-1:0] idle;
  } clk_hint_status_t;

  parameter clk_hint_status_t CLK_HINT_STATUS_DEFAULT = '{
    idle: {4{1'b1}}
  };

  // Signalling between the two partitions of the split clock manager.
  // Secondary (always-on clocks) to primary
  typedef struct packed {
    // The scan mode, which enters the secondary partition only.
    prim_mubi_pkg::mubi4_t scanmode;
    // The always-on root clocks, which the secondary partition buffers once. The always-on clock is
    // gated. It runs only while the power domain of the primary partition has power and its
    // isolation is off.
    logic clk_aon;
    // The clock gating indications of the clocks that the secondary partition generates and the
    // primary partition does not buffer itself. The primary partition outputs all the indications,
    // and drives those of the clocks that it buffers too.
    prim_mubi_pkg::mubi4_t cg_en_aon_powerup;
    prim_mubi_pkg::mubi4_t cg_en_aon_secure;
    prim_mubi_pkg::mubi4_t cg_en_aon_peri;
    prim_mubi_pkg::mubi4_t cg_en_aon_timers;
    // The clock enable requests come from the power manager, which is in the power domain of the
    // secondary partition.
    logic main_ip_clk_en;
    logic io_ip_clk_en;
    logic usb_ip_clk_en;
  } intraip_s2p_t;

  // Primary to secondary
  typedef struct packed {
    // used in the power domain of the secondary as clk_io_div4_powerup
    logic clk_io_div4;
    // used in the power domain of the secondary as clk_io_div4_infra, clk_io_div4_secure,
    // clk_io_div4_timers
    logic clk_io_div4_root;
    // used in the power domain of the secondary as clk_io_div4_peri
    logic clk_io_div4_peri;
    // The clock status responses go to the power manager.
    logic main_status;
    logic io_status;
    logic usb_status;
  } intraip_p2s_t;

endpackage // clkmgr_pkg
