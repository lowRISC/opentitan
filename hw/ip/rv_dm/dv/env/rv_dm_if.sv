// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface rv_dm_if(input logic clk, input logic rst_n);

  import rv_dm_env_pkg::*;

  // "Enable" inputs
  lc_ctrl_pkg::lc_tx_t    lc_init_done;
  lc_ctrl_pkg::lc_tx_t    lc_hw_debug_clr;
  lc_ctrl_pkg::lc_tx_t    lc_hw_debug_en;
  lc_ctrl_pkg::lc_tx_t    lc_check_byp_en;
  lc_ctrl_pkg::lc_tx_t    lc_escalate_en;
  lc_ctrl_pkg::lc_tx_t    pinmux_hw_debug_en;
  lc_ctrl_pkg::lc_tx_t    lc_dft_en;
  prim_mubi_pkg::mubi8_t  otp_dis_rv_dm_late_debug;
  logic                   strap_en;
  logic                   strap_en_override;

  // Other DUT inputs.
  prim_mubi_pkg::mubi4_t  scanmode;
  logic                   scan_rst_n;
  logic [NUM_HARTS-1:0]   unavailable;

  // DUT outputs.
  wire ndmreset_req;
  wire dmactive;
  wire [NUM_HARTS-1:0] debug_req;

  // Disable TLUL host SBA assertions when injecting intg errors on the response channel.
  bit disable_tlul_assert_host_sba_resp_svas;

  clocking cb @(posedge clk);
    output lc_init_done;
    output lc_hw_debug_clr;
    output lc_hw_debug_en;
    output pinmux_hw_debug_en;
    output lc_dft_en;
    output otp_dis_rv_dm_late_debug;
    output scanmode;
    output scan_rst_n;
    output unavailable;
    input ndmreset_req;
    input dmactive;
    input debug_req;
  endclocking

endinterface
