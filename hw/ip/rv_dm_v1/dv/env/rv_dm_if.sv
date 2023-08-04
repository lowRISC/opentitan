// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface rv_dm_if(input logic clk, input logic rst_n);

  import rv_dm_env_pkg::*;

  // DUT inputs.
  lc_ctrl_pkg::lc_tx_t    lc_hw_debug_en;
  prim_mubi_pkg::mubi4_t  scanmode;
  logic                   scan_rst_n;
  logic [NUM_HARTS-1:0]   unavailable;

  // DUT outputs.
  logic ndmreset_req;
  logic dmactive;
  logic [NUM_HARTS-1:0] debug_req;

  // Disable TLUL host SBA assertions when injecting intg errors on the response channel.
  bit disable_tlul_assert_host_sba_resp_svas;

  // TODO: add clocking blocks.

endinterface
