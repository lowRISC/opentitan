// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// clkmgr interface.

interface rstmgr_if (
  input logic clk,
  input logic rst_n
);

  import rstmgr_env_pkg::*;
  import rstmgr_pkg::*;

  logic                        por_n;

  pwrmgr_pkg::pwr_rst_req_t    pwr_i;
  pwrmgr_pkg::pwr_rst_rsp_t    pwr_o;

  // cpu related inputs
  rstmgr_pkg::rstmgr_cpu_t     cpu_i;

  // Interface to alert handler
  alert_pkg::alert_crashdump_t alert_dump_i;

  // Interface to cpu crash dump
  ibex_pkg::crash_dump_t       cpu_dump_i;

  // dft bypass
  logic                        scan_rst_ni;

  lc_ctrl_pkg::lc_tx_t         scanmode_i;

  // reset outputs
  rstmgr_pkg::rstmgr_ast_out_t resets_ast_o;
  rstmgr_pkg::rstmgr_out_t     resets_o;

endinterface
