// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// clkmgr interface.

interface rstmgr_if (
  input logic clk_aon,
  input logic clk,
  input logic rst_n
);

  import rstmgr_env_pkg::*;
  import rstmgr_pkg::PowerDomains;

  logic                        [PowerDomains-1:0] por_n;

  pwrmgr_pkg::pwr_rst_req_t                       pwr_i;
  pwrmgr_pkg::pwr_rst_rsp_t                       pwr_o;

  prim_mubi_pkg::mubi4_t                          sw_rst_req_o;

  // cpu related inputs
  rstmgr_pkg::rstmgr_cpu_t                        cpu_i;

  // Interface to alert handler
  alert_pkg::alert_crashdump_t                    alert_dump_i;

  // Interface to cpu crash dump
  rv_core_ibex_pkg::cpu_crash_dump_t              cpu_dump_i;

  // dft bypass
  logic                                           scan_rst_ni;
  prim_mubi_pkg::mubi4_t                          scanmode_i;

  // Reset status for alert handler.
  rstmgr_pkg::rstmgr_rst_en_t                     rst_en_o;

  // reset outputs
  rstmgr_pkg::rstmgr_out_t                        resets_o;

  // Supporting code.
  int                                             aon_cycles;
  always @(posedge clk_aon) aon_cycles += 1;

endinterface
