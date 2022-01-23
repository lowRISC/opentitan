// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This has assertions that check the output resets read-only value of the alert and cpu_info_attr.
interface rstmgr_sw_rst_sva_if (
  input logic                                   clk_i,
  input logic                                   rst_ni,
  input logic                                   parent_rst_n,
  input logic [rstmgr_reg_pkg::NumSwResets-1:0] enables,
  input logic [rstmgr_reg_pkg::NumSwResets-1:0] ctrl_ns,
  input logic [rstmgr_reg_pkg::NumSwResets-1:0] rst_ens,
  input logic [rstmgr_reg_pkg::NumSwResets-1:0] rst_ns
);
  logic disable_sva;

  for (genvar i = 0; i < rstmgr_reg_pkg::NumSwResets; ++i) begin : gen_assertions
    `ASSERT(RstNOn_A, !parent_rst_n || (enables[i] && !ctrl_ns[i]) |=> !rst_ns[i], clk_i,
            !rst_ni || disable_sva)
    `ASSERT(RstNOff_A, parent_rst_n && !(enables[i] && !ctrl_ns[i]) |=> rst_ns[i], clk_i,
            !rst_ni || disable_sva)
    `ASSERT(RstEnOn_A, !parent_rst_n || (enables[i] && !ctrl_ns[i]) |=> rst_ens[i], clk_i,
            !rst_ni || disable_sva)
    `ASSERT(RstEnOff_A, parent_rst_n && !(enables[i] && !ctrl_ns[i]) |=> !rst_ens[i], clk_i,
            !rst_ni || disable_sva)
  end
endinterface
