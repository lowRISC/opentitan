// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module implements generic reset controls
//

`include "prim_assert.sv"

module rstmgr_ctrl
  import rstmgr_pkg::*;
  import rstmgr_reg_pkg::*;
(
  input clk_i,
  input rst_ni,
  input [PowerDomains-1:0] rst_req_i,
  input [PowerDomains-1:0] rst_parent_ni, // parent reset
  output logic [PowerDomains-1:0] rst_no
);

  // the always on root reset
  logic rst_aon_nq;

  // the remaining resets
  logic [OffDomains-1:0] rst_pd_nd, rst_pd_nq;

  // Parent resets may assert asynchronously, so we need to sync before using it as part
  // of the control path
  logic [PowerDomains-1:0] rst_parent_synced;
  prim_flop_2sync #(
    .Width(PowerDomains),
    .ResetValue('0)
  ) u_lc (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .d_i(rst_parent_ni),
    .q_o(rst_parent_synced)
  );

  // always on handling
  prim_flop u_aon_rst (
    .clk_i,
    .rst_ni,
    .d_i(~rst_req_i[DomainAonSel] & rst_parent_synced[DomainAonSel]),
    .q_o(rst_aon_nq)
  );

  // the non-always-on domains
  // These reset whenever the always on domain reset, to ensure power definition consistency.
  // By extension, they also reset whenever the root (rst_ni) resets
  assign rst_pd_nd = ~rst_req_i[Domain0Sel +: OffDomains] &
                     rst_parent_synced[Domain0Sel +: OffDomains];

  prim_flop u_pd_rst (
    .clk_i,
    .rst_ni(rst_aon_nq),
    .d_i(rst_pd_nd),
    .q_o(rst_pd_nq)
  );

  assign rst_no = {rst_pd_nq, rst_aon_nq};

endmodule // rstmgr_ctrl
