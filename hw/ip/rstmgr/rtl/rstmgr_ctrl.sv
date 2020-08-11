// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module implements generic reset controls
//

`include "prim_assert.sv"

module rstmgr_ctrl
import rstmgr_pkg::*;
#(
    parameter int PowerDomains = 2,
    localparam int OffDomains = PowerDomains - 1
) (
    input                           clk_i,
    input                           rst_ni,
    input        [PowerDomains-1:0] rst_req_i,
    input        [PowerDomains-1:0] rst_parent_ni,  // parent reset
    output logic [PowerDomains-1:0] rst_no
);

  // The code below always assumes the always on domain is index 0
  `ASSERT_INIT(AlwaysOnIndex_A, ALWAYS_ON_SEL == 0)

  // when there are multiple on domains, the latter 1 should become another parameter
  localparam int OffDomainSelStart = ALWAYS_ON_SEL + 1;

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
      .clk_i (clk_i),
      .rst_ni(rst_ni),
      .d_i   (rst_parent_ni),
      .q_o   (rst_parent_synced)
  );

  // always on handling
  prim_flop u_aon_rst (
      .clk_i,
      .rst_ni,
      .d_i(~rst_req_i[ALWAYS_ON_SEL] & rst_parent_synced[ALWAYS_ON_SEL]),
      .q_o(rst_aon_nq)
  );


  // the non-always-on domains
  // These reset whenever the always on domain reset, to ensure power definition consistency.
  // By extension, they also reset whenever the root (rst_ni) resets
  assign rst_pd_nd = ~rst_req_i[OffDomainSelStart +: OffDomains] &
      rst_parent_synced[OffDomainSelStart +: OffDomains];

  prim_flop u_pd_rst (
      .clk_i,
      .rst_ni(rst_aon_nq),
      .d_i   (rst_pd_nd),
      .q_o   (rst_pd_nq)
  );

  assign rst_no = {rst_pd_nq, rst_aon_nq};

endmodule  // rstmgr_ctrl
