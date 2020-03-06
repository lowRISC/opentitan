// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module implements generic reset controls
//

`include "prim_assert.sv"

module rstmgr_ctrl import rstmgr_pkg::*; #(
  parameter int PowerDomains = 2,
  localparam int OffDomains = PowerDomains - 1
) (
  input clk_i,
  input rst_ni,
  input [PowerDomains-1:0] rst_req_i,
  input [PowerDomains-1:0] rst_parent_ni, // parent reset
  output logic [PowerDomains-1:0] rst_no
);

  // The code below always assumes the always on domain is index 0
  `ASSERT_INIT(AlwaysOnIndex_A, ALWAYS_ON_SEL == 0)

  // when there are multiple on domains, the latter 1 should become another parameter
  localparam int OffDomainSelStart = ALWAYS_ON_SEL + 1;

  // the always on root reset
  logic rst_aon_n;

  // the remaining resets
  logic [OffDomains-1:0] rst_pd_n;

  // Parent resets may assert asynchronously, so we need to sync before using it as part
  // of the control path
  logic [PowerDomains-1:0] rst_parent_synced;
  prim_flop_2sync #(
    .Width(PowerDomains),
    .ResetValue(0)
  ) u_lc (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .d(rst_parent_ni),
    .q(rst_parent_synced)
  );

  // always on handling
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rst_aon_n <= '0;
    end else begin
      // if the parent is in reset, OR there's an always on reset request
      // reset this node
      rst_aon_n <= ~rst_req_i[ALWAYS_ON_SEL] & rst_parent_synced[ALWAYS_ON_SEL];
    end
  end

  // the non-always-on domains
  // These reset whenever the always on domain reset, to ensure power definition consistency.
  // By extension, they also reset whenever the root (rst_ni) resets
  always_ff @(posedge clk_i or negedge rst_aon_n) begin
    if (!rst_aon_n) begin
      rst_pd_n <= '0;
    end else begin
      rst_pd_n <= ~rst_req_i[OffDomainSelStart +: OffDomains] &
                  rst_parent_synced[OffDomainSelStart +: OffDomains];
    end
  end

  assign rst_no = {rst_pd_n, rst_aon_n};

endmodule // rstmgr_ctrl
