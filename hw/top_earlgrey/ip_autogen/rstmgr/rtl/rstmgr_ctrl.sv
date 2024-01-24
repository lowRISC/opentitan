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
  input [PowerDomains-1:0] rst_req_i,
  input [PowerDomains-1:0] rst_parent_ni, // parent reset
  output logic [PowerDomains-1:0] rst_no,
  input scanmode_i,
  input scan_rst_ni
);

  // the always on root reset
  logic rst_aon_n_premux, rst_aon_n;

  // the remaining resets
  logic [OffDomains-1:0] rst_pd_nd, rst_pd_nq;

  // always on handling
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_aon_rst (
    .clk_i,
    .rst_ni(rst_parent_ni[DomainAonSel]),
    .d_i(~rst_req_i[DomainAonSel]),
    .q_o(rst_aon_n_premux)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_rst_aon_mux (
    .clk0_i(rst_aon_n_premux),
    .clk1_i(scan_rst_ni),
    .sel_i(scanmode_i),
    .clk_o(rst_aon_n)
  );
  assign rst_no[DomainAonSel] = rst_aon_n;

  // the non-always-on domains
  // These reset whenever the always on domain reset, to ensure power definition consistency.
  // By extension, they also reset whenever the root (rst_ni) resets
  assign rst_pd_nd = ~rst_req_i[Domain0Sel +: OffDomains];

  localparam int DomainPdStartIdx = DomainAonSel + 1;
  for(genvar i = 0; i < OffDomains; i++) begin : gen_rst_pd_n
    prim_flop_2sync #(
      .Width(1),
      .ResetValue('0)
    ) u_pd_rst (
      .clk_i,
      // when the always on portion resets, always reset the non-always-on portion as well.
      .rst_ni(rst_aon_n & rst_parent_ni[DomainPdStartIdx + i]),
      .d_i(rst_pd_nd[i]),
      .q_o(rst_pd_nq[i])
    );

    prim_clock_mux2 #(
      .NoFpgaBufG(1'b1)
    ) u_rst_pd_mux (
      .clk0_i(rst_pd_nq[i]),
      .clk1_i(scan_rst_ni),
      .sel_i(scanmode_i),
      .clk_o(rst_no[DomainPdStartIdx + i])
    );
  end

endmodule // rstmgr_ctrl
