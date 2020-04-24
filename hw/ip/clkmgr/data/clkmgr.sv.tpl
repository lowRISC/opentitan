// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// The overall clock manager

`include "prim_assert.sv"

<%
clks_attr = cfg['clocks']
srcs = clks_attr['srcs']
%>

module clkmgr import clkmgr_pkg::*; (
  // Primary module clocks
  input clk_i,
  input rst_ni,
% for src in srcs:
  input clk_${src['name']}_i,
  input rst_${src['name']}_ni,
% endfor

  // Bus Interface
  input tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // pwrmgr interface
  input pwrmgr_pkg::pwr_clk_req_t pwr_i,
  output pwrmgr_pkg::pwr_clk_rsp_t pwr_o,

  // dft interface
  input clk_dft_t dft_i,

  // idle hints
  input clk_hint_status_t status_i,

  // clock output interface
  output clkmgr_out_t clocks_o

);

  ////////////////////////////////////////////////////
  // Register Interface
  ////////////////////////////////////////////////////

  clkmgr_reg_pkg::clkmgr_reg2hw_t reg2hw;
  clkmgr_reg_pkg::clkmgr_hw2reg_t hw2reg;

  clkmgr_reg_top i_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .devmode_i(1'b1)
  );

  ////////////////////////////////////////////////////
  // Power up group - feedthrough
  ////////////////////////////////////////////////////
  ## This group is hardcoded right now because it is the only one.
  ## In the future if there are more, feedthrough should be converted to an attribute

% for k,v in ft_clks.items():
  assign clocks_o.${k} = clk_${v}_i;
% endfor

  ////////////////////////////////////////////////////
  // Root gating
  ////////////////////////////////////////////////////

  // the rst_ni connection below is incorrect, need to find a proper reset in the sequence to use
  // if the clkmgr is always on, can use por synced directly
  // if not, then need to generate something ahead of lc/sys

  logic async_roots_en;
  logic roots_en_q2, roots_en_q1, roots_en_d;
% for src in srcs:
  logic clk_${src['name']}_root;
  logic clk_${src['name']}_en;
% endfor

% for src in srcs:
  prim_clock_gating_sync i_${src['name']}_sync (
    .clk_i(clk_${src['name']}_i),
    .rst_ni(rst_${src['name']}_ni),
    .test_en_i(dft_i.test_en),
    .async_en_i(pwr_i.ip_clk_en),
    .en_o(clk_${src['name']}_en),
    .clk_o(clk_${src['name']}_root)
  );
% endfor

  // an async OR of all the synchronized enables
  assign async_roots_en =
% for src in srcs:
    % if loop.last:
    clk_${src['name']}_en;
    % else:
    clk_${src['name']}_en |
    % endif
% endfor

  // Sync the OR back into clkmgr domain for feedback to pwrmgr.
  // Since the signal is combo / converged on the other side, de-bounce
  // the signal prior to output
  prim_flop_2sync #(
    .Width(1)
  ) i_roots_en_sync (
    .clk_i,
    .rst_ni,
    .d(async_roots_en),
    .q(roots_en_d)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      roots_en_q1 <= 1'b0;
      roots_en_q2 <= 1'b0;
    end else begin
      roots_en_q1 <= roots_en_d;

      if (roots_en_q1 == roots_en_d) begin
        roots_en_q2 <= roots_en_q1;
      end
    end
  end

  assign pwr_o.roots_en = roots_en_q2;

  ////////////////////////////////////////////////////
  // Clocks with only root gate
  ////////////////////////////////////////////////////
% for k,v in rg_clks.items():
  assign clocks_o.${k} = clk_${v}_root;
% endfor

  ////////////////////////////////////////////////////
  // Software direct control group
  ////////////////////////////////////////////////////

  // the rst_ni connection below is incorrect, need to find a proper reset in the sequence to use
  // if the clkmgr is always on, can use por synced directly
  // if not, then need to generate something ahead of lc/sys

% for k,v in sw_clks.items():
  prim_clock_gating_sync i_${k}_sync (
    .clk_i(clk_${v}_root),
    .rst_ni(rst_${v}_ni),
    .test_en_i(dft_i.test_en),
    .async_en_i(reg2hw.clk_enables.${k}_en.q),
    .en_o(), // should this be fedback for software?
    .clk_o(clocks_o.${k})
  );
% endfor

  ////////////////////////////////////////////////////
  // Software hint group
  // The idle hint feedback is assumed to be synchronous to the
  // clock target
  ////////////////////////////////////////////////////

  // the rst_ni connection below is incorrect, need to find a proper reset in the sequence to use
  // if the clkmgr is always on, can use por synced directly
  // if not, then need to generate something ahead of lc/sys

% for k in hint_clks:
  logic ${k}_hint;
  logic ${k}_en;
% endfor

% for k,v in hint_clks.items():
  assign ${k}_en = ${k}_hint | ~status_i.idle[${loop.index}];

  prim_flop_2sync #(
    .Width(1)
  ) i_${k}_hint_sync (
    .clk_i(clk_${v}_root),
    .rst_ni(rst_${v}_ni),
    .d(reg2hw.clk_hints.${k}_hint.q),
    .q(${k}_hint)
  );

  prim_clock_gating i_${k}_sync (
    .clk_i(clk_${v}_root),
    .en_i(${k}_en),
    .test_en_i(dft_i.test_en),
    .clk_o(clocks_o.${k})
  );

% endfor

  // state readback
% for k,v in hint_clks.items():
  assign hw2reg.clk_hints_status.${k}_val.de = 1'b1;
  assign hw2reg.clk_hints_status.${k}_val.d = ${k}_en;
% endfor


  ////////////////////////////////////////////////////
  // Assertions
  ////////////////////////////////////////////////////


endmodule // rstmgr
