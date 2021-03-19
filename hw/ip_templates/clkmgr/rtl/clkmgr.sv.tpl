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
  // Primary module control clocks and resets
  // This drives the register interface
  input clk_i,
  input rst_ni,

  // System clocks and resets
  // These are the source clocks for the system
% for src in srcs:
  input clk_${src['name']}_i,
  % if src['aon'] == 'no':
  input rst_${src['name']}_ni,
  % endif
% endfor

  // Resets for derived clocks
  // clocks are derived locally
% for src in div_srcs:
  input rst_${src['name']}_ni,
% endfor

  // Bus Interface
  input tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // pwrmgr interface
  input pwrmgr_pkg::pwr_clk_req_t pwr_i,
  output pwrmgr_pkg::pwr_clk_rsp_t pwr_o,

  // dft interface
  input lc_ctrl_pkg::lc_tx_t scanmode_i,

  // idle hints
  input [${len(hint_clks)-1}:0] idle_i,

  // clock bypass control
  input lc_ctrl_pkg::lc_tx_t ast_clk_bypass_ack_i,
  output lc_ctrl_pkg::lc_tx_t lc_clk_bypass_ack_o,

  // jittery enable
  output logic jitter_en_o,

  // clock output interface
% for intf in export_clks:
  output clkmgr_${intf}_out_t clocks_${intf}_o,
% endfor
  output clkmgr_out_t clocks_o

);

  ////////////////////////////////////////////////////
  // Register Interface
  ////////////////////////////////////////////////////

  clkmgr_reg_pkg::clkmgr_reg2hw_t reg2hw;
  clkmgr_reg_pkg::clkmgr_hw2reg_t hw2reg;

  clkmgr_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .intg_err_o(),
    .devmode_i(1'b1)
  );

  ////////////////////////////////////////////////////
  // Divided clocks
  ////////////////////////////////////////////////////

  lc_ctrl_pkg::lc_tx_t step_down_req;
  logic [${len(div_srcs)-1}:0] step_down_acks;

  prim_lc_sync u_rcv (
    .clk_i,
    .rst_ni,
    .lc_en_i(ast_clk_bypass_ack_i),
    .lc_en_o(step_down_req)
  );

% for src in div_srcs:
  logic clk_${src['name']}_i;
% endfor

% for src in div_srcs:

  lc_ctrl_pkg::lc_tx_t ${src['name']}_div_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_${src['name']}_div_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(${src['name']}_div_scanmode)
  );

  prim_clock_div #(
    .Divisor(${src['div']})
  ) u_no_scan_${src['name']}_div (
    .clk_i(clk_${src['src']}_i),
    .rst_ni(rst_${src['src']}_ni),
    .step_down_req_i(step_down_req == lc_ctrl_pkg::On),
    .step_down_ack_o(step_down_acks[${loop.index}]),
    .test_en_i(${src['name']}_div_scanmode == lc_ctrl_pkg::On),
    .clk_o(clk_${src['name']}_i)
  );
% endfor

  prim_lc_sender u_send (
   .clk_i,
   .rst_ni,
   .lc_en_i(&step_down_acks ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off),
   .lc_en_o(lc_clk_bypass_ack_o)
  );

  ////////////////////////////////////////////////////
  // Feed through clocks
  // Feed through clocks do not actually need to be in clkmgr, as they are
  // completely untouched. The only reason they are here is for easier
  // bundling management purposes through clocks_o
  ////////////////////////////////////////////////////
% for k,v in ft_clks.items():
  prim_clock_buf u_${k}_buf (
    .clk_i(clk_${v}_i),
    .clk_o(clocks_o.${k})
  );
% endfor

  ////////////////////////////////////////////////////
  // Root gating
  ////////////////////////////////////////////////////

  logic wait_enable;
  logic wait_disable;
  logic en_status_d;
  logic dis_status_d;
  logic [1:0] en_status_q;
  logic [1:0] dis_status_q;
  logic clk_status;
% for src in rg_srcs:
  logic clk_${src}_root;
  logic clk_${src}_en;
% endfor

% for src in rg_srcs:
  lc_ctrl_pkg::lc_tx_t ${src}_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_${src}_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(${src}_scanmode)
  );

  prim_clock_gating_sync u_${src}_cg (
    .clk_i(clk_${src}_i),
    .rst_ni(rst_${src}_ni),
    .test_en_i(${src}_scanmode == lc_ctrl_pkg::On),
    .async_en_i(pwr_i.ip_clk_en),
    .en_o(clk_${src}_en),
    .clk_o(clk_${src}_root)
  );
% endfor

  // an async AND of all the synchronized enables
  // return feedback to pwrmgr only when all clocks are enabled
  assign wait_enable =
% for src in rg_srcs:
    % if loop.last:
    clk_${src}_en;
    % else:
    clk_${src}_en &
    % endif
% endfor

  // an async OR of all the synchronized enables
  // return feedback to pwrmgr only when all clocks are disabled
  assign wait_disable =
% for src in rg_srcs:
    % if loop.last:
    clk_${src}_en;
    % else:
    clk_${src}_en |
    % endif
% endfor

  // Sync clkmgr domain for feedback to pwrmgr.
  // Since the signal is combo / converged on the other side, de-bounce
  // the signal prior to output
  prim_flop_2sync #(
    .Width(1)
  ) u_roots_en_status_sync (
    .clk_i,
    .rst_ni,
    .d_i(wait_enable),
    .q_o(en_status_d)
  );

  prim_flop_2sync #(
    .Width(1)
  ) u_roots_or_sync (
    .clk_i,
    .rst_ni,
    .d_i(wait_disable),
    .q_o(dis_status_d)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      en_status_q <= '0;
      dis_status_q <= '0;
      clk_status <= '0;
    end else begin
      en_status_q <= {en_status_q[0], en_status_d};
      dis_status_q <= {dis_status_q[0], dis_status_d};

      if (&en_status_q) begin
        clk_status <= 1'b1;
      end else if (|dis_status_q == '0) begin
        clk_status <= 1'b0;
      end
    end
  end

  assign pwr_o.clk_status = clk_status;

  ////////////////////////////////////////////////////
  // Clocks with only root gate
  ////////////////////////////////////////////////////
% for k,v in rg_clks.items():
  assign clocks_o.${k} = clk_${v}_root;
% endfor

  ////////////////////////////////////////////////////
  // Software direct control group
  ////////////////////////////////////////////////////

% for k in sw_clks:
  logic ${k}_sw_en;
% endfor

% for k,v in sw_clks.items():
  prim_flop_2sync #(
    .Width(1)
  ) u_${k}_sw_en_sync (
    .clk_i(clk_${v}_i),
    .rst_ni(rst_${v}_ni),
    .d_i(reg2hw.clk_enables.${k}_en.q),
    .q_o(${k}_sw_en)
  );

  lc_ctrl_pkg::lc_tx_t ${k}_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_${k}_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(${k}_scanmode)
  );

  prim_clock_gating #(
    .NoFpgaGate(1'b1)
  ) u_${k}_cg (
    .clk_i(clk_${v}_root),
    .en_i(${k}_sw_en & clk_${v}_en),
    .test_en_i(${k}_scanmode == lc_ctrl_pkg::On),
    .clk_o(clocks_o.${k})
  );

% endfor

  ////////////////////////////////////////////////////
  // Software hint group
  // The idle hint feedback is assumed to be synchronous to the
  // clock target
  ////////////////////////////////////////////////////

% for k in hint_clks:
  logic ${k}_hint;
  logic ${k}_en;
% endfor

% for k,v in hint_clks.items():
  assign ${k}_en = ${k}_hint | ~idle_i[${v["name"].capitalize()}];

  prim_flop_2sync #(
    .Width(1)
  ) u_${k}_hint_sync (
    .clk_i(clk_${v["src"]}_i),
    .rst_ni(rst_${v["src"]}_ni),
    .d_i(reg2hw.clk_hints.${k}_hint.q),
    .q_o(${k}_hint)
  );

  lc_ctrl_pkg::lc_tx_t ${k}_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_${k}_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(${k}_scanmode)
  );

  prim_clock_gating #(
    .NoFpgaGate(1'b1)
  ) u_${k}_cg (
    .clk_i(clk_${v["src"]}_root),
    .en_i(${k}_en & clk_${v["src"]}_en),
    .test_en_i(${k}_scanmode == lc_ctrl_pkg::On),
    .clk_o(clocks_o.${k})
  );

% endfor

  // state readback
% for k,v in hint_clks.items():
  assign hw2reg.clk_hints_status.${k}_val.de = 1'b1;
  assign hw2reg.clk_hints_status.${k}_val.d = ${k}_en;
% endfor

  assign jitter_en_o = reg2hw.jitter_enable.q;

  ////////////////////////////////////////////////////
  // Exported clocks
  ////////////////////////////////////////////////////

% for intf, eps in export_clks.items():
  % for ep, clks in eps.items():
    % for clk in clks:
  assign clocks_${intf}_o.clk_${intf}_${ep}_${clk} = clocks_o.clk_${clk};
    % endfor
  % endfor
% endfor

  ////////////////////////////////////////////////////
  // Assertions
  ////////////////////////////////////////////////////

  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)
% for intf in export_clks:
  `ASSERT_KNOWN(ExportClocksKownO_A, clocks_${intf}_o)
% endfor
  `ASSERT_KNOWN(ClocksKownO_A, clocks_o)

endmodule // clkmgr
