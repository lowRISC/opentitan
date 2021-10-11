// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// The overall clock manager

`include "prim_assert.sv"

  module clkmgr
    import clkmgr_pkg::*;
    import clkmgr_reg_pkg::*;
    import lc_ctrl_pkg::lc_tx_t;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  // Primary module control clocks and resets
  // This drives the register interface
  input clk_i,
  input rst_ni,

  // System clocks and resets
  // These are the source clocks for the system
% for src in clocks.srcs.values():
  input clk_${src.name}_i,
  input rst_${src.name}_ni,
% endfor

  // Resets for derived clocks
  // clocks are derived locally
% for src_name in clocks.derived_srcs:
  input rst_${src_name}_ni,
% endfor

  // Bus Interface
  input tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // pwrmgr interface
  input pwrmgr_pkg::pwr_clk_req_t pwr_i,
  output pwrmgr_pkg::pwr_clk_rsp_t pwr_o,

  // dft interface
  input lc_tx_t scanmode_i,

  // idle hints
  input [${len(typed_clocks.hint_clks)-1}:0] idle_i,

  // life cycle state output
  input lc_tx_t lc_dft_en_i,

  // clock bypass control
  input lc_tx_t lc_clk_byp_req_i,
  output lc_tx_t ast_clk_byp_req_o,
  input lc_tx_t ast_clk_byp_ack_i,
  output lc_tx_t lc_clk_byp_ack_o,

  // jittery enable
  output logic jitter_en_o,

  // clock gated indications going to alert handlers
  output clkmgr_cg_en_t cg_en_o,

  // clock output interface
% for intf in cfg['exported_clks']:
  output clkmgr_${intf}_out_t clocks_${intf}_o,
% endfor
  output clkmgr_out_t clocks_o

);

  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;

  ////////////////////////////////////////////////////
  // Divided clocks
  ////////////////////////////////////////////////////

  lc_tx_t step_down_req;
  logic [${len(clocks.derived_srcs)-1}:0] step_down_acks;

% for src_name in clocks.derived_srcs:
  logic clk_${src_name}_i;
% endfor

% for src in clocks.derived_srcs.values():

  lc_tx_t ${src.name}_div_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_${src.name}_div_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(${src.name}_div_scanmode)
  );

  prim_clock_div #(
    .Divisor(${src.div})
  ) u_no_scan_${src.name}_div (
    .clk_i(clk_${src.src.name}_i),
    .rst_ni(rst_${src.src.name}_ni),
    .step_down_req_i(step_down_req == lc_ctrl_pkg::On),
    .step_down_ack_o(step_down_acks[${loop.index}]),
    .test_en_i(${src.name}_div_scanmode == lc_ctrl_pkg::On),
    .clk_o(clk_${src.name}_i)
  );
% endfor

  ////////////////////////////////////////////////////
  // Register Interface
  ////////////////////////////////////////////////////

  logic [NumAlerts-1:0] alert_test, alerts;
  clkmgr_reg_pkg::clkmgr_reg2hw_t reg2hw;
  clkmgr_reg_pkg::clkmgr_hw2reg_t hw2reg;

  clkmgr_reg_top u_reg (
    .clk_i,
    .rst_ni,
% for src in typed_clocks.rg_srcs:
    .clk_${src}_i,
    .rst_${src}_ni,
% endfor
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .intg_err_o(hw2reg.fatal_err_code.de),
    .devmode_i(1'b1)
  );
  assign hw2reg.fatal_err_code.d = 1'b1;


  ////////////////////////////////////////////////////
  // Alerts
  ////////////////////////////////////////////////////

  assign alert_test = {
    reg2hw.alert_test.fatal_fault.q & reg2hw.alert_test.fatal_fault.qe,
    reg2hw.alert_test.recov_fault.q & reg2hw.alert_test.recov_fault.qe
  };

  logic recov_alert;
  assign recov_alert =
% for src in typed_clocks.rg_srcs:
    hw2reg.recov_err_code.${src}_measure_err.de${";" if loop.last else " |"}
% endfor

  assign alerts = {
    |reg2hw.fatal_err_code,
    recov_alert
  };

  localparam logic [NumAlerts-1:0] AlertFatal = {1'b1, 1'b0};

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(AlertFatal[i])
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alerts[i]     ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  ////////////////////////////////////////////////////
  // Clock bypass request
  ////////////////////////////////////////////////////

  clkmgr_byp #(
    .NumDivClks(${len(clocks.derived_srcs)})
  ) u_clkmgr_byp (
    .clk_i,
    .rst_ni,
    .en_i(lc_dft_en_i),
    .byp_req_i(lc_tx_t'(reg2hw.extclk_ctrl.sel.q)),
    .step_down_req_i(lc_tx_t'(reg2hw.extclk_ctrl.step_down.q)),
    .ast_clk_byp_req_o,
    .ast_clk_byp_ack_i,
    .lc_clk_byp_req_i,
    .lc_clk_byp_ack_o,
    .step_down_acks_i(step_down_acks),
    .step_down_req_o(step_down_req)
  );

  ////////////////////////////////////////////////////
  // Feed through clocks
  // Feed through clocks do not actually need to be in clkmgr, as they are
  // completely untouched. The only reason they are here is for easier
  // bundling management purposes through clocks_o
  ////////////////////////////////////////////////////
% for k,v in typed_clocks.ft_clks.items():
  prim_clock_buf u_${k}_buf (
    .clk_i(clk_${v.src.name}_i),
    .clk_o(clocks_o.${k})
  );

  // clock gated indication for alert handler: these clocks are never gated.
  assign cg_en_o.${k.split('clk_')[-1]} = MuBi4False;
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
% for src in typed_clocks.rg_srcs:
  logic clk_${src}_root;
  logic clk_${src}_en;
% endfor

% for src in typed_clocks.rg_srcs:
  lc_tx_t ${src}_scanmode;
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
% for src in typed_clocks.rg_srcs:
    % if loop.last:
    clk_${src}_en;
    % else:
    clk_${src}_en &
    % endif
% endfor

  // an async OR of all the synchronized enables
  // return feedback to pwrmgr only when all clocks are disabled
  assign wait_disable =
% for src in typed_clocks.rg_srcs:
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
  // Clock Measurement for the roots
  ////////////////////////////////////////////////////

<% aon_freq = clocks.all_srcs['aon'].freq %>\
% for src in typed_clocks.rg_srcs:
  logic ${src}_fast_err;
  logic ${src}_slow_err;
  <%
   freq = clocks.all_srcs[src].freq
   cnt = int(freq*2 / aon_freq)
  %>\
  prim_clock_meas #(
    .Cnt(${cnt}),
    .RefCnt(1)
  ) u_${src}_meas (
    .clk_i(clk_${src}_i),
    .rst_ni(rst_${src}_ni),
    .clk_ref_i(clk_aon_i),
    .rst_ref_ni(rst_aon_ni),
    .en_i(clk_${src}_en & reg2hw.${src}_measure_ctrl.en.q),
    .max_cnt(reg2hw.${src}_measure_ctrl.max_thresh.q),
    .min_cnt(reg2hw.${src}_measure_ctrl.min_thresh.q),
    .valid_o(),
    .fast_o(${src}_fast_err),
    .slow_o(${src}_slow_err)
  );

  logic synced_${src}_err;
  prim_pulse_sync u_${src}_err_sync (
    .clk_src_i(clk_${src}_i),
    .rst_src_ni(rst_${src}_ni),
    .src_pulse_i(${src}_fast_err | ${src}_slow_err),
    .clk_dst_i(clk_i),
    .rst_dst_ni(rst_ni),
    .dst_pulse_o(synced_${src}_err)
  );

  assign hw2reg.recov_err_code.${src}_measure_err.d = 1'b1;
  assign hw2reg.recov_err_code.${src}_measure_err.de = synced_${src}_err;

% endfor

  ////////////////////////////////////////////////////
  // Clocks with only root gate
  ////////////////////////////////////////////////////
% for k,v in typed_clocks.rg_clks.items():
  assign clocks_o.${k} = clk_${v.src.name}_root;

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_${k} (
    .clk_i(clk_${v.src.name}_i),
    .rst_ni(rst_${v.src.name}_ni),
    .mubi_i(((clk_${v.src.name}_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.${k.split('clk_')[-1]})
  );
% endfor

  ////////////////////////////////////////////////////
  // Software direct control group
  ////////////////////////////////////////////////////

% for k in typed_clocks.sw_clks:
  logic ${k}_sw_en;
% endfor

% for k,v in typed_clocks.sw_clks.items():
  prim_flop_2sync #(
    .Width(1)
  ) u_${k}_sw_en_sync (
    .clk_i(clk_${v.src.name}_i),
    .rst_ni(rst_${v.src.name}_ni),
    .d_i(reg2hw.clk_enables.${k}_en.q),
    .q_o(${k}_sw_en)
  );

  lc_tx_t ${k}_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_${k}_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(${k}_scanmode)
  );

  logic ${k}_combined_en;
  assign ${k}_combined_en = ${k}_sw_en & clk_${v.src.name}_en;
  prim_clock_gating #(
    .FpgaBufGlobal(1'b1) // This clock spans across multiple clock regions.
  ) u_${k}_cg (
    .clk_i(clk_${v.src.name}_root),
    .en_i(${k}_combined_en),
    .test_en_i(${k}_scanmode == lc_ctrl_pkg::On),
    .clk_o(clocks_o.${k})
  );

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_${k} (
    .clk_i(clk_${v.src.name}_i),
    .rst_ni(rst_${v.src.name}_ni),
    .mubi_i(((${k}_combined_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.${k.split('clk_')[-1]})
  );

% endfor

  ////////////////////////////////////////////////////
  // Software hint group
  // The idle hint feedback is assumed to be synchronous to the
  // clock target
  ////////////////////////////////////////////////////

% for clk in typed_clocks.hint_clks.keys():
  logic ${clk}_hint;
  logic ${clk}_en;
% endfor

% for clk, sig in typed_clocks.hint_clks.items():
  assign ${clk}_en = ${clk}_hint | ~idle_i[${hint_names[clk]}];

  prim_flop_2sync #(
    .Width(1)
  ) u_${clk}_hint_sync (
    .clk_i(clk_${sig.src.name}_i),
    .rst_ni(rst_${sig.src.name}_ni),
    .d_i(reg2hw.clk_hints.${clk}_hint.q),
    .q_o(${clk}_hint)
  );

  lc_tx_t ${clk}_scanmode;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_${clk}_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(${clk}_scanmode)
  );

  // Add a prim buf here to make sure the CG and the lc sender inputs
  // are derived from the same physical signal.
  logic ${clk}_combined_en;
  prim_buf u_prim_buf_${clk}_en (
    .in_i(${clk}_en & clk_${sig.src.name}_en),
    .out_o(${clk}_combined_en)
  );

  prim_clock_gating #(
    .FpgaBufGlobal(1'b0) // This clock is used primarily locally.
  ) u_${clk}_cg (
    .clk_i(clk_${sig.src.name}_root),
    .en_i(${clk}_combined_en),
    .test_en_i(${clk}_scanmode == lc_ctrl_pkg::On),
    .clk_o(clocks_o.${clk})
  );

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_${clk} (
    .clk_i(clk_${sig.src.name}_i),
    .rst_ni(rst_${sig.src.name}_ni),
    .mubi_i(((${clk}_combined_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.${clk.split('clk_')[-1]})
  );

% endfor

  // state readback
% for clk in typed_clocks.hint_clks.keys():
  assign hw2reg.clk_hints_status.${clk}_val.de = 1'b1;
  assign hw2reg.clk_hints_status.${clk}_val.d = ${clk}_en;
% endfor

  assign jitter_en_o = reg2hw.jitter_enable.q;

  ////////////////////////////////////////////////////
  // Exported clocks
  ////////////////////////////////////////////////////

% for intf, eps in cfg['exported_clks'].items():
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
  `ASSERT_KNOWN(AlertsKnownO_A,   alert_tx_o)
  `ASSERT_KNOWN(PwrMgrKnownO_A, pwr_o)
  `ASSERT_KNOWN(AstClkBypReqKnownO_A, ast_clk_byp_req_o)
  `ASSERT_KNOWN(LcCtrlClkBypAckKnownO_A, lc_clk_byp_ack_o)
  `ASSERT_KNOWN(JitterEnableKnownO_A, jitter_en_o)
% for intf in cfg['exported_clks']:
  `ASSERT_KNOWN(ExportClocksKownO_A, clocks_${intf}_o)
% endfor
  `ASSERT_KNOWN(ClocksKownO_A, clocks_o)
  `ASSERT_KNOWN(CgEnKnownO_A, cg_en_o)

endmodule // clkmgr
