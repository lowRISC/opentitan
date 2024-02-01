// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// The overall clock manager

<%
from collections import OrderedDict
from topgen.lib import Name
all_derived_srcs = list(sorted(set([dc['src']['name']
                                    for dc in derived_clks.values()])))
all_srcs = src_clks.copy()
all_srcs.update(derived_clks)
rg_srcs = list(sorted({sig['src_name'] for sig
                       in typed_clocks['rg_clks'].values()}))
%>\

`include "prim_assert.sv"

  module clkmgr
    import clkmgr_pkg::*;
    import clkmgr_reg_pkg::*;
    import lc_ctrl_pkg::lc_tx_t;
    import prim_mubi_pkg::mubi4_t;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  // Primary module control clocks and resets
  // This drives the register interface
  input clk_i,
  input rst_ni,
  input rst_shadowed_ni,

  // System clocks and resets
  // These are the source clocks for the system
% for src in src_clks.values():
  input clk_${src['name']}_i,
  input rst_${src['name']}_ni,
% endfor

  // Resets for derived clocks
  // clocks are derived locally
% for src_name in derived_clks.keys():
  input rst_${src_name}_ni,
% endfor

  // Resets for derived clock generation, root clock gating and related status
  input rst_root_ni,
% for clk_family in parent_child_clks.values():
  % for src in clk_family:
  input rst_root_${src}_ni,
  % endfor
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
  input prim_mubi_pkg::mubi4_t scanmode_i,

  // idle hints
  // SEC_CM: IDLE.INTERSIG.MUBI
  input prim_mubi_pkg::mubi4_t [${len(hint_names)-1}:0] idle_i,

  // life cycle state output
  // SEC_CM: LC_CTRL.INTERSIG.MUBI
  input lc_tx_t lc_hw_debug_en_i,

  // clock bypass control with lc_ctrl
  // SEC_CM: LC_CTRL_CLK_HANDSHAKE.INTERSIG.MUBI
  input lc_tx_t lc_clk_byp_req_i,
  output lc_tx_t lc_clk_byp_ack_o,

  // clock bypass control with ast
  // SEC_CM: CLK_HANDSHAKE.INTERSIG.MUBI
  output mubi4_t io_clk_byp_req_o,
  input mubi4_t io_clk_byp_ack_i,
  output mubi4_t all_clk_byp_req_o,
  input mubi4_t all_clk_byp_ack_i,
  output mubi4_t hi_speed_sel_o,

  // clock calibration has been done.
  // If this is signal is 0, assume clock frequencies to be
  // uncalibrated.
  input prim_mubi_pkg::mubi4_t calib_rdy_i,

  // jittery enable to ast
  output mubi4_t jitter_en_o,

  // external indication for whether dividers should be stepped down
  // SEC_CM: DIV.INTERSIG.MUBI
  input mubi4_t div_step_down_req_i,

  // clock gated indications going to alert handlers
  output clkmgr_cg_en_t cg_en_o,

  // clock output interface
% for intf in exported_clks:
  output clkmgr_${intf}_out_t clocks_${intf}_o,
% endfor
  output clkmgr_out_t clocks_o

);

  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;
  import prim_mubi_pkg::mubi4_test_true_strict;
  import prim_mubi_pkg::mubi4_test_true_loose;
  import prim_mubi_pkg::mubi4_test_false_strict;

  // Hookup point for OCC's on root clocks.
% for src in src_clks.values():
<% clk_name = src['name'] %>\
  logic clk_${clk_name};
  prim_clock_buf #(
    .NoFpgaBuf(1'b1)
  ) u_clk_${clk_name}_buf (
    .clk_i(clk_${clk_name}_i),
    .clk_o(clk_${clk_name})
  );
% endfor

  ////////////////////////////////////////////////////
  // External step down request
  ////////////////////////////////////////////////////
% for src_name in all_derived_srcs:
  mubi4_t ${src_name}_step_down_req;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(1),
    .StabilityCheck(1),
    .ResetValue(MuBi4False)
  ) u_${src_name}_step_down_req_sync (
    .clk_i(clk_${src_name}),
    .rst_ni(rst_${src_name}_ni),
    .mubi_i(div_step_down_req_i),
    .mubi_o({${src_name}_step_down_req})
  );

% endfor

  ////////////////////////////////////////////////////
  // Divided clocks
  // Note divided clocks must use the por version of
  // its related reset to ensure clock division
  // can happen without any dependency
  ////////////////////////////////////////////////////

  logic [${len(derived_clks)-1}:0] step_down_acks;

% for src_name in derived_clks:
  logic clk_${src_name};
% endfor

% for src in derived_clks.values():

  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] ${src['name']}_div_scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_${src['name']}_div_scanmode_sync  (
    .clk_i,
    .rst_ni,
    .mubi_i(scanmode_i),
    .mubi_o({${src['name']}_div_scanmode})
  );

  prim_clock_div #(
    .Divisor(${src['div']})
  ) u_no_scan_${src['name']}_div (
    // We're using the pre-occ hookup (*_i) version for clock derivation.
    .clk_i(clk_${src['src']['name']}_i),
    .rst_ni(rst_root_${src['src']['name']}_ni),
    .step_down_req_i(mubi4_test_true_strict(${src['src']['name']}_step_down_req)),
    .step_down_ack_o(step_down_acks[${loop.index}]),
    .test_en_i(mubi4_test_true_strict(${src['name']}_div_scanmode[0])),
    .clk_o(clk_${src['name']})
  );
% endfor

  ////////////////////////////////////////////////////
  // Register Interface
  ////////////////////////////////////////////////////

  logic [NumAlerts-1:0] alert_test, alerts;
  clkmgr_reg_pkg::clkmgr_reg2hw_t reg2hw;
  clkmgr_reg_pkg::clkmgr_hw2reg_t hw2reg;

  // SEC_CM: MEAS.CONFIG.REGWEN
  // SEC_CM: MEAS.CONFIG.SHADOW
  // SEC_CM: CLK_CTRL.CONFIG.REGWEN
  clkmgr_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .rst_shadowed_ni,
% for src in rg_srcs:
    .clk_${src}_i(clk_${src}),
    .rst_${src}_ni,
% endfor
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .shadowed_storage_err_o(hw2reg.fatal_err_code.shadow_storage_err.de),
    .shadowed_update_err_o(hw2reg.recov_err_code.shadow_update_err.de),
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o(hw2reg.fatal_err_code.reg_intg.de)
  );
  assign hw2reg.fatal_err_code.reg_intg.d = 1'b1;
  assign hw2reg.recov_err_code.shadow_update_err.d = 1'b1;
  assign hw2reg.fatal_err_code.shadow_storage_err.d = 1'b1;

  ////////////////////////////////////////////////////
  // Alerts
  ////////////////////////////////////////////////////

  assign alert_test = {
    reg2hw.alert_test.fatal_fault.q & reg2hw.alert_test.fatal_fault.qe,
    reg2hw.alert_test.recov_fault.q & reg2hw.alert_test.recov_fault.qe
  };

  logic recov_alert;
  assign recov_alert =
% for src in rg_srcs:
    hw2reg.recov_err_code.${src}_measure_err.de |
    hw2reg.recov_err_code.${src}_timeout_err.de |
% endfor
    hw2reg.recov_err_code.shadow_update_err.de;

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

  mubi4_t extclk_ctrl_sel;
  mubi4_t extclk_ctrl_hi_speed_sel;

  assign extclk_ctrl_sel = mubi4_t'(reg2hw.extclk_ctrl.sel.q);
  assign extclk_ctrl_hi_speed_sel = mubi4_t'(reg2hw.extclk_ctrl.hi_speed_sel.q);

  clkmgr_byp #(
    .NumDivClks(${len(derived_clks)})
  ) u_clkmgr_byp (
    .clk_i,
    .rst_ni,
    .en_i(lc_hw_debug_en_i),
    .lc_clk_byp_req_i,
    .lc_clk_byp_ack_o,
    .byp_req_i(extclk_ctrl_sel),
    .byp_ack_o(hw2reg.extclk_status.d),
    .hi_speed_sel_i(extclk_ctrl_hi_speed_sel),
    .all_clk_byp_req_o,
    .all_clk_byp_ack_i,
    .io_clk_byp_req_o,
    .io_clk_byp_ack_i,
    .hi_speed_sel_o,

    // divider step down controls
    .step_down_acks_i(step_down_acks)
  );

  ////////////////////////////////////////////////////
  // Feed through clocks
  // Feed through clocks do not actually need to be in clkmgr, as they are
  // completely untouched. The only reason they are here is for easier
  // bundling management purposes through clocks_o
  ////////////////////////////////////////////////////
% for k,v in typed_clocks['ft_clks'].items():
  prim_clock_buf u_${k}_buf (
    .clk_i(clk_${v['src_name']}),
    .clk_o(clocks_o.${k})
  );

  // clock gated indication for alert handler: these clocks are never gated.
  assign cg_en_o.${k.split('clk_')[-1]} = MuBi4False;
% endfor

  ////////////////////////////////////////////////////
  // Distribute pwrmgr ip_clk_en requests to each family
  ////////////////////////////////////////////////////
% for root, clk_family in parent_child_clks.items():
  // clk_${root} family
  % for clk in clk_family:
  logic pwrmgr_${clk}_en;
  % endfor
  % for clk in clk_family:
  assign pwrmgr_${clk}_en = pwr_i.${root}_ip_clk_en;
  % endfor
% endfor

  ////////////////////////////////////////////////////
  // Root gating
  ////////////////////////////////////////////////////

% for root, clk_family in parent_child_clks.items():
  // clk_${root} family
  logic [${len(clk_family)-1}:0] ${root}_ens;

  % for src in clk_family:
  logic clk_${src}_en;
  logic clk_${src}_root;
  clkmgr_root_ctrl u_${src}_root_ctrl (
    .clk_i(clk_${src}),
    .rst_ni(rst_root_${src}_ni),
    .scanmode_i,
    .async_en_i(pwrmgr_${src}_en),
    .en_o(clk_${src}_en),
    .clk_o(clk_${src}_root)
  );
  assign ${root}_ens[${loop.index}] = clk_${src}_en;

  % endfor
  // create synchronized status
  clkmgr_clk_status #(
    .NumClocks(${len(clk_family)})
  ) u_${root}_status (
    .clk_i,
    .rst_ni(rst_root_ni),
    .ens_i(${root}_ens),
    .status_o(pwr_o.${root}_status)
  );

% endfor
  ////////////////////////////////////////////////////
  // Clock Measurement for the roots
  // SEC_CM: TIMEOUT.CLK.BKGN_CHK, MEAS.CLK.BKGN_CHK
  ////////////////////////////////////////////////////

  typedef enum logic [${(len(rg_srcs) + 1).bit_length() - 1}:0] {
    BaseIdx,
% for src in rg_srcs:
    Clk${Name.from_snake_case(src).as_camel_case()}Idx,
% endfor
    CalibRdyLastIdx
  } clkmgr_calib_idx_e;

  // if clocks become uncalibrated, allow the measurement control configurations to change
  mubi4_t [CalibRdyLastIdx-1:0] calib_rdy;
  prim_mubi4_sync #(
    .AsyncOn(1),
    .NumCopies(int'(CalibRdyLastIdx)),
    .ResetValue(MuBi4False)
  ) u_calib_rdy_sync (
    .clk_i,
    .rst_ni,
    .mubi_i(calib_rdy_i),
    .mubi_o({calib_rdy})
  );

  always_comb begin
    hw2reg.measure_ctrl_regwen.de = '0;
    hw2reg.measure_ctrl_regwen.d = reg2hw.measure_ctrl_regwen;

    if (mubi4_test_false_strict(calib_rdy[BaseIdx])) begin
      hw2reg.measure_ctrl_regwen.de = 1'b1;
      hw2reg.measure_ctrl_regwen.d = 1'b1;
    end
  end
<% aon_freq = src_clks['aon']['freq'] %>\
% for i, src in enumerate(rg_srcs):
<%
 freq = all_srcs[src]['freq']
 cnt = int(freq*2 / aon_freq)
 sel_idx = f"Clk{Name.from_snake_case(src).as_camel_case()}Idx"
%>
  clkmgr_meas_chk #(
    .Cnt(${cnt}),
    .RefCnt(1)
  ) u_${src}_meas (
    .clk_i,
    .rst_ni,
    .clk_src_i(clk_${src}),
    .rst_src_ni(rst_${src}_ni),
    .clk_ref_i(clk_aon),
    .rst_ref_ni(rst_aon_ni),
    // signals on source domain
    .src_en_i(clk_${src}_en & mubi4_test_true_loose(mubi4_t'(reg2hw.${src}_meas_ctrl_en))),
    .src_max_cnt_i(reg2hw.${src}_meas_ctrl_shadowed.hi.q),
    .src_min_cnt_i(reg2hw.${src}_meas_ctrl_shadowed.lo.q),
    .src_cfg_meas_en_i(mubi4_t'(reg2hw.${src}_meas_ctrl_en.q)),
    .src_cfg_meas_en_valid_o(hw2reg.${src}_meas_ctrl_en.de),
    .src_cfg_meas_en_o(hw2reg.${src}_meas_ctrl_en.d),
    // signals on local clock domain
    .calib_rdy_i(calib_rdy[${sel_idx}]),
    .meas_err_o(hw2reg.recov_err_code.${src}_measure_err.de),
    .timeout_err_o(hw2reg.recov_err_code.${src}_timeout_err.de)
  );

  assign hw2reg.recov_err_code.${src}_measure_err.d = 1'b1;
  assign hw2reg.recov_err_code.${src}_timeout_err.d = 1'b1;

% endfor

  ////////////////////////////////////////////////////
  // Clocks with only root gate
  ////////////////////////////////////////////////////
% for k,v in typed_clocks['rg_clks'].items():
  assign clocks_o.${k} = clk_${v['src_name']}_root;

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_${k} (
    .clk_i(clk_${v['src_name']}),
    .rst_ni(rst_${v['src_name']}_ni),
    .mubi_i(((clk_${v['src_name']}_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.${k.split('clk_')[-1]})
  );
% endfor

  ////////////////////////////////////////////////////
  // Software direct control group
  ////////////////////////////////////////////////////

% for k in typed_clocks['sw_clks']:
  logic ${k}_sw_en;
% endfor

% for k,v in typed_clocks['sw_clks'].items():
  prim_flop_2sync #(
    .Width(1)
  ) u_${k}_sw_en_sync (
    .clk_i(clk_${v['src_name']}),
    .rst_ni(rst_${v['src_name']}_ni),
    .d_i(reg2hw.clk_enables.${k}_en.q),
    .q_o(${k}_sw_en)
  );

  // Declared as size 1 packed array to avoid FPV warning.
  prim_mubi_pkg::mubi4_t [0:0] ${k}_scanmode;
  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(0)
  ) u_${k}_scanmode_sync  (
    .clk_i,
    .rst_ni,
    .mubi_i(scanmode_i),
    .mubi_o(${k}_scanmode)
  );

  logic ${k}_combined_en;
  assign ${k}_combined_en = ${k}_sw_en & clk_${v['src_name']}_en;
  prim_clock_gating #(
    .FpgaBufGlobal(1'b1) // This clock spans across multiple clock regions.
  ) u_${k}_cg (
    .clk_i(clk_${v['src_name']}),
    .en_i(${k}_combined_en),
    .test_en_i(mubi4_test_true_strict(${k}_scanmode[0])),
    .clk_o(clocks_o.${k})
  );

  // clock gated indication for alert handler
  prim_mubi4_sender #(
    .ResetValue(MuBi4True)
  ) u_prim_mubi4_sender_${k} (
    .clk_i(clk_${v['src_name']}),
    .rst_ni(rst_${v['src_name']}_ni),
    .mubi_i(((${k}_combined_en) ? MuBi4False : MuBi4True)),
    .mubi_o(cg_en_o.${k.split('clk_')[-1]})
  );

% endfor

  ////////////////////////////////////////////////////
  // Software hint group
  // The idle hint feedback is assumed to be synchronous to the
  // clock target
  ////////////////////////////////////////////////////

  logic [${len(typed_clocks['hint_clks'])-1}:0] idle_cnt_err;
% for clk, sig in typed_clocks['hint_clks'].items():
<%assert_name = Name.from_snake_case(clk)
%>
  clkmgr_trans #(
% if clk == "clk_main_kmac":
    .FpgaBufGlobal(1'b1) // KMAC is getting too big for a single clock region.
% else:
    .FpgaBufGlobal(1'b0) // This clock is used primarily locally.
% endif
  ) u_${clk}_trans (
    .clk_i(clk_${sig['src_name']}),
    .clk_gated_i(clk_${sig['src_name']}_root),
    .rst_ni(rst_${sig['src_name']}_ni),
    .en_i(clk_${sig['src_name']}_en),
    .idle_i(idle_i[${hint_names[clk]}]),
% if len(typed_clocks['hint_clks'].items()) > 1:
    .sw_hint_i(reg2hw.clk_hints.${clk}_hint.q),
% else:
    .sw_hint_i(reg2hw.clk_hints.q),
% endif
    .scanmode_i,
    .alert_cg_en_o(cg_en_o.${clk.split('clk_')[-1]}),
    .clk_o(clocks_o.${clk}),
    .clk_reg_i(clk_i),
    .rst_reg_ni(rst_ni),
% if len(typed_clocks['hint_clks'].items()) > 1:
    .reg_en_o(hw2reg.clk_hints_status.${clk}_val.d),
% else:
    .reg_en_o(hw2reg.clk_hints_status.d),
% endif
    .reg_cnt_err_o(idle_cnt_err[${hint_names[clk]}])
  );
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(
    ${assert_name.as_camel_case()}CountCheck_A,
    u_${clk}_trans.u_idle_cnt,
    alert_tx_o[1])
% endfor
  assign hw2reg.fatal_err_code.idle_cnt.d = 1'b1;
  assign hw2reg.fatal_err_code.idle_cnt.de = |idle_cnt_err;

  // state readback
% if len(typed_clocks['hint_clks'].items()) > 1:
% for clk in typed_clocks['hint_clks'].keys():
  assign hw2reg.clk_hints_status.${clk}_val.de = 1'b1;
% endfor
% else:
  assign hw2reg.clk_hints_status.de = 1'b1;
% endif

  // SEC_CM: JITTER.CONFIG.MUBI
  assign jitter_en_o = mubi4_t'(reg2hw.jitter_enable.q);

  ////////////////////////////////////////////////////
  // Exported clocks
  ////////////////////////////////////////////////////

% for intf, eps in exported_clks.items():
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
  `ASSERT_KNOWN(AllClkBypReqKnownO_A, all_clk_byp_req_o)
  `ASSERT_KNOWN(IoClkBypReqKnownO_A, io_clk_byp_req_o)
  `ASSERT_KNOWN(LcCtrlClkBypAckKnownO_A, lc_clk_byp_ack_o)
  `ASSERT_KNOWN(JitterEnableKnownO_A, jitter_en_o)
% for intf in exported_clks:
  `ASSERT_KNOWN(ExportClocksKownO_A, clocks_${intf}_o)
% endfor
  `ASSERT_KNOWN(ClocksKownO_A, clocks_o)
  `ASSERT_KNOWN(CgEnKnownO_A, cg_en_o)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[1])
endmodule // clkmgr
