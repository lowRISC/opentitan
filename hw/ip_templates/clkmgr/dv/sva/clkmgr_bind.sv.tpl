// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module clkmgr_bind;
`ifndef GATE_LEVEL
  bind clkmgr tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (.clk_i, .rst_ni, .h2d(tl_i), .d2h(tl_o));

  // In top-level testbench, do not bind the csr_assert_fpv to reduce simulation time.
`ifndef TOP_LEVEL_DV
  bind clkmgr clkmgr_csr_assert_fpv clkmgr_csr_assert (.clk_i, .rst_ni, .h2d(tl_i), .d2h(tl_o));
`endif

% for src_clk in src_clks.values():
  % if src_clk['name'] != 'aon':
<% is_usb = 1 if src_clk['name'] == 'usb' else 0 %>\
  bind clkmgr clkmgr_pwrmgr_sva_if #(.IS_USB(${is_usb})) clkmgr_pwrmgr_${src_clk['name']}_sva_if (
    .clk_i,
    .rst_ni,
    .clk_en(pwr_i.${src_clk['name']}_ip_clk_en),
    .status(pwr_o.${src_clk['name']}_status)
  );

  % endif
% endfor
% for sw_clk, attr in typed_clocks['sw_clks'].items():
<%
  src_clk = derived_clks[attr['src_name']]['src'] if attr['src_name'] in derived_clks else src_clks[attr['src_name']]
%>\
  bind clkmgr clkmgr_gated_clock_sva_if clkmgr_${attr['src_name']}_peri_sva_if (
    .clk(clocks_o.clk_${attr['src_name']}_powerup),
    .rst_n(rst_${attr['src_name']}_ni),
    .ip_clk_en(pwr_i.${src_clk['name']}_ip_clk_en),
    .sw_clk_en(${sw_clk}_sw_en),
    .scanmode(scanmode_i == prim_mubi_pkg::MuBi4True),
    .gated_clk(clocks_o.${sw_clk})
  );

% endfor
  // Assertions for transactional clocks.
% for clk, sig in typed_clocks['hint_clks'].items():
  bind clkmgr clkmgr_trans_sva_if clkmgr_${sig['endpoint_ip']}_trans_sva_if (
    .clk(clk_${sig['src_name']}_i),
    .rst_n(rst_${sig['src_name']}_ni),
    .hint(reg2hw.clk_hints.${clk}_hint.q),
    .idle(idle_i[${hint_names[clk]}] == prim_mubi_pkg::MuBi4True),
    .scanmode(scanmode_i == prim_mubi_pkg::MuBi4True),
    .status(hw2reg.clk_hints_status.${clk}_val.d),
    .trans_clk(clocks_o.${clk})
  );

% endfor
  bind clkmgr clkmgr_extclk_sva_if clkmgr_extclk_sva_if (
    .clk_i,
    .rst_ni,
    .extclk_ctrl_sel,
    .extclk_ctrl_hi_speed_sel,
    .lc_hw_debug_en_i,
    .lc_clk_byp_req_i,
    .io_clk_byp_req_o,
    .all_clk_byp_req_o,
    .hi_speed_sel_o
  );

  bind clkmgr clkmgr_div_sva_if #(
    .DIV(2)
  ) clkmgr_div2_sva_if (
    .clk(clocks_o.clk_io_powerup),
    .rst_n(rst_ni),
    .maybe_divided_clk(clocks_o.clk_io_div2_powerup),
    .div_step_down_req_i(div_step_down_req_i == prim_mubi_pkg::MuBi4True),
    .scanmode(scanmode_i == prim_mubi_pkg::MuBi4True)
  );

  // The div2 clk also steps, so not a good reference. Instead, check it always tracks io_div2.
  bind clkmgr clkmgr_div_sva_if #(
    .DIV(4)
  ) clkmgr_div4_sva_if (
    .clk(clocks_o.clk_io_div2_powerup),
    .rst_n(rst_ni),
    .maybe_divided_clk(clocks_o.clk_io_div4_powerup),
    .div_step_down_req_i(div_step_down_req_i == prim_mubi_pkg::MuBi4True),
    .scanmode(scanmode_i == prim_mubi_pkg::MuBi4True)
  );

  // AON clock gating enables.
% for clk in sorted(typed_clocks['ft_clks']):
<% suffix = clk.split('clk_')[-1] %>\
  bind clkmgr clkmgr_aon_cg_en_sva_if clkmgr_aon_cg_${suffix} (
    .cg_en(cg_en_o.${suffix} == prim_mubi_pkg::MuBi4True)
  );

% endfor
  // Non-AON clock gating enables with no software control.
% for clk, sig in sorted(typed_clocks['rg_clks'].items(), key=lambda p: p[0]):
<% suffix = clk.split('clk_')[-1] %>\
  bind clkmgr clkmgr_cg_en_sva_if clkmgr_cg_${suffix} (
    .clk(clk_${sig['src_name']}),
    .rst_n(rst_${sig['src_name']}_ni),
    .ip_clk_en(clk_${sig['src_name']}_en),
    .sw_clk_en(1'b1),
    .scanmode(prim_mubi_pkg::MuBi4False),
    .cg_en(cg_en_o.${suffix} == prim_mubi_pkg::MuBi4True)
  );

% endfor
  // Software controlled gating enables.
% for clk, sig in typed_clocks['sw_clks'].items():
<% suffix = clk.split('clk_')[-1] %>\
  bind clkmgr clkmgr_cg_en_sva_if clkmgr_cg_${suffix} (
    .clk(clk_${sig['src_name']}),
    .rst_n(rst_${sig['src_name']}_ni),
    .ip_clk_en(clk_${sig['src_name']}_en),
    .sw_clk_en(${clk}_sw_en),
    .scanmode(prim_mubi_pkg::MuBi4False),
    .cg_en(cg_en_o.${suffix} == prim_mubi_pkg::MuBi4True)
  );

%endfor
  // Hint controlled gating enables.
% for clk, sig in typed_clocks['hint_clks'].items():
<% suffix = clk.split('clk_')[-1] %>\
  bind clkmgr clkmgr_cg_en_sva_if clkmgr_cg_${suffix} (
    .clk(clk_${sig['src_name']}_i),
    .rst_n(rst_${sig['src_name']}_ni),
    .ip_clk_en(clk_${sig['src_name']}_en),
    .sw_clk_en(u_${clk}_trans.sw_hint_synced || !u_${clk}_trans.idle_valid),
    .scanmode(prim_mubi_pkg::MuBi4False),
    .cg_en(cg_en_o.${suffix} == prim_mubi_pkg::MuBi4True)
  );

 % endfor
  // Calibration assertions.
  bind clkmgr clkmgr_lost_calib_regwen_sva_if clkmgr_lost_calib_regwen_sva_if (
    .clk(clk_i),
    .rst_n(rst_ni),
    .calib_rdy(calib_rdy_i),
    .meas_ctrl_regwen(u_reg.measure_ctrl_regwen_qs)
  );

% for clk in sorted(src_clks):
  % if clk != 'aon':
  bind clkmgr clkmgr_lost_calib_ctrl_en_sva_if clkmgr_lost_calib_${clk}_ctrl_en_sva_if (
    .clk(clk_i),
    .rst_n(rst_ni),
    .calib_rdy(calib_rdy_i),
    .meas_ctrl_en(u_reg.${clk}_meas_ctrl_en_qs)
  );

  % endif
% endfor
% for clk in derived_clks:
  bind clkmgr clkmgr_lost_calib_ctrl_en_sva_if clkmgr_lost_calib_${clk}_ctrl_en_sva_if (
    .clk(clk_i),
    .rst_n(rst_ni),
    .calib_rdy(calib_rdy_i),
    .meas_ctrl_en(u_reg.${clk}_meas_ctrl_en_qs)
  );

% endfor
  bind clkmgr clkmgr_sec_cm_checker_assert clkmgr_sec_cm_checker_assert (
    .clk_i,
    .rst_ni,
    .all_clk_byp_req_o,
    .lc_hw_debug_en_i,
    .lc_clk_byp_req_i,
    .lc_clk_byp_ack_o,
    .io_clk_byp_req_o,
    // internal signal is picked due to inconsistent t->f, f->t delay
    .io_clk_byp_ack(u_clkmgr_byp.io_clk_byp_ack),
    // internal signal is picked due to inconsistent input to signal delay
    .step_down_acks_sync(u_clkmgr_byp.step_down_acks_sync),
    .extclk_ctrl_sel
  );
`endif
endmodule : clkmgr_bind
