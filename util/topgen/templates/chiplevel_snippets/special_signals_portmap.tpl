## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%from topgen.merge import alert_handler_signals%>\
<%page args="top, feature_info, cio_info, gen_bkdr_loader, domain"/>\
<%
  clkmgr = lib.find_module(top['module'], 'clkmgr')
  rstmgr = lib.find_module(top['module'], 'rstmgr')
  domain_clkmgr = clkmgr.get('domain')
  domain_rstmgr = rstmgr.get('domain')
%>\
% if domain_clkmgr == domain:
    // All externally supplied clocks
    .clk_main_i(ast_base_clks.clk_sys),
    .clk_io_i  (ast_base_clks.clk_io ),
% if feature_info["has_usb"]:
    .clk_usb_i (ast_base_clks.clk_usb),
% endif
    .clk_aon_i (ast_base_clks.clk_aon),
% else:
    // Clocks and clock gating control from ${clkmgr['name']}
    .${clkmgr['name']}_clocks_i(${clkmgr['name']}_clocks),
    .${clkmgr['name']}_cg_en_i (${clkmgr['name']}_cg_en),
% endif

% if domain_rstmgr != domain:
    // Resets and reset assert info from ${rstmgr['name']}
    .${rstmgr['name']}_resets_i(${rstmgr['name']}_resets),
    .${rstmgr['name']}_rst_en_i(${rstmgr['name']}_rst_en),

% endif\

    // Manual DFT signals
    .scan_rst_ni(scan_rst_n),
% if feature_info["has_scan_en"][domain]:
    .scan_en_i  (scan_en   ),
% endif
    .scanmode_i (scanmode  ),

% if feature_info["has_pinmux"]:
% if lib.find_module(top["module"], "pinmux").get("domain") == domain:
% if cio_info["num_mio_pads"] != 0:
% if gen_bkdr_loader:
    // Multiplexed I/O to backdoor
    .mio_in_i (mio_bkdr_in ),
    .mio_out_o(mio_bkdr_out),
    .mio_oe_o (mio_bkdr_oe ),
% else:
    // Multiplexed I/O
    .mio_in_i (mio_in ),
    .mio_out_o(mio_out),
    .mio_oe_o (mio_oe ),
% endif

% endif
% if cio_info["num_dio_total"] != 0:
    // Dedicated I/O
    .dio_in_i (dio_in ),
    .dio_out_o(dio_out),
    .dio_oe_o (dio_oe ),

% endif
    // Pad attributes
% if gen_bkdr_loader:
    .mio_attr_o(mio_bkdr_attr),
% else:
    .mio_attr_o(mio_attr),
% endif
    .dio_attr_o(dio_attr),

% endif
% endif\

    // Special inter-power domain signals (interrupts, alerts)
% for name, plic in top["plic_info"].items():
<% prefix = "_" + name if len(top["plic_info"]) > 1 else "" %>\
% if plic["domain"] == domain:
  % for pd in top["power"]["domains"]:
<% if pd == domain: continue %>\
    % if plic["count_pd"][pd] > 0:
<% chiplevel_sig = f"intr_vector{prefix}_pd_{pd.lower()}" %>\
    .${chiplevel_sig}_i(${chiplevel_sig}),
    % endif
  % endfor
% else:
  % if plic["count_pd"][domain] > 0:
<% chiplevel_sig = f"intr_vector{prefix}_pd_{domain.lower()}" %>\
    .intr_vector${prefix}_o(${chiplevel_sig}),
  % endif
% endif
% endfor

% if feature_info["has_alert_handler"]:
% for name, ah in top["alert_handler_info"].items():
<% signals = alert_handler_signals(name) %>\
% if ah["domain"] == domain:
  % for pd in top["power"]["domains"]:
<% if pd == domain: continue %>\
<% pd_len = ah["count_pd"][pd] - 1 %>\
    % if pd_len >= 0:
<% chiplevel_sigs = (f"{signals[0]}_pd_{pd.lower()}", f"{signals[1]}_pd_{pd.lower()}") %>\
    .${chiplevel_sigs[0]}_i(${chiplevel_sigs[0]}),
    .${chiplevel_sigs[1]}_o(${chiplevel_sigs[1]}),
    % endif
  % endfor
% else:
<% pd_len = ah["count_pd"][domain] - 1 %>\
  % if pd_len >= 0:
<% chiplevel_sigs = (f"{signals[0]}_pd_{domain.lower()}", f"{signals[1]}_pd_{domain.lower()}") %>\
    .${signals[0]}_o(${chiplevel_sigs[0]}),
    .${signals[1]}_i(${chiplevel_sigs[1]}),
  % endif
% endif
% endfor
% endif\
