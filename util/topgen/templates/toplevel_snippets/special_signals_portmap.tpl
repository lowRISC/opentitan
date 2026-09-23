## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%from topgen.merge import alert_handler_signals%>\
<%page args="top, feature_info, cio_info, domain"/>\
<%
  clkmgr = lib.find_module(top['module'], 'clkmgr')
  rstmgr = lib.find_module(top['module'], 'rstmgr')
  domain_clkmgr = clkmgr.get('domain')
  ## The reset tree is driven by the rstmgr's primary partition.
  domain_rstmgr = rstmgr.get('domain')
  ## Clocks sourced from another IP module's own generated clock (e.g. AST
  ## feeding clkmgr) are wired as internal nets/inter-module ports instead -
  ## see intermodule.resolve_module_clocks().
  clk_srcs = top['clocks'].srcs
  has_ext_clks = ((clk_srcs['main'].module is None)                            or
                  (clk_srcs['io'].module is None)                              or
                  (feature_info["has_usb"] and clk_srcs['usb'].module is None) or 
                  (clk_srcs['aon'].module is None))
%>\
% if domain_clkmgr == domain:
  % if has_ext_clks:
    // All externally supplied clocks
    % if clk_srcs['main'].module is None:
    .clk_main_i(ast_base_clks_i.clk_sys),
    % endif
    % if clk_srcs['io'].module is None:
    .clk_io_i  (ast_base_clks_i.clk_io ),
    % endif
    % if feature_info["has_usb"] and clk_srcs['usb'].module is None:
    .clk_usb_i (ast_base_clks_i.clk_usb),
    % endif
    % if clk_srcs['aon'].module is None:
    .clk_aon_i (ast_base_clks_i.clk_aon),
    % endif
  % endif
  % if feature_info["ast_is_internal"]:
    // Clocks and clock gating control from ${clkmgr['name']}
    .${clkmgr['name']}_clocks_o(${clkmgr['name']}_clocks),
    .${clkmgr['name']}_cg_en_o (${clkmgr['name']}_cg_en),
  % endif
% else:
    // Clocks and clock gating control from ${clkmgr['name']}
    .${clkmgr['name']}_clocks_i(${clkmgr['name']}_clocks${"_o" if not feature_info["ast_is_internal"] else ""}),
    .${clkmgr['name']}_cg_en_i (${clkmgr['name']}_cg_en${"_o" if not feature_info["ast_is_internal"] else ""}),
% endif

% if len(top['unmanaged_clocks']._asdict().values()) > 0:
    // Unmanaged external clocks
% for clk in top['unmanaged_clocks']._asdict().values():
    .${clk.signal_name},
    .${clk.cg_en_signal},
% endfor

% endif\

% if domain_rstmgr == domain:
  % if feature_info["ast_is_internal"]:
    // Resets and reset assert info from ${rstmgr['name']}
    .${rstmgr['name']}_resets_o(${rstmgr['name']}_resets${"_o" if not feature_info["ast_is_internal"] else ""}),
    .${rstmgr['name']}_rst_en_o(${rstmgr['name']}_rst_en${"_o" if not feature_info["ast_is_internal"] else ""}),
  % endif
% else:
    // Resets and reset assert info from ${rstmgr['name']}
    .${rstmgr['name']}_resets_i(${rstmgr['name']}_resets${"_o" if not feature_info["ast_is_internal"] else ""}),
    .${rstmgr['name']}_rst_en_i(${rstmgr['name']}_rst_en${"_o" if not feature_info["ast_is_internal"] else ""}),

% endif\

% if not feature_info["ast_is_internal"]:
    // Manual DFT signals
    .scan_rst_ni,
  % if feature_info["has_scan_en"][domain]:
    .scan_en_i,
  % endif
    .scanmode_i,
% else:
  % if not feature_info["dft_source_in_domain"][domain]:
    // Manual DFT signals
    .scan_rst_ni(scan_rst_n_o),
    % if feature_info["has_scan_en"][domain]:
    .scan_en_i  (scan_en_o),
    % endif
    .scanmode_i (scanmode_o),
  % endif
% endif

% if feature_info["has_pinmux"]:
% if lib.find_module(top["module"], "pinmux").get("domain") == domain:
% if cio_info["num_mio_pads"] != 0:
    // Multiplexed I/O
    .mio_in_i,
    .mio_out_o,
    .mio_oe_o,

% endif
% if cio_info["num_dio_total"] != 0:
    // Dedicated I/O
    .dio_in_i,
    .dio_out_o,
    .dio_oe_o,

% endif
    // Pad attributes
    .mio_attr_o,
    .dio_attr_o,

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

% for alert_group in top["outgoing_alert"].keys():
<% signals = alert_handler_signals(alert_group) %>\
<% pd_len = top["alert_handler_info"][alert_group]["count_pd"][domain] - 1 %>\
% if pd_len >= 0:
<% chiplevel_sigs = (f"{signals[0]}_pd_{domain.lower()}", f"{signals[1]}_pd_{domain.lower()}") %>\
    // Outgoing alerts for group ${alert_group}
    .outgoing_alert_${alert_group}_tx_o(${chiplevel_sigs[0]}),
    .outgoing_alert_${alert_group}_rx_i(${chiplevel_sigs[1]}),
% endif
% if lib.find_module(top["module"], "clkmgr", domain=domain):
    .outgoing_lpg_cg_en_${alert_group}_o(outgoing_lpg_cg_en_${alert_group}),
% endif
% if lib.find_module(top["module"], "rstmgr", domain=domain):
    .outgoing_lpg_rst_en_${alert_group}_o(outgoing_lpg_rst_en_${alert_group}),
% endif
% endfor
