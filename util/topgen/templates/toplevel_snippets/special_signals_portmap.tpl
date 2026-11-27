## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%from topgen.merge import alert_handler_signals%>\
<%page args="top, feature_info, cio_info, domain"/>\
<%
  clkmgr = lib.find_module(top['module'], 'clkmgr')
  rstmgr = lib.find_module(top['module'], 'rstmgr')
  ## Clocks sourced from another IP module's own generated clock (e.g. AST
  ## feeding clkmgr) are wired as internal nets/inter-module ports instead -
  ## see intermodule.resolve_module_clocks().
  clk_srcs = top['clocks'].srcs
  clkmgr_parts = lib.get_clkmgr_partitions(top)
  rstmgr_parts = lib.get_rstmgr_partitions(top)
  ## The struct ports of the partitions of the clkmgr and rstmgr in this domain.
  struct_ports = lib.get_manager_struct_ports(top, domain, feature_info["ast_is_internal"])
  ## Each raw clock from outside the top connects to the clkmgr partition that receives it.
  ext_conns = {part: [] for part, _, _, _ in clkmgr_parts}
  for src_name, conn in (('main', '.clk_main_i(ast_base_clks_i.clk_sys),'),
                         ('io', '.clk_io_i  (ast_base_clks_i.clk_io ),'),
                         ('usb', '.clk_usb_i (ast_base_clks_i.clk_usb),'),
                         ('aon', '.clk_aon_i (ast_base_clks_i.clk_aon),')):
    if src_name == 'usb' and not feature_info["has_usb"]:
      continue
    if clk_srcs[src_name].module is None:
      part = lib.get_clkmgr_clock_partition(top, clk_srcs[src_name])
      ext_conns[part].append(conn)
%>\
## Connect the ports of each clkmgr partition, as port_special_signals.tpl declares them.
% for part, dom, sfx, tinfix in clkmgr_parts:
<%
  who = f"the {part} partition of the {clkmgr['name']}"
  structs = [p for p in struct_ports if p.ip_type == 'clkmgr' and p.partition == part]
%>\
  % if dom == domain and ext_conns[part]:
    // All externally supplied clocks of the ${part} partition of the clkmgr
    % for conn in ext_conns[part]:
    ${conn}
    % endfor
  % endif
  % if structs:
    // Clocks and clock gating control from ${who}
    % for p in structs:
    .${p.port}(${p.net}),
    % endfor
  % endif
% endfor

% if len(top['unmanaged_clocks']._asdict().values()) > 0:
    // Unmanaged external clocks
% for clk in top['unmanaged_clocks']._asdict().values():
    .${clk.signal_name},
    .${clk.cg_en_signal},
% endfor

% endif\

## Connect the struct ports of each rstmgr partition, as port_special_signals.tpl declares them.
% for part, dom, sfx, _ in rstmgr_parts:
<%
  who = f"the {part} partition of the {rstmgr['name']}"
  structs = [p for p in struct_ports if p.ip_type == 'rstmgr' and p.partition == part]
%>\
  % if structs:
    // Resets and reset asserted information from ${who}
    % for p in structs:
    .${p.port}(${p.net}),
    % endfor
  % endif
% endfor
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
