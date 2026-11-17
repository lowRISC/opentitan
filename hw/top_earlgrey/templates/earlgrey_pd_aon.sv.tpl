// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gencmd}
<%
import topgen.lib as lib

domain = "Aon"

feature_info = {}
cio_info = {}
%>\
<%include file="/toplevel_snippets/info_dicts.tpl" args="top=top, feature_info=feature_info, cio_info=cio_info" />\
`include "prim_assert.sv"

module ${top["name"]}_pd_${domain.lower()} #(
% if top["name"] != "englishbreakfast":
  // TODO Manual parameters for pwrmgr
  parameter int AlertHandlerEscNumSeverities = 4,
  parameter int AlertHandlerEscPingCountWidth = 16,
% endif
<%include file="/toplevel_snippets/header_parameters.tpl" args="top=top, domain=domain, feedthrough=False" />\
) (
<%include file="/toplevel_snippets/port_intermodule_signals.tpl" args="top=top, domain=domain, last_snippet=False" />\
<%include file="/toplevel_snippets/port_special_signals.tpl" args="top=top, feature_info=feature_info, cio_info=cio_info, domain=domain" />\
);

  import top_${top["name"]}_pkg::*;
  // Compile-time random constants
  import top_${top["name"]}_rnd_cnst_pkg::*;

<%include file="/toplevel_snippets/localparams.tpl" args="top=top, domain=domain" />\

<%include file="/toplevel_snippets/cio_signals.tpl" args="top=top, feature_info=feature_info, cio_info=cio_info, domain=domain" />\

<%include file="/toplevel_snippets/interrupt_signals.tpl" args="top=top, name_to_block=name_to_block, domain=domain" />\

<%include file="/toplevel_snippets/alert_handler_signals.tpl" args="top=top, feature_info=feature_info, domain=domain" />\

<%include file="/toplevel_snippets/intermodule_signals.tpl" args="top=top, domain=domain" />\

<%include file="/toplevel_snippets/clk_reset_lpg_assigns.tpl" args="top=top, feature_info=feature_info, domain=domain" />\

<%include file="/toplevel_snippets/module_instantiations.tpl" args="top=top, feature_info=feature_info, domain=domain" />\

<%include file="/toplevel_snippets/interrupt_assigns.tpl" args="top=top, domain=domain" />\

<%include file="/toplevel_snippets/xbar_instantiations.tpl" args="top=top, domain=domain" />\

<%include file="/toplevel_snippets/cio_assigns.tpl" args="top=top, feature_info=feature_info, cio_info=cio_info, domain=domain" />\

<%
  clkmgr = lib.find_module(top['module'], 'clkmgr')
  rstmgr = lib.find_module(top['module'], 'rstmgr')
  domain_clkmgr = clkmgr.get('domain')
  domain_rstmgr = rstmgr.get('domain')
  has_clkmgr = domain_clkmgr == domain
  has_rstmgr = domain_rstmgr == domain
  clkmgr_domains = {part: dom for part, dom, _, _ in lib.get_clkmgr_partitions(top)}
  rstmgr_domains = {part: dom for part, dom, _, _ in lib.get_rstmgr_partitions(top)}
%>\
% for part, dom, sfx, _ in lib.get_clkmgr_partitions(top):
<%
  out_clk = lib.clkmgr_struct_crosses(top, 'clocks', part)
  out_cg = lib.clkmgr_struct_crosses(top, 'cg_en', part)
%>\
  % if dom == domain and (out_clk or out_cg):
  // Connect the ${part} partition of the clkmgr to the top-level signals of the power domains that
  // need them.
    % if out_clk:
  assign ${clkmgr['name']}_clocks${sfx}_o = ${clkmgr['name']}_clocks${sfx};
    % endif
    % if out_cg:
  assign ${clkmgr['name']}_cg_en${sfx}_o  = ${clkmgr['name']}_cg_en${sfx};
    % endif
  % endif
% endfor

% for part, dom, sfx, _ in lib.get_rstmgr_partitions(top):
<%
  out_rst = lib.rstmgr_struct_crosses(top, 'resets', part)
  out_en = lib.rstmgr_struct_crosses(top, 'rst_en', part)
%>\
  % if dom == domain and (out_rst or out_en):
  // Connect the ${part} partition of the rstmgr to the top-level signals of the power domains that
  // need them.
    % if out_rst:
  assign ${rstmgr['name']}_resets${sfx}_o = ${rstmgr['name']}_resets${sfx};
    % endif
    % if out_en:
  assign ${rstmgr['name']}_rst_en${sfx}_o = ${rstmgr['name']}_rst_en${sfx};
    % endif
  % endif
% endfor

% if feature_info["ast_is_internal"]:
  // Connect the sense inputs of the AST to the clocks and resets of the secondary partitions of the
  // clkmgr and the rstmgr.
  assign ast_sns_clks = clkmgr_clocks_secondary${"" if clkmgr_domains[lib.PART_SECONDARY] == domain else "_i"};
  assign ast_sns_rsts = rstmgr_resets_secondary${"" if rstmgr_domains[lib.PART_SECONDARY] == domain else "_i"};

  // Tie-off unused clock gate signal
  logic unused_cg_en_ast_ext;
  assign unused_cg_en_ast_ext = ^cg_en_ast_ext_i;
% endif

<%
  # (struct field, flat inter-signal base name)
  # for every memory-cfg consumer of this PD.
  mem_cfg_consumers = [
    ('sram_ctrl_ret', 'sram_ctrl_ret_ram_cfg'),
  ]
%>\
<%include file="/toplevel_snippets/mem_cfg_wiring.tpl" args="mem_cfg_consumers=mem_cfg_consumers" />\

% if lib.find_module(top["module"], "pinmux", domain=domain):
<%include file="/toplevel_snippets/pinmux_jtag_breakout.tpl"/>\
% endif

  // Make sure scanmode is never X (including during reset)
% if feature_info["dft_source_in_domain"][domain]:
  `ASSERT_KNOWN(scanmodeKnown, scanmode_o, ast_clk_src_aon, 0)
% else:
  `ASSERT_KNOWN(scanmodeKnown, scanmode_i, ast_clk_src_aon, 0)
% endif

endmodule
