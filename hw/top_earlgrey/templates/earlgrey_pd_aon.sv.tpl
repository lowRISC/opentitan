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
  // TODO Manual parameters for pwrmgr
  parameter int AlertHandlerEscNumSeverities = 4,
  parameter int AlertHandlerEscPingCountWidth = 16,
<%include file="/toplevel_snippets/header_parameters.tpl" args="top=top, domain=domain" />\
) (
<%include file="/toplevel_snippets/port_intermodule_signals.tpl" args="top=top, domain=domain" />\
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

<%include file="/toplevel_snippets/module_instantiations.tpl" args="top=top, domain=domain" />\

<%include file="/toplevel_snippets/interrupt_assigns.tpl" args="top=top, domain=domain" />\

<%include file="/toplevel_snippets/xbar_instantiations.tpl" args="top=top, domain=domain" />\

<%include file="/toplevel_snippets/cio_assigns.tpl" args="top=top, feature_info=feature_info, cio_info=cio_info, domain=domain" />\

  // Make sure scanmode_i is never X (including during reset)
  `ASSERT_KNOWN(scanmodeKnown, scanmode_i, clk_main_i, 0)

endmodule
