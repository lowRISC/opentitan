// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gencmd}
<%
import re
import topgen.lib as lib
from reggen.params import Parameter

feature_info = {}
cio_info = {}

%>\
<%include file="/toplevel_snippets/info_dicts.tpl" args="top=top, feature_info=feature_info, cio_info=cio_info" />\

// This wrapper hosts all power domain wrappers and the connections between them for ${top["name"]}.
module top_${top["name"]} #(
<%include file="/toplevel_snippets/header_parameters.tpl" args="top=top, domain='', feedthrough=False" />\
) (
<%include file="/chiplevel_snippets/port_special_signals.tpl" args="top=top, feature_info=feature_info, cio_info=cio_info" />\
<%include file="/toplevel_snippets/port_intermodule_signals.tpl" args="top=top, domain='', last_snippet=True" />\
);

  import top_${top["name"]}_pkg::*;
  import prim_pad_wrapper_pkg::*;

  // Inter-Power Domain signals
% for sig in top["inter_pd"]["definitions"]:
  % if isinstance(sig["width"], Parameter):
  ${lib.im_defname(sig)} [${sig["width"].name_top}-1:0] ${sig["signame"]};
  % else:
  ${lib.im_defname(sig)} ${lib.bitarray(sig["width"],1)} ${sig["signame"]};
  % endif
% endfor

% if top["name"] == "englishbreakfast":
  // Outgoing alerts are currently unused
  assign alertenglishbreakfast_rx_pd_main = '{default: prim_alert_pkg::ALERT_RX_DEFAULT};
  assign alertenglishbreakfast_rx_pd_aon  = '{default: prim_alert_pkg::ALERT_RX_DEFAULT};

  logic unused_alertenglishbreakfast_tx;
  assign unused_alertenglishbreakfast_tx = ^{
    alertenglishbreakfast_tx_pd_main,
    alertenglishbreakfast_tx_pd_aon
  };

  logic unused_outgoing_lpg_englishbreakfast;
  assign unused_outgoing_lpg_englishbreakfast = ^{
    outgoing_lpg_cg_en_englishbreakfast,
    outgoing_lpg_rst_en_englishbreakfast
  };
% endif

% for pd in reversed(top["power"]["domains"]):
<%
  comment = "// Top-level {} Domain //".format(pd)
  border = "/" * len(comment)
%>\
  ${border}
  ${comment}
  ${border}
  ${top["name"]}_pd_${pd.lower()} #(
<%include file="/toplevel_snippets/header_parameters.tpl" args="top=top, domain=pd, feedthrough=True" />\
  ) ${top["name"]}_pd_${pd.lower()} (
<%include file="/toplevel_snippets/special_signals_portmap.tpl" args="top=top, feature_info=feature_info, cio_info=cio_info, domain=pd" />\

<%include file="/chiplevel_snippets/intermodule_portmap.tpl" args="top=top, target='', domain=pd, inter_pd=True, feedthrough=False, last_snippet=False" />\

<%include file="/chiplevel_snippets/intermodule_portmap.tpl" args="top=top, target='', domain=pd, inter_pd=False, feedthrough=True, last_snippet=True" />\
  );

% endfor
endmodule
