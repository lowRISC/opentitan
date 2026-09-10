## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%from reggen.params import Parameter%>\
<%from topgen.merge import alert_handler_signals%>\
<%page args="top, feature_info, domain"/>\
% if feature_info["has_alert_handler"]:
<% alert_handlers = [handler["type"] for handler in lib.find_modules(lib.get_all_modules(top, domain=domain), "alert_handler")]%>\
  // Alert list
% for handler in alert_handlers:
<% alert_tx, alert_rx = alert_handler_signals(handler) %>\
  prim_alert_pkg::alert_tx_t [${handler}_pkg::NAlerts-1:0] ${alert_tx};
  prim_alert_pkg::alert_rx_t [${handler}_pkg::NAlerts-1:0] ${alert_rx};
% endfor

% if not top["alert"]:
%    for handler in alert_handlers:
<%     alert_tx, _ = alert_handler_signals(handler) %>
  for (genvar k = 0; k < ${handler}_pkg::NAlerts; k++) begin : gen_alert_tie_off
    // tie off if no alerts present in the system
    assign ${alert_tx}[k].alert_p = 1'b0;
    assign ${alert_tx}[k].alert_n = 1'b1;
  end
%    endfor
% endif\

% for handler in alert_handlers:
<% alert_tx, alert_rx = alert_handler_signals(handler) %>\
  % if top["alert_handler_info"][handler]["connect_pd"]:
  // External connections for ${handler}
  % for idx, map in top["alert_handler_info"][handler]["connect_pd"].items():
  assign ${alert_tx}[${idx}] = ${alert_tx}_pd_${map["src_pd"].lower()}_i[${map["idx"]}];
  % endfor
  % for idx, map in top["alert_handler_info"][handler]["connect_pd"].items():
  assign ${alert_rx}_pd_${map["src_pd"].lower()}_o[${map["idx"]}] = ${alert_rx}[${idx}];
  % endfor
  % endif
% endfor\

% for alert_group, alerts in top['incoming_alert'].items():
<% alert_info = top["alert_connections"]["incoming_" + alert_group] %>\
% if not alert_info:
<% continue %>\
% endif
  // Alert mapping to the alert handler for alert group ${alert_group}
  % for comment in alert_info["comments"]:
  // ${comment}
  % endfor
  assign ${alert_info["tx_expr"]} = incoming_alert_${alert_group}_tx_i;
  assign incoming_alert_${alert_group}_rx_o = ${alert_info["rx_expr"]};
% endfor
% endif\
