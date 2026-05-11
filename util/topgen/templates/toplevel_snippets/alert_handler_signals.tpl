## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%from reggen.params import Parameter%>\
<%from topgen.merge import alert_handler_signals%>\
<%page args="top, feature_info"/>\
% if feature_info["has_alert_handler"]:
<% alert_handlers = [handler["type"] for handler in lib.find_modules(top["module"], "alert_handler")]%>\
  // Alert list
% for handler in alert_handlers:
<% alert_tx, alert_rx = alert_handler_signals(handler) %>\
  prim_alert_pkg::alert_tx_t [${handler}_pkg::NAlerts-1:0]  ${alert_tx};
  prim_alert_pkg::alert_rx_t [${handler}_pkg::NAlerts-1:0]  ${alert_rx};
% endfor\

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
