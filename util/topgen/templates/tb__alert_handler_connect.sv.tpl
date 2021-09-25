// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
${autogen_banner}
<%
  index = 0
  module_name = ""
%>\
% for alert in top["alert"]:
  % if alert["module_name"] == module_name:
<% index = index + 1 %>\
  % else:
<%
  module_name = alert["module_name"]
  index = 0
%>\
  % endif
assign alert_if[${loop.index}].alert_tx = `CHIP_HIER.u_${module_name}.alert_tx_o[${index}];
% endfor
