## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%from topgen.merge import is_unmanaged_reset%>\
<%page args="top"/>\
  // TL-UL Crossbars
% for xbar in top["xbar"]:
<%
  name_len = max([len(x["name"]) for x in xbar["nodes"]]);
%>\
  xbar_${xbar["name"]} u_xbar_${xbar["name"]} (
  % for k, v in xbar["clock_connections"].items():
    .${k} (${v}),
  % endfor
  % for port, reset in xbar["reset_connections"].items():
    .${port} (${lib.get_reset_path(top, reset, False, is_unmanaged_reset(top, reset['name']))}),
  % endfor

  ## Inter-module signal
  % for sig in xbar["inter_signal_list"]:
<% assert sig['type'] == "req_rsp" %>\
    // port: ${sig['name']}
    .${lib.im_portname(sig,"req")}(${lib.im_netname(sig, "req")}),
    .${lib.im_portname(sig,"rsp")}(${lib.im_netname(sig, "rsp")}),

  % endfor\

    .scanmode_i
  );

% endfor
