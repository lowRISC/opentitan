## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import re%>\
<%import topgen.lib as lib%>\
<%page args="top, target, domain, inter_pd, feedthrough, last_snippet"/>\
<%
port_list = lib.get_intermodule_ports(top, domain, inter_pd)
max_portwidth = max(len(x["signame"]) for x in port_list) if port_list else 0
if target == '':
  target = top["targets"][0]
if port_list:
  filtered_port_list = [p for p in port_list if len(p["signame_chip"][target["name"]]) <= 25]
  max_sigwidth = max(len(p["signame_chip"][target["name"]]) for p in filtered_port_list)
else:
  max_sigwidth = 0
if inter_pd:
  comment = "// Ports to and from other power domains (auto-generated)"
else:
  comment = "// Regular ports (auto-generated)"
%>\
    ${comment}
    % for sig in port_list:
    % if feedthrough:
    .${sig["signame"]}${"" if loop.last and last_snippet else ","}
    % else:
    .${lib.ljust(sig["signame"], max_portwidth)}(${lib.ljust(sig["signame_chip"][target["name"]], max_sigwidth)})${"" if loop.last and last_snippet else ","}
    % endif
    % endfor
