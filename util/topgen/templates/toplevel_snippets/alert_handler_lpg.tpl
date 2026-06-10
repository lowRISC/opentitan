## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%from topgen.clocks import Clocks%>\
<%from topgen.resets import Resets%>\
<%page args="top, feature_info, domain"/>\
<%
domain_has_clkmgr = lib.find_module(top["module"], "clkmgr", domain=domain) is not None
domain_has_rstmgr = lib.find_module(top["module"], "rstmgr", domain=domain) is not None
# get all known typed clocks and add them to a dict
# this is used to generate the tie-off assignments further below
clocks = top['clocks']
assert isinstance(clocks, Clocks)
typed_clocks = clocks.typed_clocks()
unused_cg_en = {lib.get_clock_lpg_path(top, clk, domain) for clk in typed_clocks.all_clocks()}

# get all known resets and add them to a dict
# this is used to generate the tie-off assignments further below
resets = top['resets']
assert isinstance(resets, Resets)
output_rsts = resets.get_top_resets()
unused_rst_en = set()

for rst in output_rsts:
  for dom in top['power']['domains']:
    path = lib.get_reset_lpg_path(top, resets.get_reset_by_name(rst.name)._asdict(), domain, False, dom)
    unused_rst_en.add(path)
    if rst.shadowed:
      path = lib.get_reset_lpg_path(top, resets.get_reset_by_name(rst.name)._asdict(), domain, True, dom)
      unused_rst_en.add(path)
%>\
% if lib.find_module(top["module"], "alert_handler", domain=domain):
  // Alert handler low power groups (LPGs)
  prim_mubi_pkg::mubi4_t [alert_handler_pkg::NLpg-1:0] lpg_cg_en;
  prim_mubi_pkg::mubi4_t [alert_handler_pkg::NLpg-1:0] lpg_rst_en;

<% k = 0 %>\
% for lpg in top['alert_lpgs']:
  // ${lpg['name']}
<%
  cg_en = lib.get_clock_lpg_path(top, lpg['clock_connection'], domain, lpg['unmanaged_clock'])
  rst_en = lib.get_reset_lpg_path(top, lpg['reset_connection'], domain, False, None, lpg['unmanaged_reset'])
  unused_cg_en.discard(cg_en)
  unused_rst_en.discard(rst_en)
%>\
  assign lpg_cg_en[${k}] = ${cg_en};
  assign lpg_rst_en[${k}] = ${rst_en};
<% k += 1 %>\
% endfor
% for alert_group, alerts in top['incoming_alert'].items():
  % for unique_alert_lpg_entry in get_alerts_with_unique_lpg_idx(alerts):
  assign lpg_cg_en[${k}] = incoming_lpg_cg_en_${alert_group}_i[${unique_alert_lpg_entry["lpg_idx"]}];
  assign lpg_rst_en[${k}] = incoming_lpg_rst_en_${alert_group}_i[${unique_alert_lpg_entry["lpg_idx"]}];
<% k += 1 %>\
  % endfor
% endfor

// Tie off unused clock- and reset enables
//VCS coverage off
// pragma coverage off
  prim_mubi_pkg::mubi4_t [${len(unused_cg_en)-1}:0] unused_cg_en;
  prim_mubi_pkg::mubi4_t [${len(unused_rst_en)-1}:0] unused_rst_en;

% for i, clk in enumerate(sorted(unused_cg_en)):
  assign unused_cg_en[${i}] = ${clk};
% endfor

% for i, rst in enumerate(sorted(unused_rst_en)):
  assign unused_rst_en[${i}] = ${rst};
% endfor
// pragma coverage on
//VCS coverage on

% endif\

% if domain_has_clkmgr or domain_has_rstmgr:
% for alert_group, lpgs in top['outgoing_alert_lpgs'].items():
  // Outgoing LPGs for alert group ${alert_group}
  % for k, lpg in enumerate(lpgs):
  // ${lpg['name']}
<%
    cg_en = lib.get_clock_lpg_path(top, lpg['clock_connection'], domain, lpg['unmanaged_clock'])
    rst_en = lib.get_reset_lpg_path(top, lpg['reset_connection'], domain, False, None, lpg['unmanaged_reset'])
%>\
% if domain_has_clkmgr:
  assign outgoing_lpg_cg_en_${alert_group}_o[${k}] = ${cg_en};
% endif
% if domain_has_rstmgr:
  assign outgoing_lpg_rst_en_${alert_group}_o[${k}] = ${rst_en};
% endif
  % endfor
% endfor
% endif
