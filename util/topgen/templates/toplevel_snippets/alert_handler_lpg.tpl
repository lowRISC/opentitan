## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%from topgen.clocks import Clocks%>\
<%from topgen.resets import Resets%>\
<%page args="top, feature_info"/>\
  // Wire up alert handler LPGs
  prim_mubi_pkg::mubi4_t [alert_handler_pkg::NLpg-1:0] lpg_cg_en;
  prim_mubi_pkg::mubi4_t [alert_handler_pkg::NLpg-1:0] lpg_rst_en;

<%
# get all known typed clocks and add them to a dict
# this is used to generate the tie-off assignments further below
clocks = top['clocks']
assert isinstance(clocks, Clocks)
typed_clocks = clocks.typed_clocks()
known_clocks = {}
for clk in typed_clocks.all_clocks():
  known_clocks.update({lib.get_clock_lpg_path(top, clk): 1})

# get all known resets and add them to a dict
# this is used to generate the tie-off assignments further below
resets = top['resets']
assert isinstance(resets, Resets)
output_rsts = resets.get_top_resets()
known_resets = {}
for rst in output_rsts:
  for dom in top['power']['domains']:
    if rst.shadowed:
      path = lib.get_reset_lpg_path(top, resets.get_reset_by_name(rst.name)._asdict(), True, dom)
      known_resets.update({
        path: 1
      })
    path = lib.get_reset_lpg_path(top, resets.get_reset_by_name(rst.name)._asdict(), False, dom)
    known_resets.update({
      path: 1
    })
%>\

<% k = 0 %>\
% for lpg in top['alert_lpgs']:
  // ${lpg['name']}
<%
  cg_en = lib.get_clock_lpg_path(top, lpg['clock_connection'], lpg['unmanaged_clock'])
  rst_en = lib.get_reset_lpg_path(top, lpg['reset_connection'], False, None, lpg['unmanaged_reset'])
  known_clocks[cg_en] = 0
  known_resets[rst_en] = 0
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

% for alert_group, lpgs in top['outgoing_alert_lpgs'].items():
  // Outgoing LPGs for alert group ${alert_group}
  % for k, lpg in enumerate(lpgs):
  // ${lpg['name']}
<%
    cg_en = lib.get_clock_lpg_path(top, lpg['clock_connection'], lpg['unmanaged_clock'])
    rst_en = lib.get_reset_lpg_path(top, lpg['reset_connection'], False, None, lpg['unmanaged_reset'])
    known_clocks[cg_en] = 0
    known_resets[rst_en] = 0
%>\
  assign outgoing_lpg_cg_en_${alert_group}_o[${k}] = ${cg_en};
  assign outgoing_lpg_rst_en_${alert_group}_o[${k}] = ${rst_en};
  % endfor
% endfor

// tie-off unused connections
//VCS coverage off
// pragma coverage off
<% k = 0 %>\
% for clk, unused in known_clocks.items():
  % if unused:
  prim_mubi_pkg::mubi4_t unused_cg_en_${k};
  assign unused_cg_en_${k} = ${clk};<% k += 1 %>
  % endif
% endfor
<% k = 0 %>\
% for rst, unused in known_resets.items():
  % if unused:
  prim_mubi_pkg::mubi4_t unused_rst_en_${k};
  assign unused_rst_en_${k} = ${rst};<% k += 1 %>
  % endif
% endfor
//VCS coverage on
// pragma coverage on
