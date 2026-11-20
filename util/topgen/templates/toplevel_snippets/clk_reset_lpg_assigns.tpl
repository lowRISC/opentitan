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
domain_has_alert_handler = lib.find_module(top["module"], "alert_handler", domain=domain) is not None
# Without an alert handler in this domain, nothing consumes the clock gating and reset
# enable indication signals. Tie them off if they enter this domain as inputs (in the
# clkmgr / rstmgr domains they are consumed by the output ports).
# The clkmgr and the rstmgr each have two partitions, which can be in different power domains.
# Signals from a partition in the other domain enter this domain as inputs, so they also need a
# tie-off.
clkmgr_partition_domains = [dom for _, dom, _, _ in lib.get_clkmgr_partitions(top)]
domain_has_foreign_clkmgr = any(dom != domain for dom in clkmgr_partition_domains)
tie_off_cg_en = domain_has_alert_handler or domain_has_foreign_clkmgr
rstmgr_partition_domains = [dom for _, dom, _, _ in lib.get_rstmgr_partitions(top)]
domain_has_foreign_rstmgr = any(dom != domain for dom in rstmgr_partition_domains)
tie_off_rst_en = domain_has_alert_handler or domain_has_foreign_rstmgr
# get all known typed clocks and add them to a dict
# this is used to generate the tie-off assignments further below
clocks = top['clocks']
assert isinstance(clocks, Clocks)
typed_clocks = clocks.typed_clocks()
clkmgr = lib.find_module(top["module"], "clkmgr")
# The primary partition outputs all the clock gating indications. They exist in this domain, and
# need a tie-off, if the primary partition is in this domain or its indications enter through an
# input port.
cg_en_here = (lib.get_domain_of_partition(clkmgr, lib.PART_PRIMARY) == domain or
              lib.clkmgr_struct_crosses(top, 'cg_en', lib.PART_PRIMARY, domain))
unused_cg_en = ({lib.get_clock_lpg_path(top, clk, domain) for clk in typed_clocks.all_clocks()}
                if cg_en_here else set())
# Collect the clock struct fields that arrive through an input port. A struct has a field for a
# clock only if its partition outputs that clock.
out_parts = lib.get_clkmgr_clock_out_partitions(top)
unused_clocks = set()
for part, dom, sfx, _ in lib.get_clkmgr_partitions(top):
  if dom != domain and lib.clkmgr_struct_crosses(top, 'clocks', part, domain):
    unused_clocks |= {f"{clkmgr['name']}_clocks{sfx}_i.{clk}" for clk in typed_clocks.all_clocks()
                      if part in out_parts.get(clk, [])}

# get all known resets and add them to a dict
# this is used to generate the tie-off assignments further below
resets = top['resets']
assert isinstance(resets, Resets)
output_rsts = resets.get_top_resets()
unused_rst_en = set()
unused_resets = set()

rstmgr = lib.find_module(top["module"], "rstmgr")
# The primary partition outputs all the reset asserted indications. They exist in this domain, and
# need a tie-off, if the primary partition is in this domain or its indications enter through an
# input port.
rst_en_here = (lib.get_domain_of_partition(rstmgr, lib.PART_PRIMARY) == domain or
               lib.rstmgr_struct_crosses(top, 'rst_en', lib.PART_PRIMARY, domain))
out_parts = lib.get_rstmgr_reset_out_partitions(top)
shadowed_out_parts = lib.get_rstmgr_shadowed_out_partitions(top)
for rst in output_rsts:
  for dom in rst.domains:
    shadows = (False, True) if rst.shadowed else (False,)
    if rst_en_here:
      for shadow in shadows:
        unused_rst_en.add(lib.get_reset_lpg_path(top, resets.get_reset_by_name(rst.name)._asdict(),
                                                 domain, shadow, dom))
    # Collect the reset struct fields that arrive through an input port.
    # The rstmgr outputs each reset only in the domains that use it.
    for part, pdom, sfx, _ in lib.get_rstmgr_partitions(top):
      if pdom != domain and lib.rstmgr_struct_crosses(top, 'resets', part, domain):
        prefixes = lib.get_reset_prefixes(top, domain, part)
        # The shadowed copy has its own partitions and shape, because it goes only where a module
        # uses it.
        for shadow in shadows:
          parts = (shadowed_out_parts if shadow else out_parts).get((rst.name, dom), [])
          if part in parts:
            index = lib.get_rstmgr_output_index(top, rst.name, dom, part, shadow)
            unused_resets.add(resets.get_path(rst.name, prefixes, index, shadow))

# Go over all modules of power domain at hand and remove all used resets and clocks from the
# respective unused_ set.
for m in lib.get_all_modules(top, domain=domain):
  if not lib.is_inst(m):
    continue
  # A split IP contributes the clocks / resets of every partition emitted in
  # this power domain.
  for partition in lib.get_module_partitions(m, domain):
    clock_connections = m.get(lib.partition_key("clock_connections", partition)) or {}
    for clock_sig in clock_connections.values():
      unused_clocks.discard(clock_sig)
    reset_connections = m.get(lib.partition_key("reset_connections", partition)) or {}
    for port, reset in reset_connections.items():
      unused_resets.discard(lib.get_reset_path(top, {'name': reset['name'], 'domain': reset['domain']}, domain))
      if lib.is_shadowed_port(name_to_block[m['type']], port):
        unused_resets.discard(lib.get_reset_path(top, {'name': reset['name'], 'domain': reset['domain']}, domain, True))
%>\
% if domain_has_alert_handler:
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

% endif
% if tie_off_cg_en or tie_off_rst_en:
// Tie off unused clock- and reset enables
//VCS coverage off
// pragma coverage off
% if tie_off_cg_en and unused_cg_en:
  prim_mubi_pkg::mubi4_t [${len(unused_cg_en)-1}:0] unused_cg_en;
% endif
% if tie_off_rst_en and unused_rst_en:
  prim_mubi_pkg::mubi4_t [${len(unused_rst_en)-1}:0] unused_rst_en;
% endif

% if tie_off_cg_en:
% for i, clk in enumerate(sorted(unused_cg_en)):
  assign unused_cg_en[${i}] = ${clk};
% endfor

% endif
% if tie_off_rst_en:
% for i, rst in enumerate(sorted(unused_rst_en)):
  assign unused_rst_en[${i}] = ${rst};
% endfor
// pragma coverage on
//VCS coverage on
% endif

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

% endif\

% if unused_clocks or unused_resets:
// Tie off unused clocks and resets
//VCS coverage off
// pragma coverage off
% if unused_clocks:
  logic [${len(unused_clocks)-1}:0] unused_clocks;
% for i, clk in enumerate(sorted(unused_clocks)):
  assign unused_clocks[${i}] = ${clk};
% endfor

% endif\

% if unused_resets:
  logic [${len(unused_resets)-1}:0] unused_resets;
% for i, rst_path in enumerate(sorted(unused_resets)):
  assign unused_resets[${i}] = ${rst_path};
% endfor
% endif
// pragma coverage on
//VCS coverage on
% endif
