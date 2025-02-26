## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%page args="m, top"/>\
% if m.get('racl_mappings'):
    .EnableRacl(1'b1),
    .RaclErrorRsp(top_racl_pkg::ErrorRsp),
  % for if_name, mappings in m['racl_mappings'].items():
<%
      register_mapping = mappings.get('register_mapping', {})
      window_mapping   = mappings.get('window_mapping', {})
      range_mapping    = mappings.get('range_mapping', [])
      racl_group       = mappings.get('racl_group')
      group_suffix = f"_{racl_group.upper()}" if racl_group and racl_group != "Null" else ""
      if_suffix = f"_{if_name.upper()}" if if_name else ""
      if_suffix2 = f"{if_name.title()}" if if_name else ""
      policy_sel_name = f"RACL_POLICY_SEL_{m['name'].upper()}{group_suffix}{if_suffix}"
%>\
    % if len(register_mapping) > 0:
    .RaclPolicySelVec${if_suffix2}(${policy_sel_name}),
    % endif
    % for window_name, policy_idx in window_mapping.items():
    .RaclPolicySelWin${if_suffix2}${window_name.replace("_","").title()}(${policy_sel_name}_WIN_${window_name.upper()}),
    % endfor
    % if len(range_mapping) > 0:
    .RaclPolicySelRanges${if_suffix2}Num(${policy_sel_name}_NUM_RANGES),
    .RaclPolicySelRanges${if_suffix2}(${policy_sel_name}_RANGES),
    % endif
  % endfor
% endif
% if m.get('template_type') == 'racl_ctrl':
    .RaclErrorRsp(${"1'b1" if top['racl']['error_response'] else "1'b0"}),
% endif
