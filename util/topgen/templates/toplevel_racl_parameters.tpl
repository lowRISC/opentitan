## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%page args="module, top, block"/>\
% if module.get('racl_mappings'):
    .EnableRacl(1'b1),
    .RaclErrorRsp(top_racl_pkg::ErrorRsp),
  % for if_name, mappings in module['racl_mappings'].items():
<%
      register_mapping = mappings.get('register_mapping', {})
      window_mapping   = mappings.get('window_mapping', {})
      range_mapping    = mappings.get('range_mapping', [])
      racl_group       = mappings.get('racl_group')
      group_suffix = f"_{racl_group.upper()}" if racl_group and racl_group != "Null" else ""
      if_suffix = f"_{if_name.upper()}" if if_name else ""
      if_suffix2 = f"{if_name.title()}" if if_name else ""
      policy_sel_name = f"{module['name'].upper()}{group_suffix}{if_suffix}"
%>\
    % if len(register_mapping) > 0:
    .RaclPolicySelVec${if_suffix2}(RACL_POLICY_SEL_VEC_${policy_sel_name}),
    % endif
    % for window_name, policy_idx in window_mapping.items():
    .RaclPolicySelWin${if_suffix2}${window_name.replace("_","").title()}(RACL_POLICY_SEL_WIN_${policy_sel_name}_${window_name.upper()}),
    % endfor
    % if len(range_mapping) > 0 and block.bus_interfaces.racl_range_support.get(if_name):
    .RaclPolicySelNumRanges${if_suffix2}(RACL_POLICY_SEL_NUM_RANGES_${policy_sel_name}),
    % endif
  % endfor
% endif
% if module.get('template_type') == 'racl_ctrl':
    .RaclErrorRsp(${"1'b1" if top['racl']['error_response'] else "1'b0"}),
% endif
