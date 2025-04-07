## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%page args="module, top, block"/>\
% for if_name in (x.get('name') for x in block.bus_interfaces.as_dicts()):
%   if if_name and block.bus_interfaces.racl_range_support.get(if_name):
<%
      mappings        = module.get('racl_mappings', {}).get(if_name, {})
      range_mapping   = mappings.get('range_mapping', [])
      racl_group      = mappings.get('racl_group')
      group_suffix    = f"_{racl_group.upper()}" if racl_group and racl_group != "Null" else ""
      if_suffix       = f"_{if_name.upper()}" if if_name else ""
      policy_sel_name = f"{module['name'].upper()}{group_suffix}{if_suffix}"
%>\
%     if len(range_mapping) > 0:
      .racl_policy_sel_ranges_${if_name}_i(RACL_POLICY_SEL_RANGES_${policy_sel_name}),
%     else:
      .racl_policy_sel_ranges_${if_name}_i('{top_racl_pkg::RACL_RANGE_T_DEFAULT}),
%     endif
%   endif
% endfor
