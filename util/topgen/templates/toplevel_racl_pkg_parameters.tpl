## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%page args="register_mapping, window_mapping, range_mapping, policy_names, racl_group, module_name, if_name"/>\
<% import textwrap %>\
<% import math %>\
<% policy_idx_len = math.ceil(math.log10(max(1,len(policy_names)+1))) %>\
<% group_suffix = f"_{racl_group.upper()}" if racl_group and racl_group != "Null" else "" %>\
<% if_suffix = f"_{if_name.upper()}" if if_name else "" %>\
<% reg_name_len = max( (len(name) for name in register_mapping.keys()), default=0 ) %>\
<% window_name_len = max( (len(name) for name in window_mapping.keys()), default=0 ) %>\
<% policy_sel_name = f"RACL_POLICY_SEL_{module_name.upper()}{group_suffix}{if_suffix}" %>\
  /**
   * Policy selection vector for ${module_name}
   *   TLUL interface name: ${if_name}
   *   RACL group: ${racl_group}
% if len(register_mapping) > 0:
   *   Register to policy mapping:
  % for reg_name, policy_idx in register_mapping.items():
   *     ${f"{reg_name}:".ljust(reg_name_len+1)} ${policy_names[policy_idx]} \
(Idx ${f"{policy_idx}".rjust(policy_idx_len)})
  % endfor
% endif
% if len(window_mapping) > 0:
   *   Window to policy mapping:
  % for window_name, policy_idx in window_mapping.items():
   *     ${f"{window_name}:".ljust(window_name_len+1)} ${policy_names[policy_idx]} \
(Idx ${f"{policy_idx}".rjust(policy_idx_len)})
  % endfor
% endif
% if len(range_mapping) > 0:
   *   Range to policy mapping:
  % for range in range_mapping:
   *     ${f"0x{range['base']:08x}"} -- ${f"0x{(range['base']+range['size']):08x}"} \
policy: ${policy_names[range['policy']]} (Idx ${f"{range['policy']}".rjust(policy_idx_len)})
  % endfor
% endif
   */
% if len(register_mapping) > 0:
<% policy_sel_value = ", ".join(map(str, reversed(register_mapping.values())))%>\
<% policy_sel_value = "\n    ".join(textwrap.wrap(policy_sel_value, 94))%>\
  parameter racl_policy_sel_t ${policy_sel_name} [${len(register_mapping)}] = '{
    ${policy_sel_value}
  };
% endif
% for window_name, policy_idx in window_mapping.items():
  parameter racl_policy_sel_t ${policy_sel_name}_WIN_${window_name.upper()} = ${policy_idx};
% endfor
% if len(range_mapping) > 0:
  parameter racl_policy_sel_t ${policy_sel_name}_NUM_RANGES = ${len(range_mapping)};
<% fmt_range = "'{{base:'h{base:x},mask:'h{mask:x},policy:{policy}}}" %>\
<% value =  ",\n".join(map(fmt_range.format_map, range_mapping)) %>\
  parameter racl_range_t ${policy_sel_name}_RANGES [${len(range_mapping)}] = '{
    ${value}
  };
% endif
