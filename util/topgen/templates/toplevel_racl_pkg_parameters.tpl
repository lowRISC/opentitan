## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%page args="register_mapping, window_mapping, range_mapping, policy_names, racl_group, ip_block, module_name, if_name"/>\
<% import textwrap %>\
<% import math %>\
<% policy_idx_len = math.ceil(math.log10(max(1,len(policy_names)+1))) %>\
<% reg_idx_len = math.ceil(math.log10(max(1,len(register_mapping)+1))) %>\
<% group_suffix = f"_{racl_group.upper()}" if racl_group and racl_group != "Null" else "" %>\
<% if_suffix = f"_{if_name.upper()}" if if_name else "" %>\
<% reg_name_len = max( (len(name) for name in register_mapping.keys()), default=0 ) %>\
<% window_name_len = max( (len(name) for name in window_mapping.keys()), default=0 ) %>\
<% policy_sel_name = f"{module_name.upper()}{group_suffix}{if_suffix}" %>\
<% fmt_sel = "RACL_POLICY_SEL{group_suffix}_{policy}" %>\
<% policy_sel_len = max( (len(fmt_sel.format(group_suffix=group_suffix, policy=name)) for name in policy_names), default=0 ) %>\
<% has_ranges = if_name and ip_block.bus_interfaces.racl_range_support.get(if_name) and len(range_mapping) > 0 %>\
<% verbose = False %>\
  /**
   * Policy selection vector for ${module_name}
   *   TLUL interface name: ${if_name}
   *   RACL group: ${racl_group}
% if len(register_mapping) > 0 and verbose:
   *   Register to policy mapping:
  % for reg_name, policy_idx in register_mapping.items():
   *     ${f"{loop.index}".rjust(reg_idx_len)} ${f"{reg_name}:".ljust(reg_name_len+1)} ${policy_names[policy_idx]} \
(Idx ${f"{policy_idx}".rjust(policy_idx_len)})
  % endfor
% endif
% if len(window_mapping) > 0 and verbose:
   *   Window to policy mapping:
  % for window_name, policy_idx in window_mapping.items():
   *     ${f"{window_name}:".ljust(window_name_len+1)} ${policy_names[policy_idx]} \
(Idx ${f"{policy_idx}".rjust(policy_idx_len)})
  % endfor
% endif
% if has_ranges and verbose:
   *   Range to policy mapping:
  % for range in range_mapping:
   *     ${f"0x{range['base']:08x}"} -- ${f"0x{(range['base']+range['size']):08x}"} \
policy: ${policy_names[range['policy']]} (Idx ${f"{range['policy']}".rjust(policy_idx_len)})
  % endfor
% endif
   */
% if len(register_mapping) > 0:
  parameter racl_policy_sel_t RACL_POLICY_SEL_VEC_${policy_sel_name} [${len(register_mapping)}] = '{
% for reg_name, policy_idx in register_mapping.items():
<%
    value = fmt_sel.format(group_suffix=group_suffix, policy=policy_names[policy_idx].upper())
    value += ' ' if loop.last else ','
    value = value.ljust(policy_sel_len + 1)
    comment = " // " + f"{loop.index}".rjust(reg_idx_len) \
            + " " + f"{reg_name}".ljust(reg_name_len) \
            + " : Policy Idx " + f"{policy_idx}".rjust(policy_idx_len)
%>\
    ${value}${comment}
% endfor
  };
% endif
% for window_name, policy_idx in window_mapping.items():
<%
    value = fmt_sel.format(group_suffix=group_suffix, policy=policy_names[policy_idx].upper()) + ";"
    value = value.ljust(policy_sel_len + 1)
    comment = " // Policy Idx " + f"{policy_idx}".rjust(policy_idx_len)
%>\
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_${policy_sel_name}_${window_name.upper()} =
    ${value}${comment}
% endfor
% if has_ranges:
  parameter racl_policy_sel_t RACL_POLICY_SEL_NUM_RANGES_${policy_sel_name} = ${len(range_mapping)};
<%
  fmt_range = """'{{
      base:       'h{base:08x},
      limit:      'h{limit:08x},
      policy_sel: {policy} // Policy Idx {policy_idx}
      enable:     1'b1
    }}"""
%>\
  parameter racl_range_t [${len(range_mapping)-1}:0] RACL_POLICY_SEL_RANGES_${policy_sel_name} = '{
% for range in range_mapping:
<%
    policy = fmt_sel.format(group_suffix=group_suffix, policy=policy_names[range['policy']].upper())
    value = fmt_range.format(base = range['base'],
                             limit = range['limit'],
                             policy = f"{policy},".ljust(policy_sel_len + 1),
                             policy_idx = range['policy'])
    value += '' if loop.last else ','
%>\
    ${value}
% endfor
  };
% endif
