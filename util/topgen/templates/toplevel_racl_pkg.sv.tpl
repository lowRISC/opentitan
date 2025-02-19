// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gencmd}
<% import textwrap %>\

package top_${topcfg["name"]}_racl_pkg;
  import top_racl_pkg::*;

<%doc>
  Note: The RACL parameters must be generated identically across multiple files.
        Thus, this template needs to be manually synced between the following files:
        util/raclgen.py
        util/topgen/templates/toplevel_racl_pkg.sv.tpl
        hw/top_darjeeling/templates/toplevel.sv.tpl
        hw/top_earlgrey/templates/toplevel.sv.tpl
        hw/top_englishbreakfast/templates/toplevel.sv.tpl
</%doc>\
<% import raclgen.lib as raclgen %>\
<% import math %>\
% if 'racl' in topcfg:
  /**
   * RACL groups:
% for racl_group in topcfg['racl']['policies']:
<% policy_names = [policy['name'] for policy in topcfg['racl']['policies'][racl_group]] %>\
<% policy_name_len = max( (len(name) for name in policy_names) ) %>\
<% policy_idx_len = math.ceil(math.log10(max(1,len(policy_names)+1))) %>\
   *   ${racl_group}
  % for policy_idx, policy_name in enumerate(policy_names):
   *     ${f"{policy_name}".ljust(policy_name_len)} (Idx ${f"{policy_idx}".rjust(policy_idx_len)})
  % endfor
% endfor
   */

% endif
% for m in topcfg['module']:
  % if 'racl_mappings' in m:
    % for if_name in m['racl_mappings'].keys():
<% register_mapping = m['racl_mappings'][if_name]['register_mapping'] %>\
<% window_mapping = m['racl_mappings'][if_name]['window_mapping'] %>\
<% range_mapping = m['racl_mappings'][if_name]['range_mapping'] %>\
<% racl_group = m['racl_mappings'][if_name]['racl_group'] %>\
<% group_suffix = f"_{racl_group.upper()}" if racl_group and racl_group != "Null" else "" %>\
<% if_suffix = f"_{if_name.upper()}" if if_name else "" %>\
<% reg_name_len = max( (len(name) for name in register_mapping.keys()), default=0 ) %>\
<% window_name_len = max( (len(name) for name in window_mapping.keys()), default=0 ) %>\
<% policy_sel_name = f"RACL_POLICY_SEL_{m['name'].upper()}{group_suffix}{if_suffix}" %>\
  /**
   * Policy selection vector for ${m["name"]}
   *   TLUL interface name: ${if_name}
   *   RACL group: ${racl_group}
      % if len(register_mapping) > 0:
   *   Register to policy mapping:
        % for reg_name, policy_idx in register_mapping.items():
   *     ${f"{reg_name}:".ljust(reg_name_len+1)} ${policy_names[policy_idx]} (Idx ${f"{policy_idx}".rjust(policy_idx_len)})
        % endfor
      % endif
      % if len(window_mapping) > 0:
   *   Window to policy mapping:
        % for window_name, policy_idx in window_mapping.items():
   *     ${f"{window_name}:".ljust(window_name_len+1)} ${policy_names[policy_idx]} (Idx ${f"{policy_idx}".rjust(policy_idx_len)})
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
<% value =  ",\\n".join(map(raclgen.format_parameter_range_value, range_mapping)) %>\
  parameter racl_range_t ${policy_sel_name}_RANGES [${len(range_mapping)}] = '{
    ${value}
  };
      % endif

    % endfor
  % endif
% endfor
endpackage
