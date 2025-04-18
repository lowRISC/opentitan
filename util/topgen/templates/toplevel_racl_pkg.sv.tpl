// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gencmd}
<% import textwrap %>\

package top_${topcfg["name"]}_racl_pkg;
  import top_racl_pkg::*;

<% import raclgen.lib as raclgen %>\
<% import math %>\
% if 'racl' in topcfg:
  /**
   * RACL groups and policies:
% for racl_group in racl_config['policies']:
   *   ${racl_group}
<%
    policy_names = [policy['name'] for policy in racl_config['policies'][racl_group]]
    policy_name_len = max( (len(name) for name in policy_names) )
    policy_idx_len = math.ceil(math.log10(max(1,len(policy_names)+1)))
%>\
  % for policy_idx, policy_name in enumerate(policy_names):
   *     ${f"{policy_idx}".rjust(policy_idx_len)}: ${policy_name}
  % endfor
% endfor
   */

% endif
% for m in topcfg['module']:
  % for if_name, mapping in m.get('racl_mappings', {}).items():
<%
      racl_group = mapping['racl_group']
      policy_names = [policy['name'] for policy in racl_config['policies'][racl_group]]
      racl_tpl_args = {
        "register_mapping" : mapping.get('register_mapping', {}),
        "window_mapping"   : mapping.get('window_mapping', {}),
        "range_mapping"    : mapping.get('range_mapping', []),
        "policy_names"     : policy_names,
        "racl_group"       : racl_group,
        "module_name"      : m['name'],
        "ip_block"         : name_to_block[m['type']],
        "if_name"          : if_name
      }
%>\
<%include file="toplevel_racl_pkg_parameters.tpl" args="**racl_tpl_args"/>\

  % endfor
% endfor
endpackage
