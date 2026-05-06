## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%page args="top"/>\
<%
last_modidx_with_params = lib.idx_of_last_module_with_params(top)
%>\
% if not lib.num_rom_ctrl(top["module"]):
  // Manually defined parameters
  parameter BootRomInitFile = "",

% endif
  // Auto-inferred parameters
% for m in top["module"]:
  % if not lib.is_inst(m):
<% continue %>
  % endif
  // parameters for ${m['name']}
  % for p_exp in [p for p in m["param_list"] if p.get("local") == "false" and p.get("expose") == "true" ]:
<%
    p_type = p_exp.get('type')
    p_type_word = p_type + ' ' if p_type else ''

    p_lhs = f'{p_type_word}{p_exp["name_top"]}'

    if 'unpacked_dimensions' in p_exp:
      p_lhs += p_exp['unpacked_dimensions']

    p_rhs = p_exp['default']

    params_follow = not loop.last or loop.parent.index < last_modidx_with_params
    comma_char = ',' if params_follow else ''
%>\
    % if 12 + len(p_lhs) + 3 + len(str(p_rhs)) + 1 < 100:
  parameter ${p_lhs} = ${p_rhs}${comma_char}
    % else:
  parameter ${p_lhs} =
      ${p_rhs}${comma_char}
    % endif
  % endfor
% endfor
