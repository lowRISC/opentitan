## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%page args="top"/>\
  // Local Parameters
% for m in top["module"]:
  % if not lib.is_inst(m):
<% continue %>
  % endif
<%
    localparams = [p for p in m["param_list"] if p.get("local") == "true" and p.get("expose") == "true"]
    if not len(localparams):
        continue
%>\
  // local parameters for ${m['name']}
  % for p_exp in localparams:
<%
    p_type = p_exp.get('type')
    p_type_word = p_type + ' ' if p_type else ''

    p_lhs = f'{p_type_word}{p_exp["name_top"]}'
    p_rhs = p_exp['default']
%>\
    % if 13 + len(p_lhs) + 3 + len(str(p_rhs)) + 1 < 100:
  localparam ${p_lhs} = ${p_rhs};
    % else:
  localparam ${p_lhs} =
      ${p_rhs};
    % endif
  % endfor
% endfor
