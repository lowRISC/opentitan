// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//======================================================================
// This file contains outputs of rstmgr tied to constants.
//======================================================================

% for rst in leaf_rsts:
<%
  names = [rst['name']]
  if rst['shadowed']:
    names.append(f'{names[0]}_shadowed')
%>\
  % for name in names:
    % for domain in power_domains:
      % if domain not in rst['domains']:
-module_node rstmgr resets_o.rst_${name}_n[Domain${domain}Sel]
-module_node rstmgr rst_en_o.${name}[Domain${domain}Sel]
      % endif
    % endfor
  % endfor
% endfor
