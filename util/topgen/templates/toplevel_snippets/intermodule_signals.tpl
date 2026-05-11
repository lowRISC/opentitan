## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%from reggen.params import Parameter%>\
<%page args="top"/>\
<%unused_resets = lib.get_unused_resets(top)%>\
<%unused_im_defs, undriven_im_defs = lib.get_dangling_im_def(top["inter_signal"]["definitions"])%>\
## Inter-module Definitions
% if len(top["inter_signal"]["definitions"]) >= 1:
  // define inter-module signals
% endif
% for sig in top["inter_signal"]["definitions"]:
  % if isinstance(sig["width"], Parameter):
  ${lib.im_defname(sig)} [${sig["width"].name_top}-1:0] ${sig["signame"]};
  % else:
  ${lib.im_defname(sig)} ${lib.bitarray(sig["width"],1)} ${sig["signame"]};
  % endif
% endfor

## Mixed connection to port
## Index greater than 0 means a port is assigned to an inter-module array
## whereas an index of 0 means a port is directly driven by a module
  // define mixed connection to port
% for port in top['inter_signal']['external']:
  % if port['conn_type'] and port['index'] > 0:
    % if port['direction'] == 'in':
  assign ${port['netname']}[${port['index']}] = ${port['signame']};
    % else:
  assign ${port['signame']} = ${port['netname']}[${port['index']}];
    % endif
  % elif port['conn_type']:
    % if port['direction'] == 'in':
  assign ${port['netname']} = ${port['signame']};
    % else:
  assign ${port['signame']} = ${port['netname']};
    % endif
  % endif
% endfor

## Partial inter-module definition tie-off
  // Define partial inter-module tie-off
% for sig in unused_im_defs:
<%
  width = sig['width'].default if isinstance(sig['width'], Parameter) else sig['width']
%>\
  % for idx in range(sig['end_idx'], width):
  ${lib.im_defname(sig)} unused_${sig["signame"]}${idx};
  % endfor
% endfor

  // Assign partial inter-module tie-off
% for sig in unused_im_defs:
<%
  width = sig['width'].default if isinstance(sig['width'], Parameter) else sig['width']
%>\
  % for idx in range(sig['end_idx'], width):
  assign unused_${sig["signame"]}${idx} = ${sig["signame"]}[${idx}];
  % endfor
% endfor
% for sig in undriven_im_defs:
<%
  width = sig['width'].default if isinstance(sig['width'], Parameter) else sig['width']
%>\
  % for idx in range(sig['end_idx'], width):
  assign ${sig["signame"]}[${idx}] = ${sig["default"]};
  % endfor
% endfor
