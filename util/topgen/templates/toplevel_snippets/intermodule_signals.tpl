## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%from reggen.params import Parameter%>\
<%page args="top, domain"/>\
<%unused_resets = lib.get_unused_resets(top)%>\
<%
  unused_im_defs, undriven_im_defs = lib.get_dangling_im_def(
    [d for d in top["inter_signal"]["definitions"] if d["domain"] == domain])
%>\
## Inter-module Definitions
% if lib.get_intermodule_list(top, domain):
  // Define inter-module signals
% endif
% for sig in lib.get_intermodule_list(top, domain):
  % if isinstance(sig["width"], Parameter):
  ${lib.im_defname(sig)} [${sig["width"].name_top}-1:0] ${sig["signame"]};
  % else:
  ${lib.im_defname(sig)} ${lib.bitarray(sig["width"],1)} ${sig["signame"]};
  % endif
% endfor

## Mixed connection to port
## Index greater than 0 means a port is assigned to an inter-module array
## whereas an index of 0 means a port is directly driven by a module
  // Create mixed connections to ports
% for port in lib.get_intermodule_ports(top, domain):
  % if port['conn_type'] and isinstance(port['index'], list):
    % for idx_port, idx in enumerate(port['index']):
    % if port['direction'] == 'in':
  assign ${port['netname']}[${idx}] = ${port['signame']}[${idx_port}];
    % else:
  assign ${port['signame']}[${idx_port}] = ${port['netname']}[${idx}];
    % endif
    % endfor
  % elif port['conn_type'] and port['index'] != -1:
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
% if len(unused_im_defs) > 0:
  // Dummy signal definitions for unused partial inter-module signals
% for sig in unused_im_defs:
<%
  width = sig['width'].default if isinstance(sig['width'], Parameter) else sig['width']
%>\
  % for idx in range(sig['end_idx'], width):
  ${lib.im_defname(sig)} unused_${sig["signame"]}${idx};
  % endfor
% endfor

% endif\

% if len(unused_im_defs) > 0:
  // Assign unused partial inter-module signals
% for sig in unused_im_defs:
<%
  width = sig['width'].default if isinstance(sig['width'], Parameter) else sig['width']
%>\
  % for idx in range(sig['end_idx'], width):
  assign unused_${sig["signame"]}${idx} = ${sig["signame"]}[${idx}];
  % endfor
% endfor

% endif\

% if len(undriven_im_defs) > 0:
  // Assign undriven partial inter-module signals
% for sig in undriven_im_defs:
<%
  width = sig['width'].default if isinstance(sig['width'], Parameter) else sig['width']
%>\
  % for idx in range(sig['end_idx'], width):
  assign ${sig["signame"]}[${idx}] = ${sig["default"]};
  % endfor
% endfor
% endif\
