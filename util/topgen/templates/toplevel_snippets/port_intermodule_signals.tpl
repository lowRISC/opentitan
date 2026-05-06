## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%from reggen.params import Parameter%>\
<%page args="top"/>\
% if top["inter_signal"]["external"]:
  // Inter-module Signal External type
  % for sig in top["inter_signal"]["external"]:
    % if isinstance(sig["width"], Parameter):
  ${lib.get_direction(sig)} ${lib.im_defname(sig)} [${sig["width"].name_top}-1:0] ${sig["signame"]},
    % else:
  ${lib.get_direction(sig)} ${lib.im_defname(sig)} ${lib.bitarray(sig["width"],1)} ${sig["signame"]},
    % endif
  % endfor

% endif
