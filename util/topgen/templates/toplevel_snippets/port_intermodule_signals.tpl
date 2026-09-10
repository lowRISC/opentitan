## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%from reggen.params import Parameter%>\
<%page args="top, domain, last_snippet"/>\
<%inter_pd = False if domain == "" else None%>\
% if lib.get_intermodule_ports(top, domain, inter_pd):
  // Inter-module Signal External type
  % for sig in lib.get_intermodule_ports(top, domain, inter_pd):
<%comma_char = "" if loop.last and last_snippet else ","%>\
    % if isinstance(sig["width"], Parameter):
  ${lib.get_direction(sig)} ${lib.im_defname(sig)} [${sig["width"].name_top}-1:0] ${sig["signame"]}${comma_char}
    % else:
  ${lib.get_direction(sig)} ${lib.im_defname(sig)} ${lib.bitarray(sig["width"],1)} ${sig["signame"]}${comma_char}
    % endif
  % endfor

% endif
