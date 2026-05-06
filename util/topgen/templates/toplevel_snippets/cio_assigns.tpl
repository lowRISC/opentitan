## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%page args="top, feature_info, cio_info"/>\
% if feature_info["has_pinmux"]:
  // Pinmux connections
  // All muxed inputs
  % for sig in top["pinmux"]["ios"]:
    % if sig["connection"] == "muxed" and sig["type"] in ["inout", "input"]:
<% literal = lib.get_io_enum_literal(sig, 'mio_in') %>\
  assign cio_${sig["name"]}_p2d${"[" + str(sig["idx"]) +"]" if sig["idx"] !=-1  else ""} = mio_p2d[${literal}];
    % endif
  % endfor

  // All muxed outputs
  % for sig in top["pinmux"]["ios"]:
    % if sig["connection"] == "muxed" and sig["type"] in ["inout", "output"]:
<% literal = lib.get_io_enum_literal(sig, 'mio_out') %>\
  assign mio_d2p[${literal}] = cio_${sig["name"]}_d2p${"[" + str(sig["idx"]) +"]" if sig["idx"] !=-1  else ""};
    % endif
  % endfor

  // All muxed output enables
  % for sig in top["pinmux"]["ios"]:
    % if sig["connection"] == "muxed" and sig["type"] in ["inout", "output"]:
<% literal = lib.get_io_enum_literal(sig, 'mio_out') %>\
  assign mio_en_d2p[${literal}] = cio_${sig["name"]}_en_d2p${"[" + str(sig["idx"]) +"]" if sig["idx"] !=-1  else ""};
    % endif
  % endfor

  // All dedicated inputs
<% idx = 0 %>\
  logic [${cio_info["num_dio_total"]-1}:0] unused_dio_p2d;
  assign unused_dio_p2d = dio_p2d;
  % for sig in top["pinmux"]["ios"]:
<% literal = lib.get_io_enum_literal(sig, 'dio') %>\
    % if sig["connection"] != "muxed" and sig["type"] in ["inout"]:
  assign cio_${sig["name"]}_p2d${"[" + str(sig["idx"]) +"]" if sig["idx"] !=-1  else ""} = dio_p2d[${literal}];
    % elif sig["connection"] != "muxed" and sig["type"] in ["input"]:
  assign cio_${sig["name"]}_p2d${"[" + str(sig["idx"]) +"]" if sig["idx"] !=-1  else ""} = dio_p2d[${literal}];
    % endif
  % endfor

  // All dedicated outputs
  % for sig in top["pinmux"]["ios"]:
<% literal = lib.get_io_enum_literal(sig, 'dio') %>\
    % if sig["connection"] != "muxed" and sig["type"] in ["inout"]:
  assign dio_d2p[${literal}] = cio_${sig["name"]}_d2p${"[" + str(sig["idx"]) +"]" if sig["idx"] !=-1  else ""};
    % elif sig["connection"] != "muxed" and sig["type"] in ["input"]:
  assign dio_d2p[${literal}] = 1'b0;
    % elif sig["connection"] != "muxed" and sig["type"] in ["output"]:
  assign dio_d2p[${literal}] = cio_${sig["name"]}_d2p${"[" + str(sig["idx"]) +"]" if sig["idx"] !=-1  else ""};
    % endif
  % endfor

  // All dedicated output enables
  % for sig in top["pinmux"]["ios"]:
<% literal = lib.get_io_enum_literal(sig, 'dio') %>\
    % if sig["connection"] != "muxed" and sig["type"] in ["inout"]:
  assign dio_en_d2p[${literal}] = cio_${sig["name"]}_en_d2p${"[" + str(sig["idx"]) +"]" if sig["idx"] !=-1  else ""};
    % elif sig["connection"] != "muxed" and sig["type"] in ["input"]:
  assign dio_en_d2p[${literal}] = 1'b0;
    % elif sig["connection"] != "muxed" and sig["type"] in ["output"]:
  assign dio_en_d2p[${literal}] = cio_${sig["name"]}_en_d2p${"[" + str(sig["idx"]) +"]" if sig["idx"] !=-1  else ""};
    % endif
  % endfor
% endif
