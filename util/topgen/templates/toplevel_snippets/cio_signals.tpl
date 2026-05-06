## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%page args="top, feature_info, cio_info"/>\
  // Signals
% if feature_info["has_pinmux"]:
  logic [${cio_info["num_mio_inputs"] - 1}:0] mio_p2d;
  logic [${cio_info["num_mio_outputs"] - 1}:0] mio_d2p;
  logic [${cio_info["num_mio_outputs"] - 1}:0] mio_en_d2p;
  logic [${cio_info["num_dio_total"] - 1}:0] dio_p2d;
  logic [${cio_info["num_dio_total"] - 1}:0] dio_d2p;
  logic [${cio_info["num_dio_total"] - 1}:0] dio_en_d2p;
% for m in top["module"]:
  % if not lib.is_inst(m):
<% continue %>
  % endif
<%
  block = name_to_block[m['type']]
  inouts, inputs, outputs = block.xputs
%>\
  // ${m["name"]}
  % for p_in in inputs + inouts:
  logic ${lib.bitarray(p_in.bits.width(), cio_info["max_sigwidth"])} cio_${m["name"]}_${p_in.name}_p2d;
  % endfor
  % for p_out in outputs + inouts:
  logic ${lib.bitarray(p_out.bits.width(), cio_info["max_sigwidth"])} cio_${m["name"]}_${p_out.name}_d2p;
  logic ${lib.bitarray(p_out.bits.width(), cio_info["max_sigwidth"])} cio_${m["name"]}_${p_out.name}_en_d2p;
  % endfor
% endfor
% endif\
