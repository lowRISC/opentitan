## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
##
## This connects the AST memory configuration signals to the memories defined in mem_cfg_consumers.
## mem_cfg_consumers must be of type:
## (struct field, flat inter-signal base name)
<%page args="mem_cfg_consumers"/>\
<%
  # Width of the widest left-hand side, so the '=' align across both directions.
  mem_cfg_lhs_pad = max(max(len(w) + len('_req') for f, w, in mem_cfg_consumers),
                        max(len('ast_mem_cfg_rsp.') + len(f) for f, w in mem_cfg_consumers))
%>\
  // Connect local memory configurations
% for field, wire in mem_cfg_consumers:
  assign ${(wire + '_req').ljust(mem_cfg_lhs_pad)} = ast_mem_cfg_req.${field};
  assign ${('ast_mem_cfg_rsp.' + field).ljust(mem_cfg_lhs_pad)} = ${wire}_rsp;
% endfor
