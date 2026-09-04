## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%page args="top, name_to_block, domain"/>\
% for name, plic in top["plic_info"].items():
<% prefix = name + "_" if len(top["plic_info"]) > 1 else "" %>
% if plic["domain"] == domain:
  logic [${plic["count_tot"]-1}:0] ${prefix}intr_vector;
% endif
% endfor
  // Interrupt source list
% for m in lib.get_all_modules(top, domain):
    % if not lib.is_inst(m) or "outgoing_interrupt" in m:
<% continue %>
    % endif
<%
  block = name_to_block[m['type']]
  ## A split IP is returned in every power domain it occupies, so declare each
  ## interrupt only in the domain of the partition that owns it.
  interrupts = [i for p in lib.get_module_partitions(m, domain)
                for i in block.interrupts_for(p)]
%>\
    % for intr in interrupts:
      % if intr.bits.width() != 1:
  logic [${intr.bits.width()-1}:0] intr_${m["name"]}_${intr.name};
      % else:
  logic intr_${m["name"]}_${intr.name};
      % endif
    % endfor
% endfor
