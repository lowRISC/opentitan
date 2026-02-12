## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%page args="lib, top, name_to_block, plic_info"/>\
<%
  # Interrupt source 0 is tied to 0 to conform to the RISC-V PLIC spec.
  # The total number of interrupts is the sum of the widths of each entry
  # in the list, plus 1.
  plics = lib.find_modules(top["module"], "rv_plic", use_base_template_type=True)
  plics = [x["name"] for x in plics]
  for plic in plics:
    count = 1
    for x in top["interrupt"]:
      if x["outgoing"]:
        continue
      if x.get("plic") == plic:
        count += x.get("width", 1)
    prefix = (plic + "_") if len(plics) > 1 else ""
    vector = prefix + "intr_vector"
    plic_info[plic] = {"count": count, "vector": vector}
%>\
% for plic in plic_info.values():
  logic [${plic["count"]-1}:0]  ${plic["vector"]};
% endfor
  // Interrupt source list
% for m in top["module"]:
<%
  block = name_to_block[m['type']]
%>\
    % if not lib.is_inst(m) or "outgoing_interrupt" in m:
<% continue %>
    % endif
    % for intr in block.interrupts:
        % if "outgoing_interrupt" in m:
            <% continue %>
        % endif
        % if intr.bits.width() != 1:
  logic [${intr.bits.width()-1}:0] intr_${m["name"]}_${intr.name};
        % else:
  logic intr_${m["name"]}_${intr.name};
        % endif
    % endfor
% endfor
