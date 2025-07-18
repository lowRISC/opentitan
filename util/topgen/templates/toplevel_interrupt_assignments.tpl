## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%page args="top, plic_info"/>\
% for plic, info in plic_info.items():
<%
   base = info["count"]
   default_plic = top.get("default_plic", None)
%>\
  assign ${info["vector"]} = {
  % if plic == default_plic:
  %   for irq_group, irqs in reversed(top['incoming_interrupt'].items()):
  <%    base -= len(irqs) %>\
    incoming_interrupt_${irq_group}_i, // IDs [${base} +: ${len(irqs)}]
  %   endfor
  % endif
  % for intr in top["interrupt"][::-1]:
    % if intr['incoming'] or intr['plic'] != plic:
<%      continue %>\
    % endif
<% base -= intr["width"] %>\
      intr_${intr["name"]}, // IDs [${base} +: ${intr['width']}]
  % endfor
      1'b 0 // ID [0 +: 1] is a special case and tied to zero.
  };
% endfor
