## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%page args="top, plic_info"/>\
% for plic, info in plic_info.items():
<%
  base = info["count"]
  default_plic = top.get("default_plic", None)
  max_namelen = max(len(irq["name"]) for irq in top["interrupt"]
    if not(irq['incoming'] or irq['plic'] != plic))
  if plic == default_plic and top['incoming_interrupt']:
    max_namelen = max(max_namelen +
      [len(irq["irq_group"]) for irq, _ in top["incoming_interrupt"]])
    max_namelen += 22
  else:
    max_namelen += 6
%>\
  assign ${info["vector"]} = {
  % if plic == default_plic:
  %   for irq_group, irqs in reversed(top['incoming_interrupt'].items()):
<%
  base -= len(irqs)
  if len(irqs) > 1:
    intr_comment = f"// IDs [{base} +: {intr['width']}]"
  else:
    intr_comment = f"// ID {base}"
%>\
    ${lib.ljust(f"incoming_interrupt_${irq_group}_i,", max_namelen)} ${intr_comment}
  %   endfor
  % endif
  % for intr in top["interrupt"][::-1]:
    % if intr['incoming'] or intr['plic'] != plic:
<%      continue %>\
    % endif
<%
  base -= intr["width"]
  if intr["width"] > 1:
    intr_comment = f"// IDs [{base} +: {intr['width']}]"
  else:
    intr_comment = f"// ID {base}"
%>\
    ${lib.ljust(f"intr_{intr['name']},", max_namelen)} ${intr_comment}
  % endfor
    1'b0 // ID 0 is a special case and tied to zero.
  };
% endfor
