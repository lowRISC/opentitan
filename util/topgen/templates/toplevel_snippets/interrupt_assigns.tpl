## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%page args="top, domain"/>\
% for plic, info in top["plic_info"].items():
% if info["domain"] == domain:
<%
  base = info["count_tot"]
  count_pd = info["count_pd"].copy()
  default_plic = top.get("default_plic", None)
  vector_prefix = plic + "_" if len(top["plic_info"]) > 1 else ""
  max_namelen = max(len(irq["name"]) for irq in top["interrupt"]
    if not(irq['incoming'] or irq['plic'] != plic))
  if plic == default_plic and top['incoming_interrupt']:
    max_namelen = max(max_namelen +
      [len(irq["irq_group"]) for irq, _ in top["incoming_interrupt"]])
    max_namelen += 22
  else:
    max_namelen += 6
%>\
  // Interrupt assignments
  assign ${vector_prefix}intr_vector = {
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
  if intr["domain"] == domain:
    intr_sig = f"intr_{intr['name']}"
  else:
    count_pd[intr["domain"]] -= intr["width"]
    idx_l = count_pd[intr["domain"]]
    plic_str = "_" + plic if len(top["plic_info"]) > 1 else ""
    intr_sig = f"intr_vector{plic_str}_pd_{intr['domain'].lower()}_i[{idx_l}]"
    intr_comment += f" ({intr['name']})"
%>\
    ${lib.ljust(f"{intr_sig},", max_namelen)} ${intr_comment}
  % endfor
    1'b0 // ID 0 is a special case and tied to zero.
  };
% else:
<%
  intrs = [i for i in top["interrupt"] if i["plic"] == plic and i["domain"] == domain]
  if len(intrs) == 0:
    continue
  plic_str = "_" + plic if len(top["plic_info"]) > 1 else ""
%>\
  // Interrupt vector to PLIC ${plic} in power domain ${info["domain"]}
  assign intr_vector${plic_str}_o = {
    % for intr in intrs[::-1]:
    intr_${intr["name"]}${"," if not loop.last else ""}
    % endfor
  };
% endif
% endfor
