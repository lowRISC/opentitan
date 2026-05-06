## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%from collections import defaultdict%>\
<%from topgen.merge import is_unmanaged_reset%>\
<%from topgen.merge import alert_handler_signals%>\
<%page args="top, plic_info"/>\
  // Peripheral Instantiation
<% outgoing_interrupt_idx = defaultdict(int) %>\
% for m in top["module"]:
<%
if not lib.is_inst(m):
  continue

block = name_to_block[m['type']]
inouts, inputs, outputs = block.xputs

port_list = inputs + outputs + inouts
max_sigwidth = max(len(x.name) for x in port_list) if port_list else 0
max_intrwidth = (max(len(x.name) for x in block.interrupts)
                 if block.interrupts else 0)
alert_info = top["alert_connections"].get("module_" + m["name"], {})
has_params, param_items = lib.get_params(top, m)
%>\
  % if has_params:
  ${m["type"]} #(
<%include file="/toplevel_snippets/racl_parameters.tpl" args="module=m, top=top, block=block"/>\
    % for param_name, param_value in param_items:
    ${param_name}(${param_value})${"," if not loop.last else ""}
    % endfor
  ) u_${m["name"]} (
  % else:
  ${m["type"]} u_${m["name"]} (
  % endif
  % for p_in in inputs + inouts:
    % if loop.first:

    // Input
    % endif
    .${lib.ljust("cio_"+p_in.name+"_i",max_sigwidth+9)} (cio_${m["name"]}_${p_in.name}_p2d),
  % endfor
  % for p_out in outputs + inouts:
    % if loop.first:

    // Output
    % endif
    .${lib.ljust("cio_"+p_out.name+"_o",   max_sigwidth+9)} (cio_${m["name"]}_${p_out.name}_d2p),
    .${lib.ljust("cio_"+p_out.name+"_en_o",max_sigwidth+9)} (cio_${m["name"]}_${p_out.name}_en_d2p),
  % endfor
  % for intr in block.interrupts:
    % if loop.first:

    // Interrupt
    % endif
    % if "outgoing_interrupt" in m:
<%
      intr_group = m["outgoing_interrupt"]
      intr_idx = outgoing_interrupt_idx[intr_group]
      intr_slice = str(intr_idx + intr.bits.width() - 1) + ":" + str(intr_idx)
      outgoing_interrupt_idx[intr_group] += intr.bits.width()
%>\
    // External interrupt group "${intr_group}" [${intr_slice}]: ${intr.name}
    .${lib.ljust("intr_"+intr.name+"_o",max_intrwidth+7)} (outgoing_interrupt_${intr_group}_o[${intr_slice}]),
    % else:
    .${lib.ljust("intr_"+intr.name+"_o",max_intrwidth+7)} (intr_${m["name"]}_${intr.name}),
    % endif
  % endfor
  % if alert_info:
    % for comment in alert_info["comments"]:
    % if loop.first:

    % endif
    // ${comment}
    % endfor
    .alert_tx_o  ( ${alert_info["tx_expr"]} ),
    .alert_rx_i  ( ${alert_info["rx_expr"]} ),
  % endif
<%include file="/toplevel_snippets/racl_signals.tpl" args="module=m, top=top, block=block"/>\
  ## TODO: Inter-module Connection
  % if m.get('inter_signal_list'):

    // Inter-module signals
    % for sig in m['inter_signal_list']:
      ## TODO: handle below condition in lib.py
      % if sig['type'] == "req_rsp":
    .${lib.im_portname(sig,"req")}(${lib.im_netname(sig, "req")}),
    .${lib.im_portname(sig,"rsp")}(${lib.im_netname(sig, "rsp")}),
      % elif sig['type'] == "io":
    .${lib.im_portname(sig,"io")}(${lib.im_netname(sig, "io")}),
      % elif sig['type'] == "uni":
        ## TODO: Broadcast type
        ## TODO: default for logic type
    .${lib.im_portname(sig)}(${lib.im_netname(sig)}),
      % endif
    % endfor
  % endif
  % if m.get("template_type") == "rv_plic":
    .intr_src_i (${plic_info[m["name"]]["vector"]}),
  % endif
  % if m.get("template_type") == "pinmux":

    .periph_to_mio_i      (mio_d2p    ),
    .periph_to_mio_oe_i   (mio_en_d2p ),
    .mio_to_periph_o      (mio_p2d    ),

    .mio_attr_o,
    .mio_out_o,
    .mio_oe_o,
    .mio_in_i,

    .periph_to_dio_i      (dio_d2p    ),
    .periph_to_dio_oe_i   (dio_en_d2p ),
    .dio_to_periph_o      (dio_p2d    ),

    .dio_attr_o,
    .dio_out_o,
    .dio_oe_o,
    .dio_in_i,

  % endif
  % if m.get("template_type") == "alert_handler":
<% alert_tx, alert_rx = alert_handler_signals(m["type"]) %>\
    // alert signals
    .alert_rx_o  ( ${alert_rx} ),
    .alert_tx_i  ( ${alert_tx} ),
    // synchronized clock gated / reset asserted
    // indications for each alert
    .lpg_cg_en_i  ( lpg_cg_en  ),
    .lpg_rst_en_i ( lpg_rst_en ),
  % endif
  % if block.scan:
    .scanmode_i,
  % endif
  % if block.scan_reset:
    .scan_rst_ni,
  % endif
  % if block.scan_en:
    .scan_en_i,
  % endif

    // Clock and reset connections
  % for k, v in m["clock_connections"].items():
    .${k} (${v}),
  % endfor
  % for port, reset in m["reset_connections"].items():
<%
    is_shadowed_port = lib.is_shadowed_port(block, port)
    unmanaged_reset = is_unmanaged_reset(top, reset['name'])
    reset_port = lib.get_reset_path(top, reset, False, unmanaged_reset)
    shadowed_port = lib.get_reset_path(top, reset, True, unmanaged_reset)
%>\
  % if is_shadowed_port:
    .${lib.shadow_name(port)} (${shadowed_port}),
  % endif
    .${port} (${reset_port})${"," if not loop.last else ""}
  % endfor
  );

% endfor
