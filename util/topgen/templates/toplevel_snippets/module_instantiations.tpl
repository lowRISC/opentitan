## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%from collections import defaultdict%>\
<%from topgen.merge import is_unmanaged_reset%>\
<%from topgen.merge import alert_handler_signals%>\
<%page args="top, domain"/>\
<%
if lib.find_module(top["module"], "pinmux").get("domain") == domain:
  cio_suffix_o, cio_suffix_i = ("", "")
else:
  cio_suffix_o, cio_suffix_i = ("_o", "_i")
%>\
  // Instantiation of IPs
<% outgoing_interrupt_idx = defaultdict(int) %>\
% for m in lib.get_all_modules(top, domain=domain):
<%
if not lib.is_inst(m):
  continue

block = name_to_block[m['type']]
raw_inouts, raw_inputs, raw_outputs = block.xputs

## For split IPs, determine which partition(s) are emitted in this power-domain
## pass. Normally one partition maps to a given PD, but a split IP whose two
## partitions share a PD emits both here. Non-split IPs always yield a single
## 'primary' partition, reproducing the original output exactly.
is_split = m.get("is_split_ip", False)
%>\
% for partition in lib.get_module_partitions(m, domain):
<%
if is_split and partition == "secondary":
  clock_connections = m["clock_connections_secondary"]
  reset_connections = m["reset_connections_secondary"]
else:
  clock_connections = m["clock_connections"]
  reset_connections = m["reset_connections"]

part_suffix = "_part_" + partition if is_split else ""
mod_type = m["type"] + part_suffix
inst_name = m["name"] + part_suffix

## Filter comportable objects to those belonging to the emitted partition.
inputs = [s for s in raw_inputs if getattr(s, "partition", "primary") == partition]
outputs = [s for s in raw_outputs if getattr(s, "partition", "primary") == partition]
inouts = [s for s in raw_inouts if getattr(s, "partition", "primary") == partition]
interrupts = [i for i in block.interrupts
              if getattr(i, "partition", "primary") == partition]
inter_signals = [s for s in m.get("inter_signal_list", [])
                 if s.get("partition", "primary") == partition]

port_list = inputs + outputs + inouts
max_sigwidth = max(len(x.name) for x in port_list) if port_list else 0
max_intrwidth = (max(len(x.name) for x in interrupts)
                 if interrupts else 0)

alert_key = "module_" + m["name"]
if partition != "primary":
  alert_key += "_" + partition
alert_info = top["alert_connections"].get(alert_key, {})
has_params, param_items = lib.get_params(top, m, partition)

## Scan / DFT ports are emitted only for the primary partition of a split IP.
has_scan = (block.scan or block.scan_reset or block.scan_en) and \
    partition == "primary"
has_interrupts = len(interrupts) > 0
has_cio_inputs = len(inputs + inouts) > 0
has_cio_outputs = len(outputs + inouts) > 0
%>\
  % if has_params:
  ${mod_type} #(
<%include file="/toplevel_snippets/racl_parameters.tpl" args="module=m, top=top, block=block"/>\
    % for param_name, param_value in param_items:
    ${param_name}(${param_value})${"," if not loop.last else ""}
    % endfor
  ) u_${inst_name} (
  % else:
  ${mod_type} u_${inst_name} (
  % endif
    // Clock and reset connections
  % for k, v in clock_connections.items():
    .${k}(${v}),
  % endfor
  % for port, reset in reset_connections.items():
<%
    is_shadowed_port = lib.is_shadowed_port(block, port)
    unmanaged_reset = is_unmanaged_reset(top, reset['name'])
    reset_port = lib.get_reset_path(top, reset, domain, False, unmanaged_reset)
    shadowed_port = lib.get_reset_path(top, reset, domain, True, unmanaged_reset)
%>\
  % if is_shadowed_port:
    .${lib.shadow_name(port)}(${shadowed_port}),
  % endif
    .${port}(${reset_port}),
  % endfor

% if has_scan:
    // DFT/scan connections
  % if block.scan:
    .scanmode_i,
  % endif
  % if block.scan_reset:
    .scan_rst_ni,
  % endif
  % if block.scan_en:
    .scan_en_i,
  % endif

% endif\

% if has_interrupts:
    // Interrupts
  % for intr in interrupts:
    % if "outgoing_interrupt" in m:
<%
      intr_group = m["outgoing_interrupt"]
      intr_idx = outgoing_interrupt_idx[intr_group]
      intr_slice = str(intr_idx + intr.bits.width() - 1) + ":" + str(intr_idx)
      outgoing_interrupt_idx[intr_group] += intr.bits.width()
%>\
    // External interrupt group "${intr_group}" [${intr_slice}]: ${intr.name}
    .${lib.ljust("intr_"+intr.name+"_o",max_intrwidth+7)}(outgoing_interrupt_${intr_group}_o[${intr_slice}]),
    % else:
    .${lib.ljust("intr_"+intr.name+"_o",max_intrwidth+7)}(intr_${m["name"]}_${intr.name}),
    % endif
  % endfor

% endif\

% if alert_info:
    % for comment in alert_info["comments"]:
    // ${comment}
    % endfor
    .alert_tx_o(${alert_info["tx_expr"]}),
    .alert_rx_i(${alert_info["rx_expr"]}),
% endif\

<%include file="/toplevel_snippets/racl_signals.tpl" args="module=m, top=top, block=block"/>\

% if has_cio_inputs:
    // CIO inputs
  % for p_in in inputs + inouts:
    .${lib.ljust("cio_"+p_in.name+"_i",max_sigwidth+9)}(cio_${m["name"]}_${p_in.name}_p2d${cio_suffix_i}),
  % endfor

% endif\

% if has_cio_outputs:
    // CIO outputs
  % for p_out in outputs + inouts:
    .${lib.ljust("cio_"+p_out.name+"_o",   max_sigwidth+9)}(cio_${m["name"]}_${p_out.name}_d2p${cio_suffix_o}),
    .${lib.ljust("cio_"+p_out.name+"_en_o",max_sigwidth+9)}(cio_${m["name"]}_${p_out.name}_en_d2p${cio_suffix_o}),
  % endfor

% endif\

% if inter_signals:
    // Inter-module signals
  % for sig in inter_signals:
<%
if m.get("template_type") in ["rv_plic", "pinmux", "alert_handler"]:
  term = ","
elif loop.last:
  term = ""
else:
  term = ","
%>\
    ## TODO: handle below condition in lib.py
    % if sig['type'] == "req_rsp":
    .${lib.im_portname(sig,"req")}(${lib.im_netname(sig, "req")}),
    .${lib.im_portname(sig,"rsp")}(${lib.im_netname(sig, "rsp")})${term}
    % elif sig['type'] == "io":
    .${lib.im_portname(sig,"io")}(${lib.im_netname(sig, "io")})${term}
    % elif sig['type'] == "uni":
    .${lib.im_portname(sig)}(${lib.im_netname(sig)})${term}
    % endif
  % endfor
% endif\

% if m.get("template_type") == "rv_plic":
<% prefix = m["name"] + "_" if len(top["plic_info"]) > 1 else "" %>

    // Interrupt source vector
    .intr_src_i(${prefix}intr_vector)
% elif m.get("template_type") == "pinmux":

    .periph_to_mio_i   (mio_d2p   ),
    .periph_to_mio_oe_i(mio_en_d2p),
    .mio_to_periph_o   (mio_p2d   ),

    .mio_attr_o,
    .mio_out_o,
    .mio_oe_o,
    .mio_in_i,

    .periph_to_dio_i   (dio_d2p   ),
    .periph_to_dio_oe_i(dio_en_d2p),
    .dio_to_periph_o   (dio_p2d   ),

    .dio_attr_o,
    .dio_out_o,
    .dio_oe_o,
    .dio_in_i
% elif m.get("template_type") == "alert_handler":
<% alert_tx, alert_rx = alert_handler_signals(m["type"]) %>\

    // Alert signals
    .alert_rx_o(${alert_rx}),
    .alert_tx_i(${alert_tx}),

    // Reset and clock gating indications for each low power group
    .lpg_cg_en_i (lpg_cg_en ),
    .lpg_rst_en_i(lpg_rst_en)
% endif
  );

% endfor
% endfor
