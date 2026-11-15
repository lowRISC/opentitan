## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%from topgen.merge import alert_handler_signals%>\
<%page args="top, feature_info, cio_info, domain"/>\
% if feature_info["has_pinmux"]:
% if lib.find_module(top["module"], "pinmux").get("domain") == domain:
% if cio_info["num_mio_pads"] != 0:
  // Multiplexed I/O
  input  logic ${lib.bitarray(cio_info["num_mio_pads"], cio_info["max_sigwidth"])} mio_in_i,
  output logic ${lib.bitarray(cio_info["num_mio_pads"], cio_info["max_sigwidth"])} mio_out_o,
  output logic ${lib.bitarray(cio_info["num_mio_pads"], cio_info["max_sigwidth"])} mio_oe_o,

% endif\

% if cio_info["num_dio_total"] != 0:
  // Dedicated I/O
  input  logic ${lib.bitarray(cio_info["num_dio_total"], cio_info["max_sigwidth"])} dio_in_i,
  output logic ${lib.bitarray(cio_info["num_dio_total"], cio_info["max_sigwidth"])} dio_out_o,
  output logic ${lib.bitarray(cio_info["num_dio_total"], cio_info["max_sigwidth"])} dio_oe_o,

% endif\

  // Pad attributes to padring
  output prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NMioPads-1:0] mio_attr_o,
  output prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NDioPads-1:0] dio_attr_o,

% endif
% endif\

% for irq_group, irqs in top['incoming_interrupt'].items():
  // Incoming interrupt of group ${irq_group}
  input logic [${len(irqs)-1}:0] incoming_interrupt_${irq_group}_i,
% endfor\

% for irq_group, irqs in top["outgoing_interrupt"].items():
  // Outgoing interrupt of group ${irq_group}
  output logic [top_${top["name"]}_pkg::NOutgoingInterrupts${irq_group.capitalize()}-1:0] outgoing_interrupt_${irq_group}_o,
% endfor\

% for name, plic in top["plic_info"].items():
<% prefix = "_" + name if len(top["plic_info"]) > 1 else "" %>\
% if plic["domain"] == domain:
  % for pd in top["power"]["domains"]:
<% if pd == domain: continue %>\
<% pd_len = plic["count_pd"][pd] - 1 %>\
    % if pd_len >= 0:
  // Interrupts from power domain ${pd}
  input  logic [${pd_len}:0] intr_vector${prefix}_pd_${pd.lower()}_i,
    % endif
  % endfor
% else:
<% pd_len = plic["count_pd"][domain] - 1 %>\
  % if pd_len >= 0:
  // Interrupts to PLIC ${name} in power domain ${plic["domain"]}
  output logic [${pd_len}:0] intr_vector${prefix}_o,
  % endif
% endif
% endfor

% if feature_info["has_alert_handler"]:
% for name, ah in top["alert_handler_info"].items():
<% signals = alert_handler_signals(name) %>\
% if ah["domain"] == domain:
  % for pd in top["power"]["domains"]:
<% if pd == domain: continue %>\
<% pd_len = ah["count_pd"][pd] - 1 %>\
    % if pd_len >= 0:
  // Alerts from power domain ${pd}
  output prim_alert_pkg::alert_rx_t [${pd_len}:0] ${signals[1]}_pd_${pd.lower()}_o,
  input  prim_alert_pkg::alert_tx_t [${pd_len}:0] ${signals[0]}_pd_${pd.lower()}_i,
    % endif
  % endfor
% else:
<% pd_len = ah["count_pd"][domain] - 1 %>\
  % if pd_len >= 0:
  // Alerts to power domain ${ah["domain"]}
  input  prim_alert_pkg::alert_rx_t [${pd_len}:0] ${signals[1]}_i,
  output prim_alert_pkg::alert_tx_t [${pd_len}:0] ${signals[0]}_o,
  % endif
% endif
% endfor

% endif\

% for alert_group in top['outgoing_alert'].keys():
  // Outgoing alerts for group ${alert_group}
  output prim_alert_pkg::alert_tx_t [top_${top["name"]}_pkg::NOutgoingAlerts${alert_group.capitalize()}Pd${domain.capitalize()}-1:0] outgoing_alert_${alert_group}_tx_o,
  input  prim_alert_pkg::alert_rx_t [top_${top["name"]}_pkg::NOutgoingAlerts${alert_group.capitalize()}Pd${domain.capitalize()}-1:0] outgoing_alert_${alert_group}_rx_i,
% if lib.find_module(top["module"], "clkmgr", domain=domain):
  output prim_mubi_pkg::mubi4_t     [top_${top["name"]}_pkg::NOutgoingLpgs${alert_group.capitalize()}-1:0]   outgoing_lpg_cg_en_${alert_group}_o,
% endif
% if lib.find_module(top["module"], "rstmgr", domain=domain):
  output prim_mubi_pkg::mubi4_t     [top_${top["name"]}_pkg::NOutgoingLpgs${alert_group.capitalize()}-1:0]   outgoing_lpg_rst_en_${alert_group}_o,
% endif

% endfor\

% if lib.find_module(top["module"], "alert_handler", domain=domain):
% for alert_group in top['incoming_alert'].keys():
  // Incoming alerts for group ${alert_group}
  input  prim_alert_pkg::alert_tx_t [top_${top["name"]}_pkg::NIncomingAlerts${alert_group.capitalize()}-1:0] incoming_alert_${alert_group}_tx_i,
  output prim_alert_pkg::alert_rx_t [top_${top["name"]}_pkg::NIncomingAlerts${alert_group.capitalize()}-1:0] incoming_alert_${alert_group}_rx_o,
  input  prim_mubi_pkg::mubi4_t     [top_${top["name"]}_pkg::NIncomingLpgs${alert_group.capitalize()}-1:0]   incoming_lpg_cg_en_${alert_group}_i,
  input  prim_mubi_pkg::mubi4_t     [top_${top["name"]}_pkg::NIncomingLpgs${alert_group.capitalize()}-1:0]   incoming_lpg_rst_en_${alert_group}_i,
% endfor
% endif\

<%
  clkmgr = lib.find_module(top['module'], 'clkmgr')
  rstmgr = lib.find_module(top['module'], 'rstmgr')
  domain_clkmgr = clkmgr.get('domain')
  ## The reset tree is driven by the rstmgr's primary partition.
  domain_rstmgr = rstmgr.get('domain')

  has_clkmgr = domain_clkmgr == domain
  clkmgr_parts = lib.get_clkmgr_partitions(top)
  rstmgr_parts = lib.get_rstmgr_partitions(top)
  has_rstmgr_section = domain_rstmgr != domain
  has_ext_clks = len(top['unmanaged_clocks']._asdict().values()) > 0
  has_ext_rsts = len(top['unmanaged_resets']._asdict().values()) > 0
  has_dft_section = not feature_info["dft_source_in_domain"][domain]

  ## Clocks sourced from an IP inside the top are wired as inter-module connections. Do not expose
  ## them as external clocks.
  ext_clk_ports = [clk for clk, sig in top['clocks'].typed_clocks().ast_clks.items()
                   if sig.src.module is None]

  ## Find out which section is the last one to properly terminate the port list with no comma.
  ## The rstmgr has always a section, so the clkmgr does not care.
  rstmgr_last = not (has_ext_clks or has_ext_rsts or has_dft_section)
  ext_clks_last = has_ext_clks and not (has_ext_rsts or has_dft_section)
  ext_rsts_last = has_ext_rsts and not has_dft_section
%>\
## Declare the ports of each clkmgr partition. In its own domain, these are its external clocks
## and the structs that leave the domain. In the other domain, these are the structs that enter.
% for part, dom, sfx, tinfix in clkmgr_parts:
<%
  who = f"the {part} partition of the clkmgr"
  part_ext_clks = [clk for clk in ext_clk_ports
                   if lib.get_clkmgr_clock_partition(top, top['clocks'].typed_clocks().ast_clks[clk].src) == part]
%>\
<%
  # Find whether this partition's clock and indication structs cross out of this domain or into it.
  # A struct of a split clkmgr only crosses into the power domains that need it.
  out_clk = lib.clkmgr_struct_crosses(top, 'clocks', part)
  out_cg = lib.clkmgr_struct_crosses(top, 'cg_en', part)
  in_clk = lib.clkmgr_struct_crosses(top, 'clocks', part, domain)
  in_cg = lib.clkmgr_struct_crosses(top, 'cg_en', part, domain)
%>\
  % if dom == domain:
    % if part_ext_clks:
  // Externally supplied clocks
      % for clk in part_ext_clks:
  input ${clk},
      % endfor
    % endif
    % if feature_info["ast_is_internal"] and (out_clk or out_cg):
  // Clocks from ${who} to other domains
      % if out_clk:
  output clkmgr_pkg::clkmgr_out${tinfix}_t    ${clkmgr['name']}_clocks${sfx}_o,
      % endif
      % if out_cg:
  output clkmgr_pkg::clkmgr_cg_en${tinfix}_t  ${clkmgr['name']}_cg_en${sfx}_o,
      % endif
    % endif
  % elif in_clk or in_cg:
  // Clocks from ${who} in power domain ${dom}
    % if in_clk:
  input clkmgr_pkg::clkmgr_out${tinfix}_t    ${clkmgr['name']}_clocks${sfx}_i,
    % endif
    % if in_cg:
  input clkmgr_pkg::clkmgr_cg_en${tinfix}_t  ${clkmgr['name']}_cg_en${sfx}_i,
    % endif
  % endif
% endfor

<%
  ## Find the rstmgr structs that cross, as for the clkmgr. The last struct ends the port list when
  ## the rstmgr section is the last section.
  rst_ports = [(part, kind) for part, dom, _, _ in rstmgr_parts for kind in ('resets', 'rst_en')
               if (dom != domain and lib.rstmgr_struct_crosses(top, kind, part, domain)) or
                  (dom == domain and feature_info["ast_is_internal"] and
                   lib.rstmgr_struct_crosses(top, kind, part))]
  last_rst_port = rst_ports[-1] if (rstmgr_last and rst_ports) else None
%>\
## Declare the struct ports of each rstmgr partition. They are outputs in the partition's domain,
## and inputs in the other domain.
% for part, dom, sfx, tinfix in rstmgr_parts:
<%
  who = f"the {part} partition of the rstmgr"
  kinds = [k for p, k in rst_ports if p == part]
  end = {k: "" if (part, k) == last_rst_port else "," for k in kinds}
  io = "o" if dom == domain else "i"
%>\
  % if kinds:
  // Resets from ${who} ${"to other domains" if dom == domain else f"in power domain {dom}"}
    % if 'resets' in kinds:
  ${"output" if dom == domain else "input"} rstmgr_pkg::rstmgr_out${tinfix}_t    ${rstmgr['name']}_resets${sfx}_${io}${end['resets']}
    % endif
    % if 'rst_en' in kinds:
  ${"output" if dom == domain else "input"} rstmgr_pkg::rstmgr_rst_en${tinfix}_t ${rstmgr['name']}_rst_en${sfx}_${io}${end['rst_en']}
    % endif
  % endif
% endfor

% if has_ext_clks:
  // Unmanaged external clocks
% for clk in top['unmanaged_clocks']._asdict().values():
  input                        ${clk.signal_name},
  input prim_mubi_pkg::mubi4_t ${clk.cg_en_signal}${"" if loop.last and ext_clks_last else ","}
% endfor

% endif\

% if has_ext_rsts:
  // Unmanaged external resets
  % for rst in top['unmanaged_resets']._asdict().values():
  input                        ${rst.signal_name},
  ## TODO: handle trailing comma properly
  input prim_mubi_pkg::mubi4_t ${rst.rst_en_signal_name}${"" if loop.last and ext_rsts_last else ","}
  % endfor
% endif\

## TODO: should we always expose scandmode_o and manually wire it up in the corresponding domain?
% if has_dft_section:
  // Manual DFT signals
  ## If the scansource is internal, we expose it via an external connection in the top.hjson file.
  input                        scan_rst_ni, // reset used for test mode
  % if feature_info["has_scan_en"][domain]:
  input                        scan_en_i,
  % endif
  input prim_mubi_pkg::mubi4_t scanmode_i   // lc_ctrl_pkg::On for Scan
% endif\
