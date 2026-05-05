## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%from topgen.merge import alert_handler_signals%>\
<%page args="top, feature_info, cio_info, domain"/>\
% if feature_info["has_pinmux"]:
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
  % for pd in top["power"]["physical"]:
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

  // All externally supplied clocks
% for clk in top['clocks'].typed_clocks().ast_clks:
  input ${clk},
% endfor\

% for alert_group in top['outgoing_alert'].keys():
  // Outgoing alerts for group ${alert_group}
  output prim_alert_pkg::alert_tx_t [top_${top["name"]}_pkg::NOutgoingAlerts${alert_group.capitalize()}-1:0] outgoing_alert_${alert_group}_tx_o,
  input  prim_alert_pkg::alert_rx_t [top_${top["name"]}_pkg::NOutgoingAlerts${alert_group.capitalize()}-1:0] outgoing_alert_${alert_group}_rx_i,
  output prim_mubi_pkg::mubi4_t     [top_${top["name"]}_pkg::NOutgoingLpgs${alert_group.capitalize()}-1:0]   outgoing_lpg_cg_en_${alert_group}_o,
  output prim_mubi_pkg::mubi4_t     [top_${top["name"]}_pkg::NOutgoingLpgs${alert_group.capitalize()}-1:0]   outgoing_lpg_rst_en_${alert_group}_o,
% endfor\

% for alert_group in top['incoming_alert'].keys():
  // Incoming alerts for group ${alert_group}
  input  prim_alert_pkg::alert_tx_t [top_${top["name"]}_pkg::NIncomingAlerts${alert_group.capitalize()}-1:0] incoming_alert_${alert_group}_tx_i,
  output prim_alert_pkg::alert_rx_t [top_${top["name"]}_pkg::NIncomingAlerts${alert_group.capitalize()}-1:0] incoming_alert_${alert_group}_rx_o,
  input  prim_mubi_pkg::mubi4_t     [top_${top["name"]}_pkg::NIncomingLpgs${alert_group.capitalize()}-1:0]   incoming_lpg_cg_en_${alert_group}_i,
  input  prim_mubi_pkg::mubi4_t     [top_${top["name"]}_pkg::NIncomingLpgs${alert_group.capitalize()}-1:0]   incoming_lpg_rst_en_${alert_group}_i,
% endfor

<%
  clkmgr = lib.find_module(top['module'], 'clkmgr')
  domain_clkmgr = clkmgr.get('domain')
%>\
% if domain_clkmgr == domain:
  // Externally supplied clocks
  % for clk in top['clocks'].typed_clocks().ast_clks:
  input ${clk},
  % endfor
% else:
  input clkmgr_pkg::clkmgr_out_t    ${clkmgr['name']}_clocks_i,
  input clkmgr_pkg::clkmgr_cg_en_t  ${clkmgr['name']}_cg_en_i,
% endif

% if len(top['unmanaged_clocks']._asdict().values()) > 0:
  // Unmanaged external clocks
% for clk in top['unmanaged_clocks']._asdict().values():
  input                        ${clk.signal_name},
  input prim_mubi_pkg::mubi4_t ${clk.cg_en_signal},
% endfor

% endif\

% if len(top['unmanaged_resets']._asdict().values()) > 0:
  // Unmanaged external resets
  % for rst in top['unmanaged_resets']._asdict().values():
  input                        ${rst.signal_name},
  input prim_mubi_pkg::mubi4_t ${rst.rst_en_signal_name},
  % endfor

% endif\

  input                      scan_rst_ni, // reset used for test mode
% if feature_info["has_scan_en"]:
  input                      scan_en_i,
% endif
  input prim_mubi_pkg::mubi4_t scanmode_i   // lc_ctrl_pkg::On for Scan
