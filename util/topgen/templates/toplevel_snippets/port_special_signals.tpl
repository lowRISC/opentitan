## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%page args="top, feature_info, cio_info"/>\
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

% if feature_info["has_ast"]:
  // All clocks forwarded to ast
  output clkmgr_pkg::clkmgr_out_t clks_ast_o,
  output rstmgr_pkg::rstmgr_out_t rsts_ast_o,

% endif\

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
