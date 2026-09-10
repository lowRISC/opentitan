## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%from topgen.merge import alert_handler_signals%>\
<%page args="top, feature_info, cio_info"/>\
<%
  clkmgr = lib.find_module(top['module'], 'clkmgr')
  rstmgr = lib.find_module(top['module'], 'rstmgr')
%>\
  // Base clocks from AST
  input ast_pkg::ast_clks_t ast_base_clks_i,

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

  // Manual DFT signals
  input                        scan_rst_ni, // reset used for test mode
  input                        scan_en_i,
  input prim_mubi_pkg::mubi4_t scanmode_i,  // lc_ctrl_pkg::On for Scan

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
