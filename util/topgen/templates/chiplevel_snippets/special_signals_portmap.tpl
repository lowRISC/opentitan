## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%from topgen.merge import alert_handler_signals%>\
<%page args="top, feature_info, cio_info, gen_bkdr_loader"/>\
% if not feature_info["ast_is_internal"]:
    // Base clocks from AST
    .ast_base_clks_i(ast_base_clks),

% endif\

% if len(top['unmanaged_clocks']._asdict().values()) > 0:
    // Unmanaged external clocks
  % for clk in top['unmanaged_clocks']._asdict().values():
    .${clk.signal_name}  (${clk.signal_name[:-2]}),
    .${clk.cg_en_signal}(${clk.cg_en_signal[:-2]}),
  % endfor

% endif\

% if len(top['unmanaged_resets']._asdict().values()) > 0:
    // Unmanaged external resets
  % for rst in top['unmanaged_resets']._asdict().values():
    .${rst.signal_name}   (${rst.signal_name[:-2]}),
    .${rst.rst_en_signal_name}(${rst.rst_en_signal_name[:-2]}),
  % endfor

% endif\

    // Manual DFT signals
% if feature_info["ast_is_internal"]:
    .padring_scan_clk_o(padring_scan_clk),
% else:
    .scan_rst_ni(scan_rst_n),
  % for domain in feature_info["has_scan_en"]:
  % if feature_info["has_scan_en"][domain]:
    .scan_en_i  (scan_en   ),
<% continue %>
  % endif
  % endfor
    .scanmode_i (scanmode  ),
% endif

% if feature_info["has_pinmux"]:
% if cio_info["num_mio_pads"] != 0:
% if gen_bkdr_loader:
    // Multiplexed I/O to backdoor
    .mio_in_i (mio_bkdr_in ),
    .mio_out_o(mio_bkdr_out),
    .mio_oe_o (mio_bkdr_oe ),
% else:
    // Multiplexed I/O
    .mio_in_i (mio_in ),
    .mio_out_o(mio_out),
    .mio_oe_o (mio_oe ),
% endif

% endif
% if cio_info["num_dio_total"] != 0:
    // Dedicated I/O
    .dio_in_i (dio_in ),
    .dio_out_o(dio_out),
    .dio_oe_o (dio_oe ),

% endif
    // Pad attributes
% if gen_bkdr_loader:
    .mio_attr_o(mio_bkdr_attr),
% else:
    .mio_attr_o(mio_attr),
% endif
    .dio_attr_o(dio_attr),

% endif\
