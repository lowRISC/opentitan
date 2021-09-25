// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
${autogen_banner}

<%
num_hints = len(typed_clocks.hint_clks)
%>\
package clkmgr_pkg;

  typedef enum int {
% for idx, hint_name in list(enumerate(hint_names.values())):
    ${hint_name} = ${idx}${"," if not loop.last else ""}
% endfor
  } hint_names_e;

  typedef struct packed {
% for clk in typed_clocks.all_clocks():
    logic ${clk};
% endfor

  } clkmgr_out_t;

% for intf, eps in cfg['exported_clks'].items():
  typedef struct packed {
  % for ep, clks in eps.items():
    % for clk in clks:
    logic clk_${intf}_${ep}_${clk};
    % endfor
  % endfor
  } clkmgr_${intf}_out_t;
% endfor

  typedef struct packed {
    logic [${num_hints}-1:0] idle;
  } clk_hint_status_t;

  parameter clk_hint_status_t CLK_HINT_STATUS_DEFAULT = '{
    idle: {${num_hints}{1'b1}}
  };

endpackage // clkmgr_pkg
