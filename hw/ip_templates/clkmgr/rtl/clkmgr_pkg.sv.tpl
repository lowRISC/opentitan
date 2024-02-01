// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%
from collections import OrderedDict
num_hints = len(hint_names)
all_clocks = OrderedDict({clk: None for clk in typed_clocks['ft_clks'].keys()})
all_clocks.update({clk: None for clk in typed_clocks['hint_clks'].keys()})
all_clocks.update({clk: None for clk in typed_clocks['rg_clks'].keys()})
all_clocks.update({clk: None for clk in typed_clocks['sw_clks'].keys()})
%>

package clkmgr_pkg;

  typedef enum int {
% for idx, hint_name in list(enumerate(hint_names.values())):
    ${hint_name} = ${idx}${"," if not loop.last else ""}
% endfor
  } hint_names_e;

  // clocks generated and broadcast
  typedef struct packed {
% for clk in all_clocks.keys():
    logic ${clk};
% endfor
  } clkmgr_out_t;

  // clock gating indication for alert handler
  typedef struct packed {
<% n_clk = 0 %>\
% for clk in all_clocks.keys():
    prim_mubi_pkg::mubi4_t ${clk.split('clk_')[-1]};<% n_clk += 1 %>
% endfor
  } clkmgr_cg_en_t;

  parameter int NumOutputClk = ${n_clk};

% for intf, eps in exported_clks.items():
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
