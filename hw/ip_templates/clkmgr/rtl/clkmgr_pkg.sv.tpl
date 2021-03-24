// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%
from collections import OrderedDict

clks_attr = cfg['clocks']
grps = clks_attr['groups']
num_hints = len(hint_clks)
%>

package clkmgr_pkg;

  typedef enum int {
% for hint, v in hint_clks.items():
    ${v['name'].capitalize()} = ${loop.index}${"," if not loop.last else ""}
% endfor
  } hint_names_e;

  typedef struct packed {
<%
# Merge Clock Dicts together
all_clocks = OrderedDict()
all_clocks.update(ft_clks)
all_clocks.update(hint_clks)
all_clocks.update(rg_clks)
all_clocks.update(sw_clks)
%>\
% for clk in all_clocks:
  logic ${clk};
% endfor

  } clkmgr_out_t;

% for intf, eps in export_clks.items():
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
