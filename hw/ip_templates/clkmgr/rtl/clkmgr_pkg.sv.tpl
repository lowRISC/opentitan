// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
<%
import textwrap
from collections import OrderedDict
num_hints = len(hint_names)
all_clocks = OrderedDict({clk: None for clk in typed_clocks['ft_clks'].keys()})
all_clocks.update({clk: None for clk in typed_clocks['hint_clks'].keys()})
all_clocks.update({clk: None for clk in typed_clocks['rg_clks'].keys()})
all_clocks.update({clk: None for clk in typed_clocks['sw_clks'].keys()})
from ipgen.manager_split import (clkmgr_out_clks, clkmgr_generated_clks, clkmgr_routed_nets,
                                 clkmgr_split_srcs)
# A partition generates the clocks of the sources that it receives. The secondary partition only
# buffers them, and the primary partition also gates them. The secondary partition outputs the
# clocks of the modules of the always-on power domain, and the primary partition those of every
# other module and of the rstmgr's primary partition. A clock from the other partition crosses the
# boundary once, inside the clkmgr (intraip_p2s or intraip_s2p).
primary_srcs, secondary_srcs = clkmgr_split_srcs(src_clks)
generated = {part: clkmgr_generated_clks(typed_clocks, src_clks, part) for part in ('primary', 'secondary')}
outputs = {part: clkmgr_out_clks(typed_clocks, part) for part in ('primary', 'secondary')}
p2s_nets = clkmgr_routed_nets(typed_clocks, src_clks, 'secondary')
for part in ('primary', 'secondary'):
  assert outputs[part], f"the {part} partition of the clkmgr outputs no clock"
%>\

package clkmgr_pkg;

  typedef enum int {
% for idx, hint_name in list(enumerate(hint_names.values())):
    ${hint_name} = ${idx}${"," if not loop.last else ""}
% endfor
  } hint_names_e;

  // Clocks broadcast. Each partition outputs the clocks of the modules on its side.
% for part, clks in outputs.items():
  typedef struct packed {
  % for clk in clks:
    logic ${clk};
  % endfor
  } clkmgr_out_${part}_t;

% endfor
  // Clock gating indications for the alert handlers. The primary partition outputs all of them.
  // The secondary partition's indications cross to it in intraip_s2p.
  typedef struct packed {
% for clk in [c for c in all_clocks if c in generated['primary'] or c in generated['secondary']]:
    prim_mubi_pkg::mubi4_t ${clk.split('clk_')[-1]};
% endfor
  } clkmgr_cg_en_primary_t;

  parameter int NumOutputClk = ${len(all_clocks)};

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

  // Signalling between the two partitions of the split clock manager.
  // Secondary (always-on clocks) to primary
  typedef struct packed {
    // The scan mode, which enters the secondary partition only.
    prim_mubi_pkg::mubi4_t scanmode;
    // The always-on root clocks, which the secondary partition buffers once. The always-on clock is
    // gated. It runs only while the power domain of the primary partition has power and its
    // isolation is off.
% for src in secondary_srcs:
    logic clk_${src['name']};
% endfor
    // The clock gating indications of the clocks that the secondary partition generates and the
    // primary partition does not buffer itself. The primary partition outputs all the indications,
    // and drives those of the clocks that it buffers too.
% for clk in [c for c in generated['secondary'] if c not in outputs['primary']]:
    prim_mubi_pkg::mubi4_t cg_en_${clk.split('clk_')[-1]};
% endfor
    // The clock enable requests come from the power manager, which is in the power domain of the
    // secondary partition.
% for root in parent_child_clks:
    logic ${root}_ip_clk_en;
% endfor
  } intraip_s2p_t;

  // Primary to secondary
  typedef struct packed {
% for net, info in p2s_nets.items():
  % for line in textwrap.wrap('used in the power domain of the secondary as ' + ', '.join(info['clocks']), width=93):
    // ${line}
  % endfor
    logic ${net};
% endfor
    // The clock status responses go to the power manager.
% for root in parent_child_clks:
    logic ${root}_status;
% endfor
  } intraip_p2s_t;

endpackage // clkmgr_pkg
