// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Secondary partition of the split clock manager.
//
// The secondary partition hosts only the always-on clocks, with their root buffers and the
// feed-through buffers of the typed clocks that come from them. It never gates them for the
// always-on power domain. It gates only the copy that it gives the primary partition, around the
// clamp of the power domain of the primary partition. It has no registers and no state, and the
// always-on clocks keep running while the power domain of the primary partition is down.
//
// The always-on source clocks and their resets enter the block here.

<%
from ipgen.manager_split import (clkmgr_out_clks, clkmgr_routed_nets, clkmgr_secondary_ft_clks,
                                 clkmgr_split_srcs)
primary_srcs, secondary_srcs = clkmgr_split_srcs(src_clks)
secondary_ft_clks = clkmgr_secondary_ft_clks(typed_clocks, src_clks)
# This partition outputs the clocks of the modules of the always-on power domain. They are the
# clocks of its own sources, and the clocks that the primary partition generates for them, through
# intraip_p2s.
out_clks = clkmgr_out_clks(typed_clocks, 'secondary')
primary_out_clks = clkmgr_out_clks(typed_clocks, 'primary')
from_primary_nets = clkmgr_routed_nets(typed_clocks, src_clks, 'secondary')
%>\
`include "prim_assert.sv"

module clkmgr_part_secondary
  import clkmgr_pkg::*;
  import prim_mubi_pkg::mubi4_t;
(
  // Source clocks of this partition, and their resets
% for src in secondary_srcs:
  input clk_${src['name']}_i,
  input rst_${src['name']}_ni,
% endfor

  // Power manager interface. The power manager is in the power domain of this partition.
  input pwrmgr_pkg::pwr_clk_req_t pwr_i,
  output pwrmgr_pkg::pwr_clk_rsp_t pwr_o,
  // The always-on clock may enter the power domain of the primary partition.
  input main_pd_aon_clk_en_i,
  // The scan mode. It enters this partition only, and goes on to the primary partition in
  // intraip_s2p_o.
  input prim_mubi_pkg::mubi4_t scanmode_i,


  // clock output interface
  output clkmgr_out_secondary_t clocks_secondary_o,

  // inter-partition signalling
  output intraip_s2p_t intraip_s2p_o,
  input intraip_p2s_t intraip_p2s_i
);

  import prim_mubi_pkg::MuBi4False;

  // The scan mode goes on to the primary partition.
  assign intraip_s2p_o.scanmode = scanmode_i;

  // The primary partition uses the power manager's requests and answers them.
% for root in parent_child_clks:
  assign intraip_s2p_o.${root}_ip_clk_en = pwr_i.${root}_ip_clk_en;
  assign pwr_o.${root}_status = intraip_p2s_i.${root}_status;
% endfor

  // Hookup point for OCC's on root clocks.
% for src in secondary_srcs:
  logic clk_${src['name']};
  prim_clock_buf #(
    .NoFpgaBuf(1'b1)
  ) u_clk_${src['name']}_buf (
    .clk_i(clk_${src['name']}_i),
    .clk_o(clk_${src['name']})
  );

  // The primary partition takes the buffered clock of this source from here. Each source clock
  // comes with its reset, as the clocking of the IP declares them in pairs. The assertions below
  // use the reset of the first source, and no other logic here uses these resets. The primary
  // partition has its own ports for them, for the clock measurement.
% if src['name'] == 'aon':
  // This gate controls the always-on clock of the primary partition. The clock runs only while the
  // power domain of the primary partition has power and its isolation is off. The power manager
  // opens the gate before it releases the clamp, and closes the gate before the clamp asserts. Thus
  // the gate is open while any clock or reset of that domain is active. The slow FSM's terminal
  // state is the one exception. There the gate closes in the same cycle as the clamp. The enable
  // changes on this clock. Thus the primary partition and its modules see a continuous clock.
  // TODO(#32351): test_en_i is tied off. A follow-up connects it to the scan mode, which this
  // partition receives.
  prim_clock_gating #(
    .NoFpgaGate(1'b1)
  ) u_clk_aon_main_pd_cg (
    .clk_i(clk_aon),
    .en_i(main_pd_aon_clk_en_i),
    .test_en_i(1'b0),
    .clk_o(intraip_s2p_o.clk_aon)
  );
% else:
  assign intraip_s2p_o.clk_${src['name']} = clk_${src['name']};
% endif
  logic unused_rst_${src['name']}_ni;
  assign unused_rst_${src['name']}_ni = rst_${src['name']}_ni;
% endfor

  ////////////////////////////////////////////////////
  // Feed-through clocks sourced from the always-on clocks
  ////////////////////////////////////////////////////
% for k, v in secondary_ft_clks.items():
  % if k in out_clks:
  prim_clock_buf u_${k}_buf (
    .clk_i(clk_${v['src_name']}),
    .clk_o(clocks_secondary_o.${k})
  );

  % endif
  // clock gated indication for alert handler: these clocks are never gated.
  % if k not in primary_out_clks:
  // The primary partition outputs the clock gating indication. A feed-through clock is never gated,
  // so the indication is MuBi4False.
  assign intraip_s2p_o.cg_en_${k.split('clk_')[-1]} = MuBi4False;
  % endif
% endfor

  ////////////////////////////////////////////////////
  // Clocks the primary partition generates for this power domain
  ////////////////////////////////////////////////////
% for net, info in from_primary_nets.items():
  % for k in info['clocks']:
    % if info['kind'] == 'ft':
  prim_clock_buf u_${k}_buf (
    .clk_i(intraip_p2s_i.${net}),
    .clk_o(clocks_secondary_o.${k})
  );
    % else:
  assign clocks_secondary_o.${k} = intraip_p2s_i.${net};
    % endif
  % endfor
% endfor

  ////////////////////////////////////////////////////
  // Assertions
  ////////////////////////////////////////////////////
  // The secondary partition has no clk_i or rst_ni. Its assertions use the clock and reset of its
  // first source.
<% clk, rst = f"clk_{secondary_srcs[0]['name']}_i", f"!rst_{secondary_srcs[0]['name']}_ni" %>\
  `ASSERT_KNOWN(ClocksKownO_A, clocks_secondary_o, ${clk}, ${rst})
  `ASSERT_KNOWN(PwrMgrKnownO_A, pwr_o, ${clk}, ${rst})
  `ASSERT_KNOWN(IntraipKnownO_A, intraip_s2p_o, ${clk}, ${rst})
endmodule // clkmgr_part_secondary
