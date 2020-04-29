// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// TODO: This module is only a draft implementation that covers most of the rstmgr
// functoinality but is incomplete

<%
clks_attr = cfg['clocks']
srcs = clks_attr['srcs']
grps = clks_attr['groups']
num_grps = len(grps)
%>

# CLKMGR register template
#
{
  name: "CLKMGR",
  clock_primary: "clk_i",
  other_clock_list: [
% for src in srcs:
    "clk_${src['name']}_i",
% endfor
  ],
  bus_device: "tlul",
  regwidth: "32",
  param_list: [
    { name: "NumGroups",
      desc: "Number of clock groups",
      type: "int",
      default: "${num_grps}",
      local: "true"
    },
  ],

  // Define rstmgr struct package
  inter_signal_list: [
    { struct:  "clkmgr_out",
      type:    "uni",
      name:    "clocks",
      act:     "req",
      package: "clkmgr_pkg",
    },

    { struct:  "clk_dft",
      type:    "uni",
      name:    "dft",
      act:     "rcv",
      package: "clkmgr_pkg", // This should be moved elsewhere later
    },

    { struct:  "clk_hint_status",
      type:    "uni",
      name:    "status",
      act:     "rcv",
      package: "clkmgr_pkg",
    },
  ],


  registers: [
    { name: "CLK_ENABLES",
      desc: '''
        Clock enable for software gateable clocks.
        These clocks are direclty controlled by software.
      ''',
      swaccess: "rw",
      hwaccess: "hro",
      fields: [
% for clk in sw_clks:
        {
          bits: "${loop.index}",
          name: "${clk.upper()}_EN",
          resval: 1,
          desc: '''
            0 ${clk.upper()} is disabled.
            1 ${clk.upper()} is enabled.
          '''
        }
% endfor
      ]
    },

    { name: "CLK_HINTS",
      desc: '''
        Clock hint for software gateable clocks.
        These clocks are not fully controlled by software.

        For disable, software only provides a hint, and hardware determines the final clock state based on the
        hint and whether the block in question is idle.

      ''',
      swaccess: "rw",
      hwaccess: "hro",
      fields: [
% for clk in hint_clks:
        {
          bits: "${loop.index}",
          name: "${clk.upper()}_HINT",
          resval: 1,
          desc: '''
            0 ${clk.upper()} can be disabled.
            1 ${clk.upper()} is enabled.
          '''
        }
% endfor
      ]
    },

    { name: "CLK_HINTS_STATUS",
      desc: '''
        Since the final state of !!CLK_HINTS is not always determined by software,
        this register provides read feedback for the current clock state.

      ''',
      swaccess: "ro",
      hwaccess: "hwo",
      fields: [
% for clk in hint_clks:
        {
          bits: "${loop.index}",
          name: "${clk.upper()}_VAL",
          resval: 1,
          desc: '''
            0 ${clk.upper()} is disabled.
            1 ${clk.upper()} is enabled.
          '''
        }
% endfor
      ]
    },
  ]
}
