// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// TODO: This module is only a draft implementation that covers most of the clkmgr
// functionality but is incomplete

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
  scan: "true",
  clock_primary: "clk_i",
  other_clock_list: [],
  reset_primary: "rst_ni",
  other_reset_list: [
% for src in srcs:
    % if src['aon'] == 'no':
    "rst_${src['name']}_ni"
    % endif
% endfor
% for src in div_srcs:
    "rst_${src['name']}_ni"
% endfor
  ]
  bus_interfaces: [
    { protocol: "tlul", direction: "device" }
  ],
  alert_list: [
    { name: "fatal_fault",
      desc: '''
      This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected.
      '''
    }
  ],
  regwidth: "32",
  param_list: [
    { name: "NumGroups",
      desc: "Number of clock groups",
      type: "int",
      default: "${num_grps}",
      local: "true"
    },
  ],

  inter_signal_list: [
    { struct:  "clkmgr_out",
      type:    "uni",
      name:    "clocks",
      act:     "req",
      package: "clkmgr_pkg",
    },

    { struct:  "lc_tx",
      type:    "uni",
      name:    "lc_dft_en",
      act:     "rcv",
      package: "lc_ctrl_pkg",
    },

    { struct:  "lc_tx",
      type:    "uni",
      name:    "ast_clk_byp_req",
      act:     "req",
      package: "lc_ctrl_pkg",
    },

    { struct:  "lc_tx",
      type:    "uni",
      name:    "ast_clk_byp_ack",
      act:     "rcv",
      package: "lc_ctrl_pkg",
    },

    { struct:  "lc_tx",
      type:    "uni",
      name:    "lc_clk_byp_req",
      act:     "rcv",
      package: "lc_ctrl_pkg",
    },

    { struct:  "lc_tx",
      type:    "uni",
      name:    "lc_clk_byp_ack",
      act:     "req",
      package: "lc_ctrl_pkg",
    },

    { struct:  "logic",
      type:    "uni",
      name:    "jitter_en",
      act:     "req",
      package: ""
    },

  // All clock inputs
% for src in srcs:
    { struct:  "logic",
      type:    "uni",
      name:    "clk_${src['name']}",
      act:     "rcv",
      package: "",
    },
% endfor

  // Exported clocks
% for intf in export_clks:
    { struct:  "clkmgr_${intf}_out",
      type:    "uni",
      name:    "clocks_${intf}",
      act:     "req",
      package: "clkmgr_pkg",
    },
% endfor

    { struct:  "pwr_clk",
      type:    "req_rsp",
      name:    "pwr",
      act:     "rsp",
    },

    { struct:  "logic",
      type:    "uni",
      name:    "idle",
      act:     "rcv",
      package: "",
      width:   "${len(hint_clks)}"
    },
  ],


  registers: [
    { name: "EXTCLK_SEL_REGWEN",
      desc: "External clock select write enable",
      swaccess: "rw0c",
      hwaccess: "none",
      fields: [
        { bits: "0",
          name: "EN",
          resval: "1"
          desc: '''
            When 1, the value of !!EXTCLK_SEL can be set.  When 0, writes to !!EXTCLK_SEL have no
            effect.
          '''
        },
      ]
    },

    { name: "EXTCLK_SEL",
      desc: '''
        Select external clock
      ''',
      regwen: "EXTCLK_SEL_REGWEN",
      swaccess: "rw",
      hwaccess: "hro",
      fields: [
        {
          bits: "3:0",
          name: "VAL",
          desc: '''
            A value of b1010 selects external clock as clock for the system.
            While this register can always be programmed, it only takes effect when the system is in
            life cycle TEST or RMA states when DFT is enabled.

            All other values are invalid and keep clocks on internal sources.
          '''
          resval: "0x5"
        }
      ]
    },

    { name: "JITTER_ENABLE",
      desc: '''
        Enable jittery clock
      ''',
      swaccess: "rw",
      hwaccess: "hro",
      fields: [
        {
          bits: "0",
          name: "VAL",
          desc: "Enable jittery clock"
          resval: "0"
        }
      ]
    },

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
      // the CLK_ENABLE register cannot be written, otherwise there is the potential clocks could be
      // disabled and the system will hang
      tags: ["excl:CsrAllTests:CsrExclAll"]
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
      // the CLK_HINT register cannot be written, otherwise there is the potential clocks could be
      // disabled and the system will hang
      tags: ["excl:CsrAllTests:CsrExclAll"]
    },

    { name: "CLK_HINTS_STATUS",
      desc: '''
        Since the final state of !!CLK_HINTS is not always determined by software,
        this register provides read feedback for the current clock state.

      ''',
      swaccess: "ro",
      hwaccess: "hwo",
      fields: [
% for clk in hint_clks.keys():
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
