// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

# CLKMGR register template
#
{
  name: "CLKMGR",
  scan: "true",
  clocking: [
    {clock: "clk_i", reset: "rst_ni", primary: true},
% for src in clocks.srcs.values():
    {clock: "clk_${src.name}_i", reset: "rst_${src.name}_ni"},
% endfor
% for src in clocks.derived_srcs.values():
    {clock: "clk_${src.name}_i", reset: "rst_${src.name}_ni", internal: true},
% endfor
  ]
  bus_interfaces: [
    { protocol: "tlul", direction: "device" }
  ],
  alert_list: [
    { name: "recov_fault",
      desc: '''
      This recoverable alert is triggered when there are measurement errors.
      '''
    }
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
      default: "${len(clocks.groups)}",
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

    { struct:  "clkmgr_cg_en",
      type:    "uni",
      name:    "cg_en",
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

  // Exported clocks
% for intf in cfg['exported_clks']:
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
      width:   "${len(hint_names)}"
    },
  ],


  registers: [
    { name: "EXTCLK_CTRL_REGWEN",
      desc: "External clock control write enable",
      swaccess: "rw0c",
      hwaccess: "none",
      fields: [
        { bits: "0",
          name: "EN",
          resval: "1"
          desc: '''
            When 1, the value of !!EXTCLK_CTRL can be set.  When 0, writes to !!EXTCLK_CTRL have no
            effect.
          '''
        },
      ]
    },

    { name: "EXTCLK_CTRL",
      desc: '''
        Select external clock
      ''',
      regwen: "EXTCLK_CTRL_REGWEN",
      swaccess: "rw",
      hwaccess: "hro",
      fields: [
        {
          bits: "3:0",
          name: "SEL",
          desc: '''
            A value of b1010 selects external clock as clock for the system.
            While this register can always be programmed, it only takes effect when the system is in
            life cycle TEST or RMA states when DFT is enabled.

            All other values are invalid and keep clocks on internal sources.
          '''
          resval: "0x5"
        },
        {
          bits: "7:4",
          name: "STEP_DOWN",
          desc: '''
            A value of b1010 steps down the clock dividers by a factor of 2 if the !!EXTCLK_CTRL.SEL
            field is also set to b1010.

            All other values have no effect.
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
% for clk in typed_clocks.sw_clks:
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
        Clock hint for software gateable transactional clocks during active mode.
        During low power mode, all clocks are gated off regardless of the software hint.

        Transactional clocks are not fully controlled by software.  Instead software provides only a disable hint.

        When software provides a disable hint, the clock manager checks to see if the associated hardware block is idle.
        If the hardware block is idle, then the clock is disabled.
        If the hardware block is not idle, the clock is kept on.

        For the enable case, the software hint is immediately honored and the clock turned on.  Hardware does not provide any
        feedback in this case.
      ''',
      swaccess: "rw",
      hwaccess: "hro",
      fields: [
% for clk in hint_names.keys():
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
% for clk in hint_names.keys():
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

    { name: "MEASURE_CTRL_REGWEN",
      desc: "Measurement control write enable",
      swaccess: "rw0c",
      hwaccess: "none",
      fields: [
        { bits: "0",
          name: "EN",
          resval: "1"
          desc: '''
            When 1, the value of the measurement control can be set.  When 0, writes have no
            effect.
          '''
        },
      ]
    },

<% aon_freq = clocks.all_srcs['aon'].freq %>\
% for src in typed_clocks.rg_srcs:
  <%
    freq = clocks.all_srcs[src].freq
    ratio = int(freq / aon_freq)
    # Add extra bit to width for margin
    width = ratio.bit_length() + 1
    max_msb = 4 + width - 1
    min_msb = (max_msb + 1) + width - 1
  %>\
    { name: "${src.upper()}_MEASURE_CTRL",
      desc: '''
        Configuration controls for ${src} measurement.

        The threshold fields are made wider than required (by 1 bit) to ensure
        there is room to adjust for measurement inaccuracies.
      ''',
      regwen: "MEASURE_CTRL_REGWEN",
      swaccess: "rw",
      hwaccess: "hro",
      fields: [
        {
          bits: "0",
          name: "EN",
          desc: "Enable measurement for ${src}",
          resval: "0"
        },

        {
          bits: "${max_msb}:4",
          name: "MAX_THRESH",
          desc: "Max threshold for ${src} measurement",
          resval: "${ratio + 10}",
          // random updates to this field if measurements are turned on can
          // cause the results to fail
          tags: ["excl:CsrNonInitTests:CsrExclWrite"]
        },

        {
          bits: "${min_msb}:${max_msb+1}",
          name: "MIN_THRESH",
          desc: "Min threshold for ${src} measurement",
          resval: "${ratio - 10}",
          // random updates to this field if measurements are turned on can
          // cause the results to fail
          tags: ["excl:CsrNonInitTests:CsrExclWrite"]
        },
      ]
    },
% endfor

    { name: "RECOV_ERR_CODE",
      desc: "Recoverable Error code ",
      swaccess: "rw1c",
      hwaccess: "hrw",
      fields: [
% for src in typed_clocks.rg_srcs:
        {
          bits: "${loop.index}",
          name: "${src.upper()}_MEASURE_ERR",
          resval: 0,
          desc: '''
            ${src} has encountered a measurement error.
          '''
        }
% endfor
      ]
    },

    { name: "FATAL_ERR_CODE",
      desc: "Error code ",
      swaccess: "ro",
      hwaccess: "hrw",
      fields: [
        { bits: "0",
          name: "REG_INTG",
          resval: 0
          desc: '''
            Register file has experienced a fatal integrity error.
          '''
        },
      ]
    },
  ]
}
