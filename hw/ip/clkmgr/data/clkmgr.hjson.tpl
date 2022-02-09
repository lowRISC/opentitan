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
    { name: "NumSwGateableClocks",
      desc: "Number of SW gateable clocks",
      type: "int",
      default: "${len(typed_clocks.sw_clks)}",
      local: "true"
    },
    { name: "NumHintableClocks",
      desc: "Number of hintable clocks",
      type: "int",
      default: "${len(hint_names)}",
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
      name:    "lc_hw_debug_en",
      act:     "rcv",
      package: "lc_ctrl_pkg",
    },

    { struct:  "mubi4",
      type:    "uni",
      name:    "io_clk_byp_req",
      act:     "req",
      package: "prim_mubi_pkg",
    },

    { struct:  "mubi4",
      type:    "uni",
      name:    "io_clk_byp_ack",
      act:     "rcv",
      package: "prim_mubi_pkg",
    },

    { struct:  "mubi4",
      type:    "uni",
      name:    "all_clk_byp_req",
      act:     "req",
      package: "prim_mubi_pkg",
    },

    { struct:  "mubi4",
      type:    "uni",
      name:    "all_clk_byp_ack",
      act:     "rcv",
      package: "prim_mubi_pkg",
    },

    { struct:  "logic",
      type:    "uni",
      name:    "hi_speed_sel",
      act:     "req",
      package: "",
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

  countermeasures: [
    { name: "BUS.INTEGRITY",
      desc: "End-to-end bus integrity scheme."
    },
    { name: "TIMEOUT.CLK.BKGN_CHK",
      desc: "Background check for clock timeout."
    },
    { name: "MEAS.CLK.BKGN_CHK",
      desc: "Background check for clock frequency."
    },
    { name: "LC_CTRL.INTERSIG.MUBI",
      desc: "The life cycle control signals are multibit encoded."
    }
    { name: "LC_CTRL_CLK_HANDSHAKE.INTERSIG.MUBI",
      desc: "The life cycle clock req/ack signals are multibit encoded."
    }
    { name: "CLK_HANDSHAKE.INTERSIG.MUBI",
      desc: "The external clock req/ack signals are multibit encoded."
    }
    { name: "JITTER.CONFIG.MUBI",
      desc: "The jitter enable configuration is multibit encoded."
    }
    { name: "MEAS.CONFIG.REGWEN",
      desc: "The measurement controls protected with regwen."
    }
    { name: "CLK_CTRL.CONFIG.REGWEN",
      desc: "Software controlled clock requests are proteced with regwen."
    }

  ]

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
          mubi: true,
          desc: '''
            When the current value is not kMultiBitBool4True, writing a value of kMultiBitBool4True
            selects external clock as clock for the system.  Writing any other value has
            no impact.

            When the current value is kMultiBitBool4True, writing a value of kMultiBitBool4False
            selects internal clock as clock for the system. Writing any other value during this stage
            has no impact.

            While this register can always be programmed, it only takes effect when debug functions are enabled
            in life cycle TEST, DEV or RMA states.
          '''
          resval: "false"
        },
        {
          bits: "7:4",
          name: "LOW_SPEED_SEL",
          mubi: true,
          desc: '''
            A value of kMultiBitBool4True selects low speed external clocks.
            All other values selects nominal speed clocks.

            Note this field only has an effect when the !!EXTCLK_CTRL.SEL field is set to
            kMultiBitBool4True.
          '''
          resval: false
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
          mubi: true,
          bits: "3:0",
          name: "VAL",
          desc: '''
            Enable jittery clock.
            A value of kMultiBitBool4False disables the jittery clock,
            while all other values enable jittery clock.
          ''',
          resval: false
        }
      ]
    },

    { name: "CLK_ENABLES",
      desc: '''
        Clock enable for software gateable clocks.
        These clocks are directly controlled by software.
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
      // the CLK_ENABLE register cannot be written.
      // During top level randomized tests, it is possible to disable the clocks and then access
      // a register in the disabled block.  This would lead to a top level hang.
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
      // the CLK_HINT register cannot be written.
      // During top level randomized tests, it is possible to disable the clocks to transactional blocks
      // and then access a register in the disabled block.  This would lead to a top level hang.
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
  %>
    { name: "${src.upper()}_MEAS_CTRL_SHADOWED",
      desc: '''
        Configuration controls for ${src} measurement.

        The threshold fields are made wider than required (by 1 bit) to ensure
        there is room to adjust for measurement inaccuracies.
      ''',
      regwen: "MEASURE_CTRL_REGWEN",
      swaccess: "rw",
      hwaccess: "hro",
      async: "clk_${src}_i",
      shadowed: "true",
      update_err_alert: "recov_fault",
      storage_err_alert: "fatal_fault",
      fields: [
        {
          bits: "0",
          name: "EN",
          desc: "Enable measurement for ${src}",
          resval: "0",
          // Measurements can cause recoverable errors depending on the
          // thresholds which randomized CSR tests will not predict correctly.
          // To provide better CSR coverage we allow writing the threshold
          // fields, but not enabling the counters.
          tags: ["excl:CsrNonInitTests:CsrExclWrite"]
        },

        {
          bits: "${max_msb}:4",
          name: "HI",
          desc: "Max threshold for ${src} measurement",
          resval: "${ratio + 10}"
        },

        {
          bits: "${min_msb}:${max_msb+1}",
          name: "LO",
          desc: "Min threshold for ${src} measurement",
          resval: "${ratio - 10}"
        },
      ]
    },
% endfor

    { name: "RECOV_ERR_CODE",
      desc: "Recoverable Error code ",
      swaccess: "rw1c",
      hwaccess: "hwo",
      fields: [
% for src in typed_clocks.rg_srcs:
        {
          bits: "${loop.index}",
          name: "${src.upper()}_MEASURE_ERR",
          resval: 0,
          desc: '''
            ${src} has encountered a measurement error.
          '''
        },
% endfor
% for src in typed_clocks.rg_srcs:
        {
          bits: "${loop.index + len(typed_clocks.rg_srcs)}",
          name: "${src.upper()}_TIMEOUT_ERR",
          resval: 0,
          desc: '''
            ${src} has timed out.
          '''
        }
% endfor
% for src in typed_clocks.rg_srcs:
        {
          bits: "${loop.index + 2*len(typed_clocks.rg_srcs)}",
          name: "${src.upper()}_UPDATE_ERR",
          resval: 0,
          desc: '''
            !!${src.upper()}_MEASURE_CTRL_SHADOWED has an update error.
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
% for src in typed_clocks.rg_srcs:
        {
          bits: "${loop.index + 1}",
          name: "${src.upper()}_STORAGE_ERR",
          resval: 0,
          desc: '''
            !!${src.upper()}_MEASURE_CTRL_SHADOWED has a storage error.
          '''
        },
% endfor
      ]
    },
  ]
}
