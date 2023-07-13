// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

# CLKMGR register template
#
{
  name:               "clkmgr",
  human_name:         "Clock Manager",
  one_line_desc:      "Derives and monitors on-chip clock signals, handles clock gating requests from power manager and software",
  one_paragraph_desc: '''
  Clock Manager derives on-chip clocks from root clock signals provided by Analog Sensor Top (AST).
  Input and output clocks may be asynchronous to each other.
  During clock derivation, Clock Manager can divide clocks to lower frequencies and gate clocks based on control signals from the power manager and to a limited extent from software.
  For example, the idle status of relevant hardware blocks is tracked and clock gating requests from software are ignored as long as these blocks are active.
  Further security features include switchable clock jitter, continuous monitoring of clock frequencies, and various countermeasures to deter fault injection (FI) attacks.
  '''
  // Unique comportable IP identifier defined under KNOWN_CIP_IDS in the regtool.
  cip_id:             "4",
  design_spec:        "../doc",
  dv_doc:             "../doc/dv",
  hw_checklist:       "../doc/checklist",
  sw_checklist:       "/sw/device/lib/dif/dif_clkmgr",
  revisions: [
    {
      version:            "2.0.0",
      life_stage:         "L1",
      design_stage:       "D2S",
      verification_stage: "V2S",
      dif_stage:          "S2",
    }
  ]
  scan: "true",
  clocking: [
    {clock: "clk_i", reset: "rst_ni", primary: true},
    {reset: "rst_root_ni"},
% for src in clocks.srcs.values():
    {clock: "clk_${src.name}_i", reset: "rst_${src.name}_ni"},
% endfor
% for src in clocks.derived_srcs.values():
    {clock: "clk_${src.name}_i", reset: "rst_${src.name}_ni", internal: true},
% endfor
% for root, clk_family in typed_clocks.parent_child_clks.items():
  % for clk in clk_family:
    {reset: "rst_root_${clk}_ni"},
  % endfor
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

    { struct:  "mubi4",
      type:    "uni",
      name:    "hi_speed_sel",
      act:     "req",
      package: "prim_mubi_pkg",
    },

    { struct:  "mubi4",
      type:    "uni",
      name:    "div_step_down_req",
      act:     "rcv",
      package: "prim_mubi_pkg",
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

    { struct:  "mubi4",
      type:    "uni",
      name:    "jitter_en",
      act:     "req",
      package: "prim_mubi_pkg"
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

    { struct:  "mubi4",
      type:    "uni",
      name:    "idle",
      act:     "rcv",
      package: "prim_mubi_pkg",
      width:   "${len(hint_names)}"
    },

    { struct:  "mubi4",
      desc:    "Indicates clocks are calibrated and frequencies accurate",
      type:    "uni",
      name:    "calib_rdy",
      act:     "rcv",
      package: "prim_mubi_pkg",
      default: "prim_mubi_pkg::MuBi4True"
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
    { name: "MEAS.CONFIG.SHADOW",
      desc: "Measurement configurations are shadowed."
    }
    { name: "IDLE.INTERSIG.MUBI",
      desc: "Idle inputs are multibit encoded."
    }
    { name: "LC_CTRL.INTERSIG.MUBI",
      desc: "The life cycle control signals are multibit encoded."
    }
    { name: "LC_CTRL_CLK_HANDSHAKE.INTERSIG.MUBI",
      desc: "The life cycle clock req/ack signals are multibit encoded."
    }
    { name: "CLK_HANDSHAKE.INTERSIG.MUBI",
      desc: "The external clock req/ack signals are multibit encoded."
    }
    { name: "DIV.INTERSIG.MUBI",
      desc: "Divider step down request is multibit encoded."
    }
    { name: "JITTER.CONFIG.MUBI",
      desc: "The jitter enable configuration is multibit encoded."
    }
    { name: "IDLE.CTR.REDUN",
      desc: "Idle counter is duplicated."
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
          name: "HI_SPEED_SEL",
          mubi: true,
          desc: '''
            A value of kMultiBitBool4True selects nominal speed external clock.
            All other values selects low speed clocks.

            Note this field only has an effect when the !!EXTCLK_CTRL.SEL field is set to
            kMultiBitBool4True.

            Nominal speed means the external clock is approximately the same frequency as
            the internal oscillator source.  When this option is used, all clocks operate
            at roughly the nominal frequency.

            Low speed means the external clock is approximately half the frequency of the
            internal oscillator source. When this option is used, the internal dividers are
            stepped down.  As a result, previously undivided clocks now run at half frequency,
            while previously divided clocks run at roughly the nominal frequency.

            See external clock switch support in documentation for more details.
          '''
          resval: false
        }
      ]
      // avoid writing random values to this register as it could trigger transient checks
      // in mubi sync
      tags: ["excl:CsrAllTests:CsrExclWrite"]
    },

    { name: "EXTCLK_STATUS",
      desc: '''
        Status of requested external clock switch
      ''',
      swaccess: "ro",
      hwaccess: "hwo",
      hwext: "true",
      fields: [
        {
          bits: "3:0",
          name: "ACK",
          mubi: true,
          desc: '''
            When !!EXTCLK_CTRL.SEL is set to kMultiBitBool4True, this field reflects
            whether the clock has been switched the external source.

            kMultiBitBool4True indicates the switch is complete.
            kMultiBitBool4False indicates the switch is either not possible or still ongoing.
          '''
          resval: "false"
        },
      ]
    },

    { name: "JITTER_REGWEN",
      desc: "Jitter write enable",
      swaccess: "rw0c",
      hwaccess: "none",
      fields: [
        { bits: "0",
          name: "EN",
          resval: "1"
          desc: '''
            When 1, the value of !!JITTER_ENABLE can be changed.  When 0, writes have no
            effect.
          '''
        },
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
          // avoid writing random values to this register as it could trigger transient checks
          // in mubi sync
          tags: ["excl:CsrAllTests:CsrExclWrite"]
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
      // the CLK_HINT_STATUS register is read-only and cannot be checked.
      // This register's value depends on the IDLE inputs, so cannot be predicted.
      tags: ["excl:CsrNonInitTests:CsrExclCheck:CsrExclCheck"]
    },

    { name: "MEASURE_CTRL_REGWEN",
      desc: "Measurement control write enable",
      swaccess: "rw0c",
      hwaccess: "hrw",
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
    { name: "${src.upper()}_MEAS_CTRL_EN",
      desc: '''
        Enable for measurement control
      ''',
      regwen: "MEASURE_CTRL_REGWEN",
      swaccess: "rw",
      hwaccess: "hrw",
      async: "clk_${src}_i",
      fields: [
        {
          bits: "3:0",
          name: "EN",
          desc: "Enable measurement for ${src}",
          mubi: true,
          resval: false,
        },
      ]
      // Measurements can cause recoverable errors depending on the
      // thresholds which randomized CSR tests will not predict correctly.
      // To provide better CSR coverage we allow writing the threshold
      // fields, but not enabling the counters.
      tags: ["excl:CsrAllTests:CsrExclWrite"]
    },
<%
  freq = clocks.all_srcs[src].freq
  ratio = int(freq / aon_freq)
  # Add extra bit to width for margin
  width = ratio.bit_length() + 1
  max_msb = width - 1
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
          bits: "${max_msb}:0",
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
        { bits: "0",
          name: "SHADOW_UPDATE_ERR",
          resval: 0
          desc: '''
            One of the shadow registers encountered an update error.
          '''
        },
% for src in typed_clocks.rg_srcs:
        {
          bits: "${loop.index+1}",
          name: "${src.upper()}_MEASURE_ERR",
          resval: 0,
          desc: '''
            ${src} has encountered a measurement error.
          '''
        },
% endfor
% for src in typed_clocks.rg_srcs:
        {
          bits: "${loop.index + len(typed_clocks.rg_srcs)+1}",
          name: "${src.upper()}_TIMEOUT_ERR",
          resval: 0,
          desc: '''
            ${src} has timed out.
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
        { bits: "1",
          name: "IDLE_CNT",
          resval: 0
          desc: '''
            One of the idle counts encountered a duplicate error.
          '''
        },
        { bits: "2",
          name: "SHADOW_STORAGE_ERR",
          resval: 0
          desc: '''
            One of the shadow registers encountered a storage error.
          '''
        },
      ]
    },
  ]
}
