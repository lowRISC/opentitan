// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%
  crash_dump_srcs = ['alert', 'cpu']
  # long term change this to a method where the generating function
  # can query the pwrmgr for how many internal resets it has
  total_hw_resets = num_rstreqs+2
%>

# RSTMGR register template
#
{
  name: "RSTMGR",
  clocking: [
    {clock: "clk_i", reset: "rst_ni", primary: true},
% for clk in reset_obj.get_clocks():
    {clock: "clk_${clk}_i"}
% endfor
  ]
  bus_interfaces: [
    { protocol: "tlul", direction: "device" }
  ],
  alert_list: [
    { name: "fatal_fault",
      desc: '''
        This fatal alert is triggered when a fatal structural fault is detected.
        Structural faults include errors such as sparse fsm errors and tlul integrity errors.
      '''
    }
    { name: "fatal_cnsty_fault",
      desc: '''
        This fatal alert is triggered when a reset consistency fault is detected.
        It is separated from the category above for clearer error collection and debug.
      '''
    }
  ],
  countermeasures: [
    { name: "BUS.INTEGRITY",
      desc: "End-to-end bus integrity scheme."
    }
    { name: "SCAN.INTERSIG.MUBI",
      desc: "scan control signals are multibit"
    }
    { name: "LEAF.RST.BKGN_CHK",
      desc: "Background consistency checks for each leaf reset."
    }
    { name: "LEAF.RST.SHADOW",
      desc: "Leaf resets to blocks containing shadow registers are shadowed"
    }
    { name: "LEAF.FSM.SPARSE",
      desc: "Sparsely encoded fsm for each leaf rst check. The Hamming delta is only 3 as there are a significant number of leaf resets"
    }
    { name: "SW_RST.CONFIG.REGWEN",
      desc: "Software reset controls are protected by regwen"
    }
    { name: "DUMP_CTRL.CONFIG.REGWEN",
      desc: "Crash dump controls are protected by regwen"
    }
  ]
  regwidth: "32",
  scan: "true",
  scan_reset: "true",
  param_list: [
    { name: "RdWidth",
      desc: "Read width for crash info",
      type: "int",
      default: "32",
      local: "true"
    },

    { name: "IdxWidth",
      desc: "Index width for crash info",
      type: "int",
      default: "4",
      local: "true"
    },

    { name: "NumHwResets",
      desc: "Number of hardware reset requests, inclusive of pwrmgr's 2 internal resets",
      type: "int",
      default: "${total_hw_resets}",
      local: "true"
    },

    { name: "NumSwResets",
      desc: "Number of software resets",
      type: "int",
      default: "${len(sw_rsts)}",
      local: "true"
    },

    { name:    "SecCheck",
      type:    "bit",
      default: "1'b1",
      desc:    '''
        When 1, enable rstmgr reset consistency checks.
        When 0, there are no consistency checks.
      '''
      local:   "false",
      expose:  "true"
    },

    { name:    "SecMaxSyncDelay",
      type:    "int",
      default: "2",
      desc:    '''
        The maximum synchronization delay for parent / child reset checks.
      '''
      local:   "false",
      expose:  "true"
    },
  ],

  // Define rstmgr struct package
  inter_signal_list: [
    { struct:  "logic",
      type:    "uni",
      name:    "por_n",
      act:     "rcv",
      width:   "${len(power_domains)}"
    },

    { struct:  "pwr_rst",    // pwr_rst_req_t, pwr_rst_rsp_t
      type:    "req_rsp",
      name:    "pwr",        // resets_o (req), resets_i (rsp)
      act:     "rsp",
    },

    { struct:  "rstmgr_out",
      type:    "uni",
      name:    "resets",
      act:     "req",
      package: "rstmgr_pkg", // Origin package (only needs for the req)
    },

    { struct:  "rstmgr_rst_en",
      type:    "uni",
      name:    "rst_en",
      act:     "req",
      package: "rstmgr_pkg", // Origin package (only needs for the req)
    },

    { struct:  "logic",
      type:    "uni",
      name:    "rst_cpu_n",
      act:     "rcv",
    },
    { struct:  "logic",
      type:    "uni",
      name:    "ndmreset_req",
      act:     "rcv",
    },

    { struct:  "alert_crashdump",
      type:    "uni",
      name:    "alert_dump",
      act:     "rcv",
      package: "alert_pkg",
    },

    { struct:  "cpu_crash_dump",
      type:    "uni",
      name:    "cpu_dump",
      act:     "rcv",
      package: "rv_core_ibex_pkg",
    },

    { struct:  "mubi4",
      type:    "uni",
      name:    "sw_rst_req",
      act:     "req",
      package: "prim_mubi_pkg",
    },

    // Exported resets
% for intf in export_rsts:
    { struct:  "rstmgr_${intf}_out",
      type:    "uni",
      name:    "resets_${intf}",
      act:     "req",
      package: "rstmgr_pkg", // Origin package (only needs for the req)
    }
% endfor
  ],

  registers: [

    { name: "RESET_REQ",
      desc: '''
        Software requested system reset.
      ''',
      swaccess: "rw",
      hwaccess: "hrw",
      fields: [
        { bits: "3:0",
          mubi: true
          name: "VAL",
          desc: '''
            When set to kMultiBitBool4True, a reset to power manager is requested.
            Upon completion of reset, this bit is automatically cleared by hardware.
          '''
          resval: false
        },
      ],
      tags: [// This register will cause a system reset, directed test only
        "excl:CsrAllTests:CsrExclWrite"]
    },

    { name: "RESET_INFO",
      desc: '''
            Device reset reason.
            ''',
      swaccess: "rw1c",
      hwaccess: "hwo",
      fields: [
        { bits: "0",
          hwaccess: "none",
          name: "POR",
          desc: '''
            Indicates when a device has reset due to power up.
            '''
          resval: "1"
        },

        { bits: "1",
          name: "LOW_POWER_EXIT",
          desc: '''
            Indicates when a device has reset due low power exit.
            '''
          resval: "0"
        },

        { bits: "2",
          name: "NDM_RESET",
          desc: '''
            Indicates when a device has reset due to non-debug-module request.
            '''
          resval: "0"
        },

        { bits: "3",
          hwaccess: "hrw",
          name: "SW_RESET",
          desc: '''
            Indicates when a device has reset due to !!RESET_REQ.
            '''
          resval: "0"
        },

        // reset requests include escalation reset + peripheral requests
        { bits: "${4 + total_hw_resets - 1}:4",
          hwaccess: "hrw",
          name: "HW_REQ",
          desc: '''
            Indicates when a device has reset due to a peripheral request.
            This can be an alert escalation, watchdog or anything else.
            '''
          resval: "0"
        },
      ]
    },

    % for dump_src in crash_dump_srcs:
    { name: "${dump_src.upper()}_REGWEN",
      desc: "${dump_src.capitalize()} write enable",
      swaccess: "rw0c",
      hwaccess: "none",
      fields: [
        { bits: "0",
          name: "EN",
          resval: "1"
          desc: '''
            When 1, !!${dump_src.upper()}_INFO_CTRL can be modified.
          '''
        },
      ]
    }

    { name: "${dump_src.upper()}_INFO_CTRL",
      desc: '''
            ${dump_src.capitalize()} info dump controls.
            ''',
      swaccess: "rw",
      hwaccess: "hro",
      regwen: "${dump_src.upper()}_REGWEN",
      fields: [
        { bits: "0",
          name: "EN",
          hwaccess: "hrw",
          desc: '''
            Enable ${dump_src} dump to capture new information.
            This field is automatically set to 0 upon system reset (even if rstmgr is not reset).
            '''
          resval: "0"
        },

        { bits: "4+IdxWidth-1:4",
          name: "INDEX",
          desc: '''
            Controls which 32-bit value to read.
            '''
          resval: "0"
        },
      ]
    },

    { name: "${dump_src.upper()}_INFO_ATTR",
      desc: '''
            ${dump_src.capitalize()} info dump attributes.
            ''',
      swaccess: "ro",
      hwaccess: "hwo",
      hwext: "true",
      fields: [
        { bits: "IdxWidth-1:0",
          name: "CNT_AVAIL",
          swaccess: "ro",
          hwaccess: "hwo",
          desc: '''
            The number of 32-bit values contained in the ${dump_src} info dump.
            '''
          resval: "0",
          tags: [// This field is tied to a design constant, thus the
                 // default value is never 0.  Since there is not a way
                 // to express this behavior at the moment, exclude from automated checks.
                 "excl:CsrAllTests:CsrExclCheck"]
        },
      ]
    },

    { name: "${dump_src.upper()}_INFO",
      desc: '''
              ${dump_src.capitalize()} dump information prior to last reset.
              Which value read is controlled by the !!${dump_src.upper()}_INFO_CTRL register.
            ''',
      swaccess: "ro",
      hwaccess: "hwo",
      hwext: "true",
      fields: [
        { bits: "31:0",
          name: "VALUE",
          desc: '''
            The current 32-bit value of crash dump.
            '''
          resval: "0",
        },
      ]
    },
    % endfor


    ########################
    # Templated registers for software control
    ########################

    { multireg: {
        cname: "RSTMGR_SW_RST",
        name:  "SW_RST_REGWEN",
        desc:  '''
          Register write enable for software controllable resets.
          When a particular bit value is 0, the corresponding value in !!SW_RST_CTRL_N can no longer be changed.
          When a particular bit value is 1, the corresponding value in !!SW_RST_CTRL_N can be changed.
        ''',
        count: "NumSwResets",
        swaccess: "rw0c",
        hwaccess: "hro",
        fields: [
          {
            bits: "0",
            name: "EN",
            desc: "Register write enable for software controllable resets",
            resval: "1",
          },
        ],
      }
    }

    { multireg: {
        cname: "RSTMGR_SW_RST",
        name:  "SW_RST_CTRL_N",
        desc:  '''
          Software controllable resets.
          When a particular bit value is 0, the corresponding module is held in reset.
          When a particular bit value is 1, the corresponding module is not held in reset.
        ''',
        count: "NumSwResets",
        swaccess: "rw",
        hwaccess: "hrw",
        hwext: "true",
        hwqe: "true",
        fields: [
          {
            bits: "0",
            name: "VAL",
            desc: "Software reset value",
            resval: "1",
          },
        ],
        tags: [// Don't reset other IPs as it will affect CSR access on these IPs
               "excl:CsrAllTests:CsrExclWrite"]
      }
    }

    { name: "ERR_CODE",
      desc: '''
        A bit vector of all the errors that have occurred in reset manager
      ''',
      swaccess: "rw1c",
      hwaccess: "hwo",
      fields: [
        { bits: "0",
          name: "REG_INTG_ERR",
          desc: '''
            The register file has experienced an integrity error.
          '''
          resval: "0"
        },

        { bits: "1",
          name: "RESET_CONSISTENCY_ERR",
          desc: '''
            A inconsistent parent / child reset was observed.
          '''
          resval: "0"
        },

      ]
    },
  ]
}
