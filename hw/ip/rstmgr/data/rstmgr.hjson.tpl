// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%
  crash_dump_srcs = ['alert', 'cpu']
%>

# RSTMGR register template
#
{
  name: "RSTMGR",
  clock_primary: "clk_i",
  other_clock_list: [
% for clk in clks:
    "clk_${clk}_i"
% endfor
  ],
  bus_device: "tlul",
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
      desc: "Number of hardware reset requests, inclusive of escalation",
      type: "int",
      default: "${num_rstreqs+1}",
      local: "true"
    },

    { name: "NumSwResets",
      desc: "Number of software resets",
      type: "int",
      default: "${len(sw_rsts)}",
      local: "true"
    },


  ],

  // Define rstmgr struct package
  inter_signal_list: [
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

    { struct:  "rstmgr_ast",
      type:    "uni",
      name:    "ast",
      act:     "rcv",
      package: "rstmgr_pkg", // Origin package (only needs for the req)
    },

    { struct:  "rstmgr_cpu",
      type:    "uni",
      name:    "cpu",
      act:     "rcv",
      package: "rstmgr_pkg", // Origin package (only needs for the req)
    },

    { struct:  "alert_crashdump",
      type:    "uni",
      name:    "alert_dump",
      act:     "rcv",
      package: "alert_pkg",
    },

    { struct:  "crashdump",
      type:    "uni",
      name:    "cpu_dump",
      act:     "rcv",
      package: "rv_core_ibex_pkg",
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

        // reset requests include escalation reset + peripheral requests
        { bits: "${3 + num_rstreqs}:3",
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
    { name: "${dump_src.upper()}_INFO_CTRL",
      desc: '''
            ${dump_src.capitalize()} info dump controls.
            ''',
      swaccess: "rw",
      hwaccess: "hro",
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
          tags: [// This field only reflects the status of the design, thus the
                 // default value is likely to change and not remain 0
                 "excl:CsrAllTests:CsrExclCheck"]
        },
      ]
    },

    { name: "${dump_src.upper()}_INFO",
      desc: '''
              ${dump_src.capitalize()} dump information prior to last reset.
              Which value read is controlled by the !${dump_src.upper()}_INFO_CTRL register.
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
        name:  "SW_RST_REGEN",
        desc:  '''
          Register write enable for software controllabe resets.
          When a particular bit value is 0, the corresponding value in !SW_RST_CTRL can no longer be changed.
          When a particular bit value is 1, the corresponding value in !SW_RST_CTRL can be changed.
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
        tags: [// Don't reset other IPs as it will affect CSR access on these IPs
               "excl:CsrAllTests:CsrExclWrite"]
      }
    }

    { multireg: {
        cname: "RSTMGR_SW_RST",
        name:  "SW_RST_CTRL_N",
        desc:  '''
          Software controllabe resets.
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
  ]


}
