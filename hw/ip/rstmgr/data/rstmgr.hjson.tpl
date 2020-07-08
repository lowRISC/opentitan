// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%

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
  param_list: [
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

    { struct:  "rstmgr_peri",
      type:    "uni",
      name:    "peri",
      act:     "rcv",
      package: "rstmgr_pkg", // Origin package (only needs for the req)
    }
  ],

  registers: [
    { name: "RESET_INFO",
      desc: '''
            Device reset reason.
            ''',
      swaccess: "rw1c",
      hwaccess: "hrw",
      hwext: "true",
      hwqe: "true",
      fields: [
        {
            bits: "4:0",
            name: "CAUSE",
            resval: 1,
            desc: '''Indicates reset cause.  The bits below are not mutually exclusive, and multiple
            bits can be set at the same time.'''
            enum: [
             {value: "0x1",  name: "por",              desc: "Indicates when a device has reset due to power up"},
             {value: "0x2",  name: "low_power_exit",   desc: "Indicates when a device has reset due low power exit"},
             {value: "0x4",  name: "watchdog",         desc: "Indicates when a device has reset due to watchdog"},
             {value: "0x8",  name: "escalation",       desc: "Indicates when a device has reset due to security escalation"},
             {value: "0x10", name: "Non-debug-module", desc: "Indicates when a device has reset due to non-debug-module request"},
            ]
        }
      ]
    },

    ########################
    # Templated registers for software control
    ########################

% for rst in sw_rsts:
    { name: "${rst['name'].upper()}_REGEN",
      desc: '''
            Register write enable for ${rst['name']} reset.
            ''',
      swaccess: "rw1c",
      hwaccess: "none",
      fields: [
        {
            bits:   "0",
            desc: ''' When 1, rst_${rst['name']}_n is software programmable.
            '''
            resval: 1,
        },
      ]
      tags: [// Don't reset other IPs as it will affect CSR access on these IPs
             "excl:CsrAllTests:CsrExclWrite"]
    },

    { name: "RST_${rst['name'].upper()}_N",
      regwen:  "${rst['name'].upper()}_REGEN",
      desc: '''
            Software reset control for ${rst['name']}
            ''',
      swaccess: "rw",
      hwaccess: "hro",
      fields: [
        {
            bits:   "0",
            desc: ''' When set to 0, ${rst['name']} is held in reset.  This bit can only be
            programmed when ${rst['name']}_regen is 1.
            '''
            resval: 1,
        },
      ]
      tags: [// Don't reset other IPs as it will affect CSR access on these IPs
             "excl:CsrAllTests:CsrExclWrite"]
    },
% endfor
  ]


}
