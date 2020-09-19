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

        { bits: "${3 + num_rstreqs - 1}:3",
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
