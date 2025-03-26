// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

# RACL Control register template
#
{
  name:               "${module_instance_name}",
  human_name:         "RACL Control",
  one_line_desc:      "Implements the RACL policy registers to distribute to subscribing IPs.",
  one_paragraph_desc: '''
  Implements the RACL policy registers to distribute to subscribing IPs.
  '''
  // Unique comportable IP identifier defined under KNOWN_CIP_IDS in the regtool.
  cip_id:             "43",
  design_spec:        "../doc",
  dv_doc:             "../doc/dv",
  hw_checklist:       "../doc/checklist",
  sw_checklist:       "/sw/device/lib/dif/dif_racl_ctrl",
  revisions: [
    {
      version:            "1.0.0",
      life_stage:         "L1",
      design_stage:       "D0",
      verification_stage: "V0",
      dif_stage:          "S0",
    }
  ]
  clocking: [
    {clock: "clk_i", reset: "rst_ni"},
  ]
  bus_interfaces: [
    { protocol: "tlul", direction: "device", static_racl_support: true }
  ],
  // In order to not disturb the racl_ctrl address map, we place the alert test and interrupt
  // registers manually at a safe offset after the main CSRs.
  // TODO(#26748) Add tooling support to avoid manual placement of alert/interrupt registers
  no_auto_intr_regs: "True",
  no_auto_alert_regs: "True",
  interrupt_list: [
    { name: "racl_error",
      desc: "RACL error has occurred.",
      type: "status"
    }
  ]
  alert_list: [
    { name: "fatal_fault"
      desc: "This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected."
    }
  % if enable_shadow_reg:
    { name: "recov_ctrl_update_err",
      desc: "This recoverable alert is triggered upon detecting an update error in the shadowed Control Register."
    }
  % endif
  ],
  countermeasures: [
    { name: "BUS.INTEGRITY",
      desc: "End-to-end bus integrity scheme."
    }
  % if enable_shadow_reg:
    { name: "RACL_POLICY.CONFIG.SHADOW",
      desc: "RACL policy registers are shadowed."
    }
  % endif
  ]
  regwidth: "32",
  param_list: [
    { name: "NumSubscribingIps",
      desc: "Number of subscribing RACL IPs",
      type: "int",
      default: "${nr_subscribing_ips}",
      expose: "true"
      local: "true"
    },
    { name: "NumExternalSubscribingIps",
      desc: "Number of external subscribing RACL IPs",
      type: "int",
      default: "1",
      expose: "true"
      local: "false"
    },
  ],
  inter_signal_list: [
    { struct:  "racl_policy_vec",
      type:    "uni",
      name:    "racl_policies",
      act:     "req",
      package: "top_racl_pkg",
      desc:    '''
        Policy vector distributed to the subscribing RACL IPs.
      '''
    }
    { struct:  "racl_error_log",
      type:    "uni",
      name:    "racl_error",
      act:     "rcv",
      width:   "NumSubscribingIps"
      package: "top_racl_pkg",
      desc:    '''
        Error log information from all IPs.
        Only one IP can raise an error at a time.
      '''
    }
    { struct:  "racl_error_log",
      type:    "uni",
      name:    "racl_error_external",
      act:     "rcv",
      width:   "NumExternalSubscribingIps"
      package: "top_racl_pkg",
      desc:    '''
        Error log information from all external IPs.
        Only one IP can raise an error at a time.
      '''
    }
  ],

  registers: [
    % for policy in policies:
    { name: "POLICY_${policy['name'].upper()}${"_SHADOWED" if enable_shadow_reg else ""}"
      desc: '''
            Read and write policy for ${policy['name']}
            '''
      swaccess: "rw"
      hwaccess: "hro"
    % if enable_shadow_reg:
      shadowed: "true"
      update_err_alert: "recov_ctrl_update_err"
      storage_err_alert: "fatal_fault"
    % endif
      fields: [
        { bits: "31:16"
          name: "write_perm"
          resval: ${policy['wr_default']}
          desc: '''
                Write permission for policy ${policy['name']}
                '''
        }
        { bits: "15:0"
          name: "read_perm"
          resval: ${policy['rd_default']}
          desc: '''
                Read permission for policy ${policy['name']}
                '''
        }
      ]
    }
    { reserved: "1" }
    % endfor
    { skipto: "0xE8" }
    { name: "INTR_STATE",
      desc: "Interrupt State Register",
      swaccess: "ro",
      hwaccess: "hrw",
      fields: [
        { bits: "0",
          name: "racl_error",
          desc: '''
                Interrupt status. The interrupt is raised when a RACL error occurs and cleared
                when error_log is cleared by writing 1 to error_log.valid."
                '''
        }
      ]
      tags: [// interrupt could be updated by HW
        "excl:CsrNonInitTests:CsrExclWriteCheck"],
    },
    { name: "INTR_ENABLE",
        desc: "Interrupt Enable Register",
        swaccess: "rw",
        hwaccess: "hro",
        fields: [
          { bits: "0",
            name: "IE",
            desc: "Interrupt Enable"
          }
        ]
    },
    { name: "INTR_TEST",
      desc: "Interrupt Test Register",
      swaccess: "wo",
      hwaccess: "hro",
      hwext: "true",
      hwqe: "true",
      fields: [
        { bits: "0",
          name: "racl_error",
          desc: "Write 1 to force racl_error interrupt",
        }
      ]
    },
    { name: "ALERT_TEST",
      desc: '''Alert Test Register.''',
      swaccess: "wo",
      hwaccess: "hro",
      hwqe:     "True",
      hwext:    "True",
      fields: [
        { bits: "0",
          name: "fatal_fault",
          desc: "'Write 1 to trigger one alert event of this kind.'",
        }
        { bits: "1",
          name: "recov_ctrl_update_err",
          desc: "'Write 1 to trigger one alert event of this kind.'",
        }
      ],
    }
    { name: "ERROR_LOG"
      desc: "Error logging registers"
      swaccess: "ro"
      hwaccess: "hwo"
      hwqe: "true"
      fields: [
        { bits: "0"
          name: "valid"
          resval: 0x0
          swaccess: "rw1c"
          hwaccess: "hrw"
          desc: '''
                Indicates a RACL error and the log register contains valid data.
                Writing a one clears this register and the !!ERROR_LOG_ADDRESS register.
                '''
        }
        { bits: "1"
          name: "overflow"
          resval: 0x0
          desc: '''
                Indicates a RACL error overflow when a RACL error occurred while the log register was set.
                '''
        }
        { bits: "2"
          name: "read_access"
          resval: 0x0
          desc: '''
                0: Write transfer was denied.
                1: Read transfer was denied.
                '''
        }
        { bits: "${3 + nr_role_bits - 1}:3"
          name: "role"
          resval: 0x0
          desc: '''
                RACL role causing the error.
                '''
        }
        { bits: "${3 + nr_role_bits + nr_ctn_uid_bits - 1}:${3 + nr_role_bits}"
          name: "ctn_uid"
          resval: 0x0
          desc: '''
                CTN UID causing the error.
                '''
        }
      ]
    }
    { name: "ERROR_LOG_ADDRESS"
      desc: '''Contains the address on which a RACL violation occurred.
               This register is valid if and only if the `valid` field of !!ERROR_LOG is true.
               Once valid, the address doesn't change (even if there are subsequent RACL violations) until the register gets cleared.
               This register gets cleared when SW writes `1` to the `valid` field of the !!ERROR_LOG register.
            '''
      swaccess: "ro"
      hwaccess: "hwo"
      hwqe: "true"
      fields: [
        { bits: "31:0"
          name: "address"
          resval: 0x0
          desc: '''
                Address on which a RACL violation occurred.
                '''
        }
      ]
    }
  ]
}
