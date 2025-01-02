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
    { protocol: "tlul", direction: "device" }
  ],
  alert_list: [
  % if enable_shadow_reg:
    { name: "recov_ctrl_update_err",
      desc: "This recoverable alert is triggered upon detecting an update error in the shadowed Control Register."
    }
  % endif
    { name: "fatal_fault"
      desc: "This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected."
    }
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
    { name: "NumPolicies",
      desc: "Number of policies",
      type: "int",
      default: "${nr_policies}",
      local: "true"
    },
    { name: "NumSubscribingIps",
      desc: "Number of subscribing RACL IPs",
      type: "int",
      default: "1",
      expose: "true"
      local: "true"
    },
  ],
  inter_signal_list: [
    { struct:  "policies",
      type:    "uni",
      name:    "policies",
      act:     "req",
      package: "racl_pkg",
      desc:    '''
        Policy vector distributed to the subscribing RACL IPs.
      '''
    },
  ],

  registers: [
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
                Writing a one clears the error log register.
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
          name: "write_read"
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
    % for policy in policies:
    { name: "POLICY_${policy['name'].upper()}${"_SHADOWED" if enable_shadow_reg else ""}"
      desc: '''
            Read and write policy for ${policy}
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
                Write permission for policy ${policy}
                '''
        }
        { bits: "15:0"
          name: "read_perm"
          resval: ${policy['rd_default']}
          desc: '''
                Read permission for policy ${policy}
                '''
        }
      ]
    }
    % endfor
  ]
}
