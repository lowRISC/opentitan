// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
# AC Range Check register template
{
  name:               "ac_range_check"
  human_name:         "Access Control Range Check"
  one_line_desc:      "Access Control Range Check."
  one_paragraph_desc: '''
  '''
  cip_id:             "41",
  design_spec:        "../doc"
  dv_doc:             "../doc/dv"
  version:            "1.0.0"

  clocking: [{clock: "clk_i", reset: "rst_ni", primary: true}]
  bus_interfaces: [
    { protocol: "tlul", direction: "device", hier_path: "u_ac_range_check_reg" }
  ]
  param_list: [
    { name:    "NumRanges",
      desc:    "Number of range registers",
      type:    "int",
      default: "${num_ranges}",
    },
    { name:    "DenyCountWidth",
      desc:    "Witdth of the deny counter",
      type:    "int",
      default: "8",
      local:   "true"
    },
  ],
  inter_signal_list: [
    { name:    "range_check_overwrite"
      type:    "uni",
      act:     "req",
      package: "prim_mubi_pkg",
      struct:  "mubi8",
      width:   "1"
      desc:    "Overwrites all ranges and let all requests pass through."
    },
    { struct:  "tl_h2d"
      package: "tlul_pkg"
      type:    "uni"
      name:    "ctn_tl_h2d"
      act:     "rcv"
      desc:    "TL-UL input port (request part), synchronous"
    }
    { struct:  "tl_d2h"
      package: "tlul_pkg"
      type:    "uni"
      name:    "ctn_tl_d2h"
      act:     "req"
      desc:    "TL-UL input port (response part), synchronous"
    }
    { struct:  "tl_h2d"
      package: "tlul_pkg"
      type:    "uni"
      name:    "ctn_filtered_tl_h2d"
      act:     "req"
      desc:    "Filtered TL-UL output port (request part), synchronous"
    }
    { struct:  "tl_d2h"
      package: "tlul_pkg"
      type:    "uni"
      name:    "ctn_filtered_tl_d2h"
      act:     "rcv"
      desc:    "Filtered TL-UL output port (response part), synchronous"
    }
  ]
  interrupt_list: [
    { name: "deny_cnt_reached"
      desc: "Deny counter has reached threshold."
    }
  ]
  alert_list: [
    { name: "recov_ctrl_update_err",
      desc: "This recoverable alert is triggered upon detecting an update error in the shadowed Control Register."
    }
    { name: "fatal_fault"
      desc: "This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected or the internal counter has an error."
    }
  ]
  countermeasures: [
    { name: "BUS.INTEGRITY",
      desc: "End-to-end bus integrity scheme."
    }
  ]
  regwidth: "32"
  registers: [
    { name: "LOG_CONFIG"
      desc: ""
      swaccess: "rw"
      hwaccess: "hro"
      fields: [
        { bits: "9:2"
          name: "deny_cnt_threshold"
          resval: 0x0
          desc: "An interrupt is raised (if enabled) when deny_cnt reaches the configured deny_cnt_threshold."
        }
        { bits: "1"
          name: "log_clear"
          resval: 0x0
          desc: '''Clears all log information for the first denied access including: 
                    - LOG_STATUS
                    - LOG_ADDRESS.
          '''
        }
        { bits: "0"
          name: "log_enable"
          resval: 0x0
          desc: "When set, blocked requests are logged by the deny counter."
        }
      ]
    }
    { name: "LOG_STATUS"
      desc: '''
            The LOG_STATUS register stores the number of denied accesses and gives more detailed diagnostics to the first denied request. 
            All fields of LOG_STATUS (other than deny_cnt) are only valid if deny_cnt > 0.
            '''
      swaccess: "ro"
      hwaccess: "hwo"
      fields: [
        { bits: "22:18"
          name: "deny_range_index"
          resval: 0x0
          desc: "Index of the range that caused the denied access."
        }
        { bits: "17:14"
          name: "denied_source_role"
          resval: 0x0
          desc: "Source RACL role that was denied access."
        }
        { bits: "13"
          name: "denied_racl_write"
          resval: 0x0
          desc: "Indicates whether a write access was denied by RACL."
        }
        { bits: "12"
          name: "denied_racl_read"
          resval: 0x0
          desc: "Indicates whether a read access was denied by RACL."
        }
        { bits: "11"
          name: "denied_no_match"
          resval: 0x0
          desc: "Indicates whether the access was denied because no range matched."
        }
        { bits: "10"
          name: "denied_execute_access"
          resval: 0x0
          desc: "Indicates whether execution access was denied."
        }
        { bits: "9"
          name: "denied_write_access"
          resval: 0x0
          desc: "Indicates whether a write access was denied."
        }
        { bits: "8"
          name: "denied_read_access"
          resval: 0x0
          desc: "Indicates whether a read access was denied."
        }
        { bits: "7:0"
          name: "deny_cnt"
          resval: 0x0
          desc: '''
                Software mirror of the internal deny counter.
                Gets incremented for every blocked request.
                '''
        }
      ]
    }
    { name: "LOG_ADDRESS"
      desc: '''
            First denied request address (if logging is enabled) gets written into that register.
            '''
      swaccess: "ro"
      hwaccess: "hwo"
      fields: [
        { bits: "31:0"
          name: "log_address"
          resval: 0x0
          desc: "First denied request address."
        }
      ]
    }
    { multireg: {
        name: "RANGE_REGWEN"
        desc: '''
              This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_PERM_x, and RANGE_RACL_POLICY_SHADOWED_x register. 
              When cleared to Mubi4::False, the corresponding range configuration registers are locked and cannot be changed until the next reset.
              '''
        count: "NumRanges"
        cname: "range_regwen"
        swaccess: "rw0c"
        hwaccess: "none"
        compact: false
        fields: [
          { bits: "3:0"
            resval: true
            mubi: true
            name: "regwen"
            desc: "Clearing this register, locks the confgiguration registers of that range until the next reset."
          }
        ]
      }
    }
    { multireg: {
        name: "RANGE_BASE"
        desc: '''
              Base address for the range check.
              The range base register exists per range and holds the base address for the range check.
              The minimum granularity of the range is 4 bytes.
              Therefore, the lowest 2 bits of the 32-bit base and limit registers are tied to zero.
              '''
        count: "NumRanges"
        cname: "range_base"
        swaccess: "rw"
        hwaccess: "hro"
        regwen: "RANGE_REGWEN"
        regwen_multi: true
        fields: [
          { name: "base"
            desc: "Base address"
            bits: "31:2"
            resval: 0x0
          }
        ]
      }
    }
    { multireg: {
        name: "RANGE_LIMIT"
        desc: '''
              The (exclusive) limit address register used for the address matching. 
              '''
        count: "NumRanges"
        cname: "BASE"
        swaccess: "rw"
        hwaccess: "hro"
        regwen: "RANGE_REGWEN"
        regwen_multi: true
        fields: [
          { name: "limit"
            desc: "Exclusive limit address."
            bits: "31:2"
            resval: 0x0
          }
        ]
      }
    }
    { multireg: {
        name: "RANGE_PERM"
        desc: '''
              Permission configuration of the range.
              The permission register exists per range and determines the access permissions of the particular range.
              If it is not enabled, the range is not considered during the range check.
              '''
        count: "NumRanges"
        cname: "BASE"
        swaccess: "rw"
        hwaccess: "hro"
        regwen: "RANGE_REGWEN"
        regwen_multi: true
        fields: [
          { name: "log_denied_access"
            desc: "When set to Mubi4::True, a denied access based on in this range is being logged."
            bits: "19:16"
            mubi: true
            resval: true
          }
          { name: "execute_access"
            desc: "When set to Mubi4::True, code execution from this range is allowed."
            bits: "15:12"
            mubi: true
            resval: false
          }
          { name: "write_access"
            desc: "When set to Mubi4::True, write access to that range is allowed."
            bits: "11:8"
            mubi: true
            resval: false
          }
          { name: "read_access"
            desc: "When set to Mubi4::True, read access from that range is allowed."
            bits: "7:4"
            mubi: true
            resval: false
          }
          { name: "enable"
            desc: "When set to Mubi4::True, the range is considered in the range check."
            bits: "3:0"
            mubi: true
            resval: false
          }
        ]
      }
    }
    { multireg: {
        name: "RANGE_RACL_POLICY_SHADOWED"
        desc: '''
              The RACL policy register exists and allows the system to further restrict the access to specific source roles.
              The default value for both the read and write permission bitmap is set to a value to allow the access from all roles.
              This register is protected against fault attacks by using a shadow register implementation. 
              '''
        count: "NumRanges"
        cname: "RACL"
        swaccess: "rw"
        hwaccess: "hro"
        regwen: "RANGE_REGWEN"
        regwen_multi: true
        shadowed: "true",
        fields: [
          { name: "write_perm"
            desc: "Write permission policy bitmap."
            bits: "31:16"
            resval: 0x0
          }
          { name: "read_perm"
            desc: "Read permission policy bitmap."
            bits: "15:0"
            resval: 0x0
          }
        ]
      }
    }
  ]
}
