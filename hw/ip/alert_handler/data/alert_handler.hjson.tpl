// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
# ALERT_HANDLER register template
#
# Parameter (given by Python tool)
#  - n_alerts:    Number of alert sources
#  - esc_cnt_dw:  Width of escalation counter
#  - accu_cnt_dw: Width of accumulator
#  - async_on:    Enables asynchronous sygnalling between specific alert RX/TX pairs
#  - n_classes:   Number of supported classes (leave this at 4 at the moment)
<%
import math
chars = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H']
%>
{
  name: "ALERT_HANDLER",
  clock_primary: "clk_i",
  other_clock_list: [ "clk_edn_i" ],
  reset_primary: "rst_ni",
  other_reset_list: [ "rst_edn_ni" ],
  bus_interfaces: [
    { protocol: "tlul", direction: "device" }
  ],
  regwidth: "32",
  hier_path: "i_reg_wrap"
##############################################################################
  param_list: [
    // Random netlist constants
    { name:      "RndCnstLfsrSeed",
      desc:      "Compile-time random bits for initial LFSR seed",
      type:      "alert_pkg::lfsr_seed_t"
      randcount: "32",
      randtype:  "data", // randomize randcount databits
    }
    { name:      "RndCnstLfsrPerm",
      desc:      "Compile-time random permutation for LFSR output",
      type:      "alert_pkg::lfsr_perm_t"
      randcount: "32",
      randtype:  "perm", // random permutation for randcount elements
    }
    // Normal parameters
    { name: "NAlerts",
      desc: "Number of peripheral inputs",
      type: "int",
      default: "${n_alerts}",
      local: "true"
    },
    { name: "EscCntDw",
      desc: "Number of peripheral outputs",
      type: "int",
      default: "${esc_cnt_dw}",
      local: "true"
    },
    { name: "AccuCntDw",
      desc: "Number of peripheral outputs",
      type: "int",
      default: "${accu_cnt_dw}",
      local: "true"
    },
    { name: "AsyncOn",
      desc: "Number of peripheral outputs",
      type: "logic [NAlerts-1:0]",
      default: "${async_on}",
      local: "true"
    },
    { name: "N_CLASSES",
      desc: "Number of classes",
      type: "int",
      default: "${n_classes}",
      local: "true"
    },
    { name: "N_ESC_SEV",
      desc: "Number of escalation severities",
      type: "int",
      default: "4",
      local: "true"
    },
    { name: "N_PHASES",
      desc: "Number of escalation phases",
      type: "int",
      default: "4",
      local: "true"
    },
    { name: "N_LOC_ALERT",
      desc: "Number of local alerts phases",
      type: "int",
      default: "4",
      local: "true"
    },
    { name: "PING_CNT_DW",
      desc: "Width of ping counter",
      type: "int",
      default: "24",
      local: "true"
    },
    { name: "PHASE_DW",
      desc: "Width of phase ID",
      type: "int",
      default: "2",
      local: "true"
    },
    { name: "CLASS_DW",
      desc: "Width of class ID",
      type: "int",
      default: "${int(math.ceil(math.log2(n_classes)))}",
      local: "true"
    },
  ],

  inter_signal_list: [
    { struct:  "alert_crashdump",
      type:    "uni",
      name:    "crashdump",
      act:     "req",
      package: "alert_pkg"
    },
    { struct:  "edn"
      type:    "req_rsp"
      name:    "edn"
      act:     "req"
      width:   "1"
      package: "edn_pkg"
    },
    { struct:  "esc_rx"
      type:    "uni"
      name:    "esc_rx"
      act:     "rcv"
      width:   "4", // N_ESC_SEV
      package: "prim_esc_pkg"
    },
    { struct:  "esc_tx"
      type:    "uni"
      name:    "esc_tx"
      act:     "req"
      width:   "4", // N_ESC_SEV
      package: "prim_esc_pkg"
    },
  ]
##############################################################################
# interrupt registers for the classes
  interrupt_list: [
% for i in range(n_classes):
    { name: "class${chars[i].lower()}",
      desc: '''
            Interrupt state bit of Class ${chars[i]}. Set by HW in case an alert within this class triggered. Defaults true, write one to clear.
            ''',
    },
% endfor
  ],

  registers: [
##############################################################################
# register lock for ping timeout counter
    { name: "PING_TIMER_REGWEN",
      desc: '''
            Register write enable for !!PING_TIMEOUT_CYC and !!PING_TIMER_EN.
            ''',
      swaccess: "rw0c",
      hwaccess: "none",
      fields: [
        {
            bits:   "0",
            desc: '''
            When true, the !!PING_TIMEOUT_CYC and !!PING_TIMER_EN registers can be modified.
            When false, they become read-only. Defaults true, write one to clear.
            This should be cleared once the alert handler has been configured and the ping
            timer mechanism has been kicked off.
            '''
            resval: 1,
        },
      ]
    },
    { name:     "PING_TIMEOUT_CYC",
      desc:     '''
                Ping timeout cycle count.
                '''
      swaccess: "rw",
      hwaccess: "hro",
      regwen:   "PING_TIMER_REGWEN",
      fields: [
        {
          bits: "PING_CNT_DW-1:0",
          resval:   32,
          desc: '''
          Timeout value in cycles. If an alert receiver or an escalation sender does not
          respond to a ping within this timeout window, a pingfail alert will be raised.
          '''
        }
      ]
    }
    { name:     "PING_TIMER_EN",
      desc:     '''
                Ping timer enable.
                '''
      swaccess: "rw1s",
      hwaccess: "hro",
      regwen:   "PING_TIMER_REGWEN",
      fields: [
        {
          bits: "0",
          resval:   0,
          desc: '''
          Setting this to 1 enables the ping timer mechanism.
          This bit cannot be cleared to 0 once it has been set to 1.

          Note that the alert pinging mechanism will only ping alerts that have been enabled and locked.
          '''
        }
      ]
    }
##############################################################################
# all alerts
    { multireg: { name:     "ALERT_REGWEN",
                  desc:     "Register write enable for alert enable bits.",
                  count:    "NAlerts",
                  compact:  "false",
                  swaccess: "rw0c",
                  hwaccess: "hro",
                  hwqe:     "false",
                  cname:    "alert",
                  fields: [
                    { bits:   "0",
                      name:   "EN",
                      desc:   '''
                              Alert configuration write enable bit.
                              If this is cleared to 0, the corresponding !!ALERT_EN
                              and !!ALERT_CLASS bits are not writable anymore.

                              Note that the alert pinging mechanism will only ping alerts that have been enabled and locked.
                              ''',
                      resval: "1",
                    }
                  ]
                }
    },
    { multireg: { name:     "ALERT_EN",
                  desc:     '''Enable register for alerts.
                  ''',
                  count:    "NAlerts",
                  compact:  "false",
                  swaccess: "rw",
                  hwaccess: "hro",
                  regwen:   "ALERT_REGWEN",
                  regwen_multi: "true",
                  cname:    "alert",
                  tags:     [// Enable `alert_en` might cause top-level escalators to trigger
                             // unexpected reset
                             "excl:CsrAllTests:CsrExclWrite"]
                 fields: [
                    { bits: "0",
                      name: "EN_A",
                      resval: 0
                      desc: '''
                            Alert enable bit.

                            Note that the alert pinging mechanism will only ping alerts that have been enabled and locked.
                            '''
                    }
                  ]
                }
    },
    { multireg: { name:     "ALERT_CLASS",
                  desc:     '''Class assignment of alerts.
                  ''',
                  count:    "NAlerts",
                  compact:  "false",
                  swaccess: "rw",
                  hwaccess: "hro",
                  regwen:   "ALERT_REGWEN",
                  regwen_multi: "true",
                  cname:    "alert",
                  fields: [
                    {
                      bits: "CLASS_DW-1:0",
                      name: "CLASS_A",
                      resval: 0
                      desc: "Classification ",
                      enum: [
% for i in range(n_classes):
                              { value: "${i}", name: "Class${chars[i]}", desc: "" },
% endfor
                            ]
                    }
                  ]
                }
    },
    { multireg: {
      name: "ALERT_CAUSE",
      desc: "Alert Cause Register",
      count: "NAlerts",
      compact:  "false",
      cname: "ALERT",
      swaccess: "rw1c",
      hwaccess: "hrw",
      fields: [
        { bits: "0", name: "A", desc: "Cause bit ", resval: 0}
      ],
      tags: [// The value of this register is determined by triggering different kinds of alerts
             // Cannot be auto-predicted so excluded from read check
             "excl:CsrNonInitTests:CsrExclWriteCheck"]
      }
    },
##############################################################################
# local alerts
    { multireg: { name:     "LOC_ALERT_REGWEN",
                  desc:     "Register write enable for alert enable bits.",
                  count:    "NAlerts",
                  compact:  "false",
                  swaccess: "rw0c",
                  hwaccess: "none",
                  cname:    "LOC_ALERT",
                  fields: [
                    { bits:   "0",
                      name:   "EN",
                      desc:   '''
                              Alert configuration write enable bit.
                              If this is cleared to 0, the corresponding !!LOC_ALERT_EN
                              and !!LOC_ALERT_CLASS bits are not writable anymore.

                              Note that the alert pinging mechanism will only ping alerts that have been enabled and locked.
                              ''',
                      resval: "1",
                    }
                  ]
                }
    },
    { multireg: { name:     "LOC_ALERT_EN",
                  desc:     '''Enable register for the aggregated local alerts "alert
                  pingfail" (0), "escalation pingfail" (1), "alert integfail" (2) and "escalation integfail" (3).
                  ''',
                  count:    "N_LOC_ALERT",
                  compact:  "false",
                  swaccess: "rw",
                  hwaccess: "hro",
                  regwen:   "LOC_ALERT_REGWEN",
                  regwen_multi: "true",
                  cname:    "LOC_ALERT",
                  fields: [
                    { bits: "0",
                      name: "EN_LA",
                      resval: 0
                      desc: '''
                            Alert enable bit.

                            Note that the alert pinging mechanism will only ping alerts that have been enabled and locked.
                            '''
                    }
                  ]
                }
    },
    { multireg: { name:     "LOC_ALERT_CLASS",
                  desc:     '''Class assignment of local alerts. "alert
                  pingfail" (0), "escalation pingfail" (1), "alert integfail" (2) and "escalation integfail" (3).
                  ''',
                  count:    "N_LOC_ALERT",
                  compact:  "false",
                  swaccess: "rw",
                  hwaccess: "hro",
                  regwen:   "LOC_ALERT_REGWEN",
                  regwen_multi: "true",
                  cname:    "LOC_ALERT",
                  fields: [
                    {
                      bits: "CLASS_DW-1:0",
                      name: "CLASS_LA",
                      resval: 0
                      desc: "Classification ",
                      enum: [
% for i in range(n_classes):
                              { value: "${i}", name: "Class${chars[i]}", desc: "" },
% endfor
                            ]
                    }
                  ]
                }
    },
    { multireg: {
      name: "LOC_ALERT_CAUSE",
      desc: '''Alert Cause Register for Local Alerts. "alert
      pingfail" (0), "escalation pingfail" (1), "alert integfail" (2) and "escalation integfail" (3).
      ''',
      count: "N_LOC_ALERT",
      compact:  "false",
      cname: "LOC_ALERT",
      swaccess: "rw1c",
      hwaccess: "hrw",
      tags: [// Top level CSR automation test, CPU clock is disabled, so escalation response will
             // not send back to alert handler. This will set loc_alert_cause and could not predict
             // automatically.
             // TODO: remove the exclusion after set up top-level esc_receiver_driver
             "excl:CsrNonInitTests:CsrExclCheck"],
      fields: [
        { bits: "0", name: "LA", desc: "Cause bit ", resval: 0}
      ]
      }
    },
##############################################################################
# classes
% for i in range(n_classes):
<% c = chars[i] %>
    { name:     "CLASS${chars[i]}_REGWEN",
      desc:     '''
                Lock bit for Class ${chars[i]} configuration.
                '''
      swaccess: "rw0c",
      hwaccess: "none",
      fields: [
      {   bits:   "0",
          desc:   '''
                  Class configuration enable bit.
                  If this is cleared to 0, the corresponding class configuration
                  registers cannot be written anymore.
                  ''',
          resval: 1,
        }
      ]
    },
    { name:     "CLASS${chars[i]}_CTRL",
      desc:     "Escalation control register for alert Class ${chars[i]}. Can not be modified if !!CLASS${chars[i]}_REGWEN is false."
      swaccess: "rw",
      hwaccess: "hro",
      regwen:   "CLASS${chars[i]}_REGWEN",
      fields: [
        { bits: "0",
          name: "EN",
          desc: '''
                Enable escalation mechanisms (accumulation and
                interrupt timeout) for Class ${chars[i]}. Note that interrupts can fire
                regardless of whether the escalation mechanisms are enabled for
                this class or not.
                ''',
        }
        { bits: "1",
          name: "LOCK",
          desc: '''
                Enable automatic locking of escalation counter for class ${chars[i]}.
                If true, there is no way to stop the escalation protocol for class ${chars[i]}
                once it has been triggered.
                '''
        }
        { bits: "2",
          name: "EN_E0",
          resval: 1,
          desc: "Enable escalation signal 0 for Class ${chars[i]}",
        }
        { bits: "3",
          name: "EN_E1",
          resval: 1,
          desc: "Enable escalation signal 1 for Class ${chars[i]}",
        }
        { bits: "4",
          name: "EN_E2",
          resval: 1,
          desc: "Enable escalation signal 2 for Class ${chars[i]}",
        }
        { bits: "5",
          name: "EN_E3",
          resval: 1,
          desc: "Enable escalation signal 3 for Class ${chars[i]}",
        }
        # TODO: bitwidth should be parameterized with PHASE_DW
        { bits: "7:6",
          name: "MAP_E0",
          resval: 0,
          desc: "Determines in which escalation phase escalation signal 0 shall be asserted.",
        }
        { bits: "9:8",
          name: "MAP_E1",
          resval: 1,
          desc: "Determines in which escalation phase escalation signal 1 shall be asserted.",
        }
        { bits: "11:10",
          name: "MAP_E2",
          resval: 2,
          desc: "Determines in which escalation phase escalation signal 2 shall be asserted.",
        }
        { bits: "13:12",
          name: "MAP_E3",
          resval: 3,
          desc: "Determines in which escalation phase escalation signal 3 shall be asserted.",
        }
      ]
    },
    { name:     "CLASS${chars[i]}_CLR_REGWEN",
      desc:     '''
                Clear enable for escalation protocol of Class ${chars[i]} alerts.
                '''
      swaccess: "rw0c",
      hwaccess: "hwo",
      fields: [
      {   bits:   "0",
          desc:   '''Register defaults to true, can only be cleared. This register is set
          to false by the hardware if the escalation protocol has been triggered and the bit
          !!CLASS${chars[i]}_CTRL.LOCK is true.
          ''',
          resval: 1,
        }
      ],
      tags: [// The value of this register is set to false only by hardware,
             // under the condition that escalation is triggered and the corresponding lock bit is true
             // Cannot not be auto-predicted so it is excluded from read check
             "excl:CsrNonInitTests:CsrExclWriteCheck"]
    },
    { name:     "CLASS${chars[i]}_CLR",
      desc:     '''
                Clear for escalation protocol of Class ${chars[i]}.
                '''
      swaccess: "wo",
      hwaccess: "hro",
      hwqe:     "true",
      regwen:   "CLASS${chars[i]}_CLR_REGWEN",
      fields: [
        { bits: "0",
          desc: '''Writing to this register clears the accumulator and aborts escalation
          (if it has been triggered). This clear is disabled if !!CLASS${chars[i]}_CLR_REGWEN is false.
          '''
        }
      ]
    },
    { name:     "CLASS${chars[i]}_ACCUM_CNT",
      desc:     '''
                Current accumulation value for alert Class ${chars[i]}. Software can clear this register
                with a write to !!CLASS${chars[i]}_CLR register unless !!CLASS${chars[i]}_CLR_REGWEN is false.
                '''
      swaccess: "ro",
      hwaccess: "hwo",
      hwext:    "true",
      fields: [
        { bits: "${accu_cnt_dw - 1}:0" }
      ],
      tags: [// The value of this register is determined by how many alerts have been triggered
             // Cannot be auto-predicted so it is excluded from read check
             "excl:CsrNonInitTests:CsrExclWriteCheck"]
    },
    { name:     "CLASS${chars[i]}_ACCUM_THRESH",
      desc:     '''
                Accumulation threshold value for alert Class ${chars[i]}.
                '''
      swaccess: "rw",
      hwaccess: "hro",
      regwen:   "CLASS${chars[i]}_REGWEN",
      fields: [
        { bits: "${accu_cnt_dw - 1}:0",
          desc: '''Once the accumulation value register is equal to the threshold escalation will
          be triggered on the next alert occurrence within this class ${chars[i]} begins. Note that this
          register can not be modified if !!CLASS${chars[i]}_REGWEN is false.
          '''
        }
      ]
    },
    { name:     "CLASS${chars[i]}_TIMEOUT_CYC",
      desc:     '''
                Interrupt timeout in cycles.
                '''
      swaccess: "rw",
      hwaccess: "hro",
      regwen:   "CLASS${chars[i]}_REGWEN",
      fields: [
        { bits: "${esc_cnt_dw - 1}:0",
          desc: '''If the interrupt corresponding to this class is not
          handled within the specified amount of cycles, escalation will be triggered.
          Set to a positive value to enable the interrupt timeout for Class ${chars[i]}. The timeout is set to zero
          by default, which disables this feature. Note that this register can not be modified if
          !!CLASS${chars[i]}_REGWEN is false.
          '''
        }
      ]
    },
% for k in range(4):
    { name:     "CLASS${chars[i]}_PHASE${k}_CYC",
      desc:     '''
                Duration of escalation phase ${k} for Class ${chars[i]}.
                '''
      swaccess: "rw",
      hwaccess: "hro",
      regwen:   "CLASS${chars[i]}_REGWEN",
      fields: [
        { bits: "${esc_cnt_dw - 1}:0" ,
          desc: '''Escalation phase duration in cycles. Note that this register can not be
          modified if !!CLASS${chars[i]}_REGWEN is false.'''
        }
      ]
    }
% endfor
    { name:     "CLASS${chars[i]}_ESC_CNT",
      desc:     '''
                Escalation counter in cycles for Class ${chars[i]}.
                '''
      swaccess: "ro",
      hwaccess: "hwo",
      hwext:    "true",
      fields: [
        { bits: "${esc_cnt_dw - 1}:0",
          desc: '''Returns the current timeout or escalation count (depending on !!CLASS${chars[i]}_STATE).
          This register can not be directly cleared. However, SW can indirectly clear as follows.

          If the class is in the Timeout state, the timeout can be aborted by clearing the
          corresponding interrupt bit.

          If this class is in any of the escalation phases (e.g. Phase0), escalation protocol can be
          aborted by writing to !!CLASS${chars[i]}_CLR. Note however that has no effect if !!CLASS${chars[i]}_REGWEN
          is set to false (either by SW or by HW via the !!CLASS${chars[i]}_CTRL.LOCK feature).
          '''
        }
      ],
      tags: [// The value of this register is determined by counting how many cycles the escalation phase has lasted
             // Cannot be auto-predicted so excluded from read check
             "excl:CsrNonInitTests:CsrExclWriteCheck"]
    },
    { name:     "CLASS${chars[i]}_STATE",
      desc:     '''
                Current escalation state of Class ${chars[i]}. See also !!CLASS${chars[i]}_ESC_CNT.
                '''
      swaccess: "ro",
      hwaccess: "hwo",
      hwext:    "true",
      fields: [
        { bits: "2:0",
          enum: [
                  { value: "0b000", name: "Idle",     desc: "No timeout or escalation triggered." },
                  { value: "0b001", name: "Timeout",  desc: "IRQ timeout counter is active." },
                  { value: "0b011", name: "Terminal", desc: "Terminal state after escalation protocol." },
                  { value: "0b100", name: "Phase0",   desc: "Escalation Phase0 is active." },
                  { value: "0b101", name: "Phase1",   desc: "Escalation Phase1 is active." },
                  { value: "0b110", name: "Phase2",   desc: "Escalation Phase2 is active." },
                  { value: "0b111", name: "Phase3",   desc: "Escalation Phase3 is active." }
                ]
        }
      ],
      tags: [// The current escalation state cannot be auto-predicted
             // so this register is excluded from read check
             "excl:CsrNonInitTests:CsrExclWriteCheck"]
    },
% endfor
  ],
}
