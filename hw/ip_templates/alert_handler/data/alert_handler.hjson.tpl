// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
# ALERT_HANDLER register template
<%
import math
chars = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H']
%>
{
  name:               "alert_handler",
  // Unique comportable IP identifier defined under KNOWN_CIP_IDS in the regtool.
  cip_id:             "32",
  design_spec:        "../doc",
  dv_doc:             "../doc/dv",
  hw_checklist:       "../doc/checklist",
  sw_checklist:       "/sw/device/lib/dif/dif_alert_handler"
  version:            "1.0.0",
  life_stage:         "L1",
  design_stage:       "D3",
  verification_stage: "V2S",
  dif_stage:          "S2",
  notes:              "Use both FPV and DV to perform block level verification.",
  clocking: [
    {clock: "clk_i", reset: "rst_ni", primary: true},
    {clock: "clk_edn_i", reset: "rst_edn_ni"}
  ]
  bus_interfaces: [
    { protocol: "tlul", direction: "device", hier_path: "u_reg_wrap.u_reg" }
  ],
  regwidth: "32",
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
      desc: "Number of alert channels.",
      type: "int",
      default: "${n_alerts}",
      local: "true"
    },
    { name: "NLpg",
      desc: "Number of LPGs.",
      type: "int",
      default: "${n_lpg}",
      local: "true"
    },
    { name: "NLpgWidth",
      desc: "Width of LPG ID.",
      type: "int",
      default: "${n_lpg.bit_length()}",
      local: "true"
    },
    { name: "LpgMap",
      desc: '''
            Defines a mapping from alerts to LPGs.
            '''
      type: "logic [NAlerts-1:0][NLpgWidth-1:0]",
      default: '''
% if lpg_map:
               {
  % for l in list(reversed(lpg_map)):
                 ${l}${"" if loop.last else ","}
  % endfor
               }
% else:
               '0
% endif
               ''',
      local: "true"
    },
    { name: "EscCntDw",
      desc: "Width of the escalation timer.",
      type: "int",
      default: "${esc_cnt_dw}",
      local: "true"
    },
    { name: "AccuCntDw",
      desc: "Width of the accumulation counter.",
      type: "int",
      default: "${accu_cnt_dw}",
      local: "true"
    },
    { name: "AsyncOn",
      desc: '''
            Each bit of this parameter corresponds to an escalation channel and
            defines whether the protocol is synchronous (0) or asynchronous (1).
            '''
      type: "logic [NAlerts-1:0]",
      default: '''
% if async_on:
               {
  % for a in list(reversed(async_on)):
                 ${a}${"" if loop.last else ","}
  % endfor
               }
% else:
               '0
% endif
               '''
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
      desc: "Number of local alerts",
      type: "int",
      default: "7",
      local: "true"
    },
    { name: "PING_CNT_DW",
      desc: "Width of ping counter",
      type: "int",
      default: "16",
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
    { name: "LOCAL_ALERT_ID_ALERT_PINGFAIL",
      desc: "Local alert ID for alert ping failure.",
      type: "int",
      default: "0",
      local: "true"
    },
    { name: "LOCAL_ALERT_ID_ESC_PINGFAIL",
      desc: "Local alert ID for escalation ping failure.",
      type: "int",
      default: "1",
      local: "true"
    },
    { name: "LOCAL_ALERT_ID_ALERT_INTEGFAIL",
      desc: "Local alert ID for alert integrity failure.",
      type: "int",
      default: "2",
      local: "true"
    },
    { name: "LOCAL_ALERT_ID_ESC_INTEGFAIL",
      desc: "Local alert ID for escalation integrity failure.",
      type: "int",
      default: "3",
      local: "true"
    },
    { name: "LOCAL_ALERT_ID_BUS_INTEGFAIL",
      desc: "Local alert ID for bus integrity failure.",
      type: "int",
      default: "4",
      local: "true"
    },
    { name: "LOCAL_ALERT_ID_SHADOW_REG_UPDATE_ERROR",
      desc: "Local alert ID for shadow register update error.",
      type: "int",
      default: "5",
      local: "true"
    },
    { name: "LOCAL_ALERT_ID_SHADOW_REG_STORAGE_ERROR",
      desc: "Local alert ID for shadow register storage error.",
      type: "int",
      default: "6",
      local: "true"
    },
    { name: "LOCAL_ALERT_ID_LAST",
      desc: "Last local alert ID.",
      type: "int",
      default: "6",
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

  features: [
    { name: "ALERT_HANDLER.ALERT.OBSERVE",
      desc: '''
                All incoming alerts can be observed by the alert handler.
            '''
    }
    { name: "ALERT_HANDLER.ALERT.INTERRUPT",
      desc: '''
                All alert classes can raise an interrupt when an alert that is
                allocated to them is raised.
            '''
    }
    { name: "ALERT_HANDLER.ALERT.ESCALATE",
      desc: '''
               All incoming alerts can trigger the alert escalation mechanisms
               of the classes they are allocated to
            '''
    }
    {
      name: "ALERT_HANDLER.PING_TIMER",
      desc: '''
                The alert handler periodically pings all alert receivers and
                will raise an alert if the ping isn't responded to in good time
             '''
    }
    { name: "ALERT_HANDLER.ESCALATION.COUNT",
      desc: '''
                An escalation can be triggered when the number of alerts seen in
                a particular class exceeds a software programmable threshold
            '''
    }
    { name: "ALERT_HANDLER.ESCALATION.TIMEOUT",
      desc: '''
                An escalation can be triggered when an interrupt from a class
                isn't acknowledged after a software programmable timeout
            '''
    }
    { name: "ALERT_HANDLER.ESCALATION.PHASES",
      desc: '''
               Each alert class can trigger the same 4 escalation phases. A
               programmable timer specifies the delay between each of the
               escalation phases. The actions taken on each of the escalation
               signals are specific to the top-level integration.
            '''
    }
    {
      name: "ALERT_HANDLER.CRASH_DUMP",
      desc: '''
               A crashdump with the state of CSRs and alert handler state bits
               is made available. When a programmable latching trigger condition
               is met the crashdump is held constant at its value on that
               trigger condition so it can be recorded and made available for
               later analysis
            '''
    }
  ]

  countermeasures: [
    { name: "BUS.INTEGRITY",
      desc: "End-to-end bus integrity scheme."
    }
    { name: "CONFIG.SHADOW",
      desc: "Important CSRs are shadowed."
    }
    { name: "PING_TIMER.CONFIG.REGWEN",
      desc: "The ping timer configuration registers are REGWEN protected."
    }
    { name: "ALERT.CONFIG.REGWEN",
      desc: "The individual alert enables are REGWEN protected."
    }
    { name: "ALERT_LOC.CONFIG.REGWEN",
      desc: "The individual local alert enables are REGWEN protected."
    }
    { name: "CLASS.CONFIG.REGWEN",
      desc: "The class configuration registers are REGWEN protected."
    }
    { name: "ALERT.INTERSIG.DIFF",
      desc: "Differentially encoded alert channels."
    }
    { name: "LPG.INTERSIG.MUBI",
      desc: "LPG signals are encoded with MUBI types."
    }
    { name: "ESC.INTERSIG.DIFF",
      desc: "Differentially encoded escalation channels."
    }
    { name: "ALERT_RX.INTERSIG.BKGN_CHK",
      desc: "Periodic background checks on alert channels (ping mechanism)."
    }
    { name: "ESC_TX.INTERSIG.BKGN_CHK",
      desc: "Periodic background checks on escalation channels (ping mechanism)."
    }
    { name: "ESC_RX.INTERSIG.BKGN_CHK",
      desc: "Escalation receivers can detect absence of periodic ping requests."
    }
    { name: "ESC_TIMER.FSM.SPARSE",
      desc: "Escalation timer FSMs are sparsely encoded."
    }
    { name: "PING_TIMER.FSM.SPARSE",
      desc: "Ping timer FSM is sparsely encoded."
    }
    { name: "ESC_TIMER.FSM.LOCAL_ESC",
      desc: "Escalation timer FSMs move into an invalid state upon local escalation."
    }
    { name: "PING_TIMER.FSM.LOCAL_ESC",
      desc: "Ping timer FSM moves into an invalid state upon local escalation."
    }
    { name: "ESC_TIMER.FSM.GLOBAL_ESC",
      desc: '''
            The escalation timer FSMs are the root of global escalation,
            hence if any of them moves into an invalid state by virtue of
            ESC_TIMER.FSM.LOCAL_ESC, this will trigger all escalation actions
            and thereby global escalation as well.
            '''
    }
    { name: "ACCU.CTR.REDUN",
      desc: "Accumulator counters employ a cross-counter implementation."
    }
    { name: "ESC_TIMER.CTR.REDUN",
      desc: "Escalation timer counters employ a duplicated counter implementation."
    }
    { name: "PING_TIMER.CTR.REDUN",
      desc: "Ping timer counters employ a duplicated counter implementation."
    }
    { name: "PING_TIMER.LFSR.REDUN",
      desc: "Ping timer LFSR is redundant."
    }
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
            Register write enable for !!PING_TIMEOUT_CYC_SHADOWED and !!PING_TIMER_EN_SHADOWED.
            ''',
      swaccess: "rw0c",
      hwaccess: "none",
      fields: [
        {
            bits:   "0",
            desc: '''
            When true, the !!PING_TIMEOUT_CYC_SHADOWED and !!PING_TIMER_EN_SHADOWED registers can be modified.
            When false, they become read-only. Defaults true, write one to clear.
            This should be cleared once the alert handler has been configured and the ping
            timer mechanism has been kicked off.
            '''
            resval: 1,
        },
      ]
    },
    { name:     "PING_TIMEOUT_CYC_SHADOWED",
      desc:     '''
                Ping timeout cycle count.
                '''
      shadowed: "true",
      swaccess: "rw",
      hwaccess: "hro",
      regwen:   "PING_TIMER_REGWEN",
      fields: [
        {
          bits: "PING_CNT_DW-1:0",
          resval:   256,
          desc: '''
          Timeout value in cycles.
          If an alert receiver or an escalation sender does not respond to a ping within this timeout window, a pingfail alert will be raised.
          It is recommended to set this value to the equivalent of 256 cycles of the slowest alert sender clock domain in the system (or greater).
          '''
        }
      ]
    }
    { name:     "PING_TIMER_EN_SHADOWED",
      desc:     '''
                Ping timer enable.
                '''
      shadowed: "true",
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
                              If this is cleared to 0, the corresponding !!ALERT_EN_SHADOWED
                              and !!ALERT_CLASS_SHADOWED bits are not writable anymore.

                              Note that the alert pinging mechanism will only ping alerts that have been enabled and locked.
                              ''',
                      resval: "1",
                    }
                  ]
                }
    },
    { multireg: { name:     "ALERT_EN_SHADOWED",
                  desc:     '''Enable register for alerts.
                  ''',
                  count:    "NAlerts",
                  shadowed: "true",
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
    { multireg: { name:     "ALERT_CLASS_SHADOWED",
                  desc:     '''Class assignment of alerts.
                  ''',
                  count:    "NAlerts",
                  shadowed: "true",
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
      }
    },
##############################################################################
# local alerts
    { multireg: { name:     "LOC_ALERT_REGWEN",
                  desc:     "Register write enable for alert enable bits.",
                  count:    "N_LOC_ALERT",
                  compact:  "false",
                  swaccess: "rw0c",
                  hwaccess: "none",
                  cname:    "LOC_ALERT",
                  fields: [
                    { bits:   "0",
                      name:   "EN",
                      desc:   '''
                              Alert configuration write enable bit.
                              If this is cleared to 0, the corresponding !!LOC_ALERT_EN_SHADOWED
                              and !!LOC_ALERT_CLASS_SHADOWED bits are not writable anymore.

                              Note that the alert pinging mechanism will only ping alerts that have been enabled and locked.
                              ''',
                      resval: "1",
                    }
                  ]
                }
    },
    { multireg: { name:     "LOC_ALERT_EN_SHADOWED",
                  desc:
                  '''
                  Enable register for the local alerts
                  "alert pingfail" (0), "escalation pingfail" (1),
                  "alert integfail" (2), "escalation integfail" (3),
                  "bus integrity failure" (4), "shadow reg update error" (5)
                  and "shadow reg storage error" (6).
                  ''',
                  count:    "N_LOC_ALERT",
                  shadowed: "true",
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
    { multireg: { name:     "LOC_ALERT_CLASS_SHADOWED",
                  desc:     '''
                  Class assignment of the local alerts
                  "alert pingfail" (0), "escalation pingfail" (1),
                  "alert integfail" (2), "escalation integfail" (3),
                  "bus integrity failure" (4), "shadow reg update error" (5)
                  and "shadow reg storage error" (6).
                  ''',
                  count:    "N_LOC_ALERT",
                  shadowed: "true",
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
      desc: '''Alert Cause Register for the local alerts
      "alert pingfail" (0), "escalation pingfail" (1),
      "alert integfail" (2), "escalation integfail" (3),
      "bus integrity failure" (4), "shadow reg update error" (5)
      and "shadow reg storage error" (6).
      ''',
      count: "N_LOC_ALERT",
      compact:  "false",
      cname: "LOC_ALERT",
      swaccess: "rw1c",
      hwaccess: "hrw",
      tags: [// Top level CSR automation test, CPU clock is disabled, so escalation response will
             // not send back to alert handler. This will set loc_alert_cause and could not predict
             // automatically.
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
    { name:     "CLASS${chars[i]}_CTRL_SHADOWED",
      desc:     "Escalation control register for alert Class ${chars[i]}. Can not be modified if !!CLASS${chars[i]}_REGWEN is false."
      swaccess: "rw",
      hwaccess: "hro",
      regwen:   "CLASS${chars[i]}_REGWEN",
      shadowed: "true",
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
          !!CLASS${chars[i]}_CTRL_SHADOWED.LOCK is true.
          ''',
          resval: 1,
        }
      ],
      tags: [// The value of this register is set to false only by hardware, under the condition
             // that escalation is triggered and the corresponding lock bit is true
             // Cannot not be auto-predicted so it is excluded from read check
             "excl:CsrNonInitTests:CsrExclWriteCheck"]
    },
    { name:     "CLASS${chars[i]}_CLR_SHADOWED",
      desc:     '''
                Clear for escalation protocol of Class ${chars[i]}.
                '''
      swaccess: "rw",
      hwaccess: "hro",
      hwqe:     "true",
      shadowed: "true",
      regwen:   "CLASS${chars[i]}_CLR_REGWEN",
      fields: [
        { bits: "0",
          desc: '''Writing 1 to this register clears the accumulator and aborts escalation
          (if it has been triggered). This clear is disabled if !!CLASS${chars[i]}_CLR_REGWEN is false.
          '''
        }
      ]
    },
    { name:     "CLASS${chars[i]}_ACCUM_CNT",
      desc:     '''
                Current accumulation value for alert Class ${chars[i]}. Software can clear this register
                with a write to !!CLASS${chars[i]}_CLR_SHADOWED register unless !!CLASS${chars[i]}_CLR_REGWEN is false.
                '''
      swaccess: "ro",
      hwaccess: "hwo",
      hwext:    "true",
      fields: [
        { bits: "AccuCntDw-1:0" }
      ],
      tags: [// The value of this register is determined by how many alerts have been triggered
             // Cannot be auto-predicted so it is excluded from read check
             "excl:CsrNonInitTests:CsrExclWriteCheck"]
    },
    { name:     "CLASS${chars[i]}_ACCUM_THRESH_SHADOWED",
      desc:     '''
                Accumulation threshold value for alert Class ${chars[i]}.
                '''
      swaccess: "rw",
      hwaccess: "hro",
      shadowed: "true",
      regwen:   "CLASS${chars[i]}_REGWEN",
      fields: [
        { bits: "AccuCntDw-1:0",
          desc: '''Once the accumulation value register is equal to the threshold escalation will
          be triggered on the next alert occurrence within this class ${chars[i]} begins. Note that this
          register can not be modified if !!CLASS${chars[i]}_REGWEN is false.
          '''
        }
      ]
    },
    { name:     "CLASS${chars[i]}_TIMEOUT_CYC_SHADOWED",
      desc:     '''
                Interrupt timeout in cycles.
                '''
      swaccess: "rw",
      hwaccess: "hro",
      shadowed: "true",
      regwen:   "CLASS${chars[i]}_REGWEN",
      fields: [
        { bits: "EscCntDw-1:0",
          desc: '''If the interrupt corresponding to this class is not
          handled within the specified amount of cycles, escalation will be triggered.
          Set to a positive value to enable the interrupt timeout for Class ${chars[i]}. The timeout is set to zero
          by default, which disables this feature. Note that this register can not be modified if
          !!CLASS${chars[i]}_REGWEN is false.
          '''
        }
      ]
    },
    { name:     "CLASS${chars[i]}_CRASHDUMP_TRIGGER_SHADOWED",
      desc:     '''
                Crashdump trigger configuration for Class ${chars[i]}.
                '''
      swaccess: "rw",
      hwaccess: "hro",
      shadowed: "true",
      regwen:   "CLASS${chars[i]}_REGWEN",
      resval:   "0",
      fields: [
        { bits: "PHASE_DW-1:0",
          desc: '''
          Determine in which escalation phase to capture the crashdump containing all alert cause CSRs and escalation
          timer states. It is recommended to capture the crashdump upon entering the first escalation phase
          that activates a countermeasure with many side-effects (e.g. life cycle state scrapping) in order
          to prevent spurious alert events from masking the original alert causes.
          Note that this register can not be modified if !!CLASS${chars[i]}_REGWEN is false.
          '''
        }
      ]
    },
% for k in range(4):
    { name:     "CLASS${chars[i]}_PHASE${k}_CYC_SHADOWED",
      desc:     '''
                Duration of escalation phase ${k} for Class ${chars[i]}.
                '''
      swaccess: "rw",
      hwaccess: "hro",
      shadowed: "true",
      regwen:   "CLASS${chars[i]}_REGWEN",
      fields: [
        { bits: "EscCntDw-1:0" ,
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
        { bits: "EscCntDw-1:0",
          desc: '''Returns the current timeout or escalation count (depending on !!CLASS${chars[i]}_STATE).
          This register can not be directly cleared. However, SW can indirectly clear as follows.

          If the class is in the Timeout state, the timeout can be aborted by clearing the
          corresponding interrupt bit.

          If this class is in any of the escalation phases (e.g. Phase0), escalation protocol can be
          aborted by writing to !!CLASS${chars[i]}_CLR_SHADOWED. Note however that has no effect if !!CLASS${chars[i]}_REGWEN
          is set to false (either by SW or by HW via the !!CLASS${chars[i]}_CTRL_SHADOWED.LOCK feature).
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
                  { value: "0b010", name: "FsmError", desc: "Terminal error state if FSM has been glitched." },
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
