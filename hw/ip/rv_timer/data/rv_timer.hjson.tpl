// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
## parameter (given by python)
##  - harts:  number of HART in timer module
##  - timers: number of timers in each hart
{
  name:               "rv_timer",
  human_name:         "RISC-V Timer",
  one_line_desc:      "Memory-mapped timer unit implementing RISC-V mtime and mtimecmp registers",
  one_paragraph_desc: '''
  RISC-V Timer provides TileLink Uncached Light (TL-UL) memory-mapped registers `mtime` and `mtimecmp` which can be used as the machine-mode timer registers as defined in the RISC-V privileged spec v1.12.
  Additional parameters can be used to add optional features, such as prescaler, step increment size, threshold-triggered interrupts, additional 64-bit timers, and support for multiple independent harts.
  '''
  // Unique comportable IP identifier defined under KNOWN_CIP_IDS in the regtool.
  cip_id:             "25",
  design_spec:        "../doc",
  dv_doc:             "../doc/dv",
  hw_checklist:       "../doc/checklist",
  sw_checklist:       "sw/device/lib/dif/dif_rv_timer",
  revisions: [
    {
      version:            "0.5.0",
      life_stage:         "L2",
      design_stage:       "D3",
      verification_stage: "V3",
      commit_id:          "a4638684103da48c793301243759e9d1eb2cb9dc",
      notes:              ""
    }
    {
      version:            "2.0.0",
      life_stage:         "L1",
      design_stage:       "D3",
      verification_stage: "V2",
      dif_stage:          "S2",
      commit_id:          "a25e162b8f91bd0ca32258c83d1d480f93327204",
      notes:              "D3 Reviewed @ 2022-07-28",
    }
  ]
  clocking: [{clock: "clk_i", reset: "rst_ni"}],
  bus_interfaces: [
    { protocol: "tlul", direction: "device" }
  ],
  available_input_list: [
  ],
  available_output_list: [
  ],
  interrupt_list: [
% for i in range(harts):
% for j in range(timers):
    { name: "timer_expired_hart${i}_timer${j}",
      desc: "raised if hart${i}'s timer${j} expired (mtimecmp >= mtime)"
    },
% endfor
% endfor
  ],
  alert_list: [
    { name: "fatal_fault",
      desc: '''
      This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected inside the RV_TIMER unit.
      '''
    }
  ],
  param_list: [
    { name: "N_HARTS",
      desc: "Number of harts",
      type: "int",
      default: "${harts}"
    },
    { name: "N_TIMERS",
      desc: "Number of timers per Hart",
      type: "int",
      default: "${timers}"
    }
  ],
  no_auto_intr_regs: "true",
  countermeasures: [
    { name: "BUS.INTEGRITY"
      desc: "End-to-end bus integrity scheme."
    }
  ]
  regwidth: "32",
  registers: [
    { multireg: {
        name: "CTRL",
        desc: "Control register",
        count: "N_HARTS",
        cname: "TIMER",
        swaccess: "rw",
        hwaccess: "hro",
        fields: [
          { bits: "0", name: "active",
            desc: "If 1, timer operates",
            tags: [// prevent timer from being enabled
                   "excl:CsrNonInitTests:CsrExclWrite"] }
        ],
      }
    },
% for i in range(harts):
    { skipto: "${"0x%x" % (256*(i+1))}" },
    { multireg: {
        name: "INTR_ENABLE${i}",
        desc: "Interrupt Enable",
        count: "N_TIMERS",
        cname: "TIMER",
        swaccess: "rw",
        hwaccess: "hro",
        fields: [
          { bits: "0", name: "IE", desc: "Interrupt Enable for timer" }
        ]
      }
    }, // R: INTR_ENABLE${i}
    { multireg: {
        name: "INTR_STATE${i}",
        desc: "Interrupt Status",
        count: "N_TIMERS",
        cname: "TIMER",
        swaccess: "rw1c",
        hwaccess: "hrw",
        fields: [
          { bits: "0", name: "IS", desc: "Interrupt status for timer",
            tags: [// intr_state csr is affected by writes to other csrs - skip write-check
                   "excl:CsrNonInitTests:CsrExclWriteCheck"] }
        ],
      }
    }, // R: INTR_STATE${i}
    { multireg: {
        name: "INTR_TEST${i}",
        desc: "Interrupt test register",
        count: "N_TIMERS",
        cname: "TIMER",
        swaccess: "wo",
        hwaccess: "hro",
        hwext: "true",
        hwqe: "true",
        fields: [
          { bits: "0", name: "T", desc: "Interrupt test for timer",
            tags: [// intr_test csr is WO which - it reads back 0s
                   "excl:CsrNonInitTests:CsrExclWrite"] }
        ]
      }
    }, // R: INTR_TEST${i}
    { name: "CFG${i}",
      desc: "Configuration for Hart ${i}",
      swaccess: "rw",
      hwaccess: "hro",
      fields: [
        { bits: "11:0", name: "prescale", desc: "Prescaler to generate tick" },
        { bits: "23:16", name: "step", resval: "0x1", desc: "Incremental value for each tick" },
      ],
    },
    { name: "TIMER_V_LOWER${i}",
      desc: "Timer value Lower",
      swaccess: "rw",
      hwaccess: "hrw",
      fields: [
        { bits: "31:0", name: "v", desc: "Timer value [31:0]" },
      ],
    },
    { name: "TIMER_V_UPPER${i}",
      desc: "Timer value Upper",
      swaccess: "rw",
      hwaccess: "hrw",
      fields: [
        { bits: "31:0", name: "v", desc: "Timer value [63:32]" },
      ],
    },
% for j in range(timers):
    { name: "COMPARE_LOWER${i}_${j}",
      desc: "Timer value Lower",
      swaccess: "rw",
      hwaccess: "hro",
      hwqe: "true",
      fields: [
        { bits: "31:0", name: "v", resval: "0xffffffff", desc: "Timer compare value [31:0]" },
      ],
    },
    { name: "COMPARE_UPPER${i}_${j}",
      desc: "Timer value Upper",
      swaccess: "rw",
      hwaccess: "hro",
      hwqe: "true",
      fields: [
        { bits: "31:0", name: "v", resval: "0xffffffff", desc: "Timer compare value [63:32]" },
      ],
    },
% endfor
% endfor
  ],
}
