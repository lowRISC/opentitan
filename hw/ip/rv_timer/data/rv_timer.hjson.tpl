// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
## parameter (given by python)
##  - harts:  number of HART in timer module
##  - timers: number of timers in each hart
{ name: "rv_timer",
  clock_primary: "clk_i",
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
    { name: "timer_expired_${i}_${j}",
      desc: "raised if the timer ${i}_${j} expired (mtimecmp >= mtime)"
    },
% endfor
% endfor
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
          { bits: "0", name: "active", desc: "If 1, timer operates" }
        ],
      }
    },
% for i in range(harts):
    { skipto: "${"0x%x" % (256*(i+1))}" },
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
    },
    { multireg: {
        name: "INTR_STATE${i}",
        desc: "Interrupt Status",
        count: "N_TIMERS",
        cname: "TIMER",
        swaccess: "rw1c",
        hwaccess: "hrw",
        fields: [
          { bits: "0", name: "IS", desc: "Interrupt status for timer" }
        ],
      }
    },
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
          { bits: "0", name: "T", desc: "Interrupt test for timer" }
        ]
      }
    },
% endfor
  ],
}
