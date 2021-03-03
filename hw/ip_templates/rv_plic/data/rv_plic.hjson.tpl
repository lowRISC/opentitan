// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
<% import math %>\
# RV_PLIC register template
#
# Parameter (given by Python tool)
#  - src:    Number of Interrupt Sources
#  - target: Number of Targets that handle interrupt requests
#  - prio:   Max value of interrupt priorities
{
  name: "RV_PLIC",
  clock_primary: "clk_i",
  bus_interfaces: [
    { protocol: "tlul", direction: "device" }
  ],

  param_list: [
    { name: "NumSrc",
      desc: "Number of interrupt sources",
      type: "int",
      default: "${src}",
      local: "true"
    },
    { name: "NumTarget",
      desc: "Number of Targets (Harts)",
      type: "int",
      default: "${target}",
      local: "true",
    },
    { name: "PrioWidth",
      desc: "Width of priority signals",
      type: "int",
      default: "${(prio).bit_length()}",
      local: "true",
    },
  ],
  regwidth: "32",
  registers: [
    { multireg: {
        name: "IP",
        desc: "Interrupt Pending",
        count: "NumSrc",
        cname: "RV_PLIC",
        swaccess: "ro",
        hwaccess: "hwo",
        fields: [
          { bits: "0", name: "P", desc: "Interrupt Pending of Source" }
        ],
        tags: [// IP is driven by intr_src, cannot auto-predict
               "excl:CsrNonInitTests:CsrExclCheck"],
      }
    },
    { multireg: {
        name: "LE",
        desc: "Interrupt Source mode. 0: Level, 1: Edge-triggered",
        count: "NumSrc",
        cname: "RV_PLIC",
        swaccess: "rw",
        hwaccess: "hro",
        fields: [
          { bits: "0", name: "LE", desc: "L0E1" }
        ],
      }
    },
% for i in range(src):
    { name: "PRIO${i}",
      desc: "Interrupt Source ${i} Priority",
      swaccess: "rw",
      hwaccess: "hro",
      fields: [
        { bits: "${(prio).bit_length()-1}:0" }
      ],
    }
% endfor
% for i in range(target):
    { skipto: "${0x100*(math.ceil((src*4+8*math.ceil(src/32))/0x100)) + i*0x100 | x}" }
    { multireg: {
        name: "IE${i}",
        desc: "Interrupt Enable for Target ${i}",
        count: "NumSrc",
        cname: "RV_PLIC",
        swaccess: "rw",
        hwaccess: "hro",
        fields: [
          { bits: "0", name: "E", desc: "Interrupt Enable of Source" }
        ],
      }
    }
    { name: "THRESHOLD${i}",
      desc: "Threshold of priority for Target ${i}",
      swaccess: "rw",
      hwaccess: "hro",
      fields: [
        { bits: "${(prio).bit_length()-1}:0" }
      ],
    }
    { name: "CC${i}",
      desc: '''Claim interrupt by read, complete interrupt by write for Target ${i}.
      Value read/written is interrupt ID. Reading a value of 0 means no pending interrupts.''',
      swaccess: "rw",
      hwaccess: "hrw",
      hwext: "true",
      hwqe: "true",
      hwre: "true",
      fields: [
        { bits: "${(src).bit_length()-1}:0" }
      ],
      tags: [// CC register value is related to IP
             "excl:CsrNonInitTests:CsrExclCheck"],
    }
    { name: "MSIP${i}",
      desc: '''msip for Hart ${i}.
      Write 1 to here asserts software interrupt for Hart msip_o[${i}], write 0 to clear.''',
      swaccess: "rw",
      hwaccess: "hro",
      fields: [
        { bits: "0",
          desc: "Software Interrupt Pending register",
        }
      ],
    }
% endfor
  ],
}
