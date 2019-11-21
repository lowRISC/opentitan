// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
# PINMUX register template
#
# Parameter (given by Python tool)
#  - n_periph_in:     Number of peripheral inputs
#  - n_periph_out:    Number of peripheral outputs
#  - n_mio_pads:      Number of muxed IO pads
# <% import math %>
{
  name: "PINMUX",
  clock_primary: "clk_i",
  bus_device: "tlul",
  regwidth: "32",
  param_list: [
    { name: "NPeriphIn",
      desc: "Number of peripheral inputs",
      type: "int",
      default: "${n_periph_in}",
      local: "true"
    },
    { name: "NPeriphOut",
      desc: "Number of peripheral outputs",
      type: "int",
      default: "${n_periph_out}",
      local: "true"
    },
    { name: "NMioPads",
      desc: "Number of muxed IO pads",
      type: "int",
      default: "${n_mio_pads}",
      local: "true"
    },
  ],
  registers: [
    { name: "REGEN",
      desc: '''
            Register write enable for all control registers.
            ''',
      swaccess: "rw0c",
      hwaccess: "none",
      fields: [
        {
            bits:   "0",
            name: "wen",
            desc: ''' When true, all configuration registers can be modified.
            When false, they become read-only. Defaults true, write zero to clear.
            '''
            resval: 1,
        },
      ]
    },
# inputs
    { multireg: { name:     "PERIPH_INSEL",
                  desc:     "Mux select for peripheral inputs.",
                  count:    "NPeriphIn",
                  swaccess: "rw",
                  hwaccess: "hro",
                  regwen:   "REGEN",
                  cname:    "IN",
                  fields: [
                    { bits: "${(n_mio_pads+1).bit_length()-1}:0",
                      name: "IN",
                      desc: '''
                      0: tie constantly to zero, 1: tie constantly to 1.
                      >=2: MIO pads (i.e., add 2 to the native MIO pad index).
                      '''
                      resval: 0
                    }
                  ]
                }
    },
# outputs
    { multireg: { name:     "MIO_OUTSEL",
                  desc:     "Mux select for MIO outputs.",
                  count:    "NMioPads",
                  swaccess: "rw",
                  hwaccess: "hro",
                  regwen:   "REGEN",
                  cname:    "OUT",
                  fields: [
                    { bits: "${(n_periph_out+2).bit_length()-1}:0",
                      name: "OUT",
                      desc: '''
                      0: tie constantly to zero, 1: tie constantly to 1. 2: high-Z
                      >=3: peripheral outputs (i.e., add 3 to the native peripheral pad index).
                      '''
                      resval: 2
                    }
                  ]
                }
    },
  ],
}
