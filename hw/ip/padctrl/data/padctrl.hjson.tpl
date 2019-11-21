// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
# PADCTRL register template
#
# Parameter (given by Python tool)
#  - n_dio_pads:      Number of dedicated IO pads
#  - n_mio_pads:      Number of muxed IO pads
#  - attr_dw:        Attribute datawidth
{
  name: "PADCTRL",
  clock_primary: "clk_fixed",
  bus_device: "tlul",
  regwidth: "32",
  param_list: [
    { name: "NDioPads",
      desc: "Number of dedicated IO pads",
      type: "int",
      default: "${n_dio_pads}",
      local: "true"
    },
    { name: "NMioPads",
      desc: "Number of muxed IO pads",
      type: "int",
      default: "${n_mio_pads}",
      local: "true"
    },
    { name: "AttrDw",
      desc: "Pad attribute data width",
      type: "int",
      default: "${attr_dw}",
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
            desc: ''' When true, all configuration registers can be modified.
            When false, they become read-only. Defaults true, write zero to clear.
            '''
            resval: 1,
        },
      ]
    },
# dedicated pads
    { multireg: { name:     "DIO_PADS",
                  desc:     '''Dedicated pad attributes.
                  This register has WARL behavior as some attributes may not be implemented.
                  ''',
                  count:    "NDioPads",
                  swaccess: "rw",
                  hwaccess: "hrw",
                  hwext:    "true",
                  regwen:   "REGEN",
                  cname:    "ATTR",
                  fields: [
                    { bits: "${attr_dw-1}:0",
                      name: "ATTR",
                      desc: '''Bit 0: input/output inversion,
                               Bit 1: Virtual open drain enable.
                               Bit 2: Pull-down enable.
                               Bit 3: Pull-up enable.
                               Bit 4: Keeper enable.
                               Bit 5: Drive strength (0: strong, 1: weak).
                      '''
                      resval: 0
                    }
                  ]
                }
    },
# muxed pads
    { multireg: { name:     "MIO_PADS",
                  desc:     '''Muxed pad attributes.
                  This register has WARL behavior as some attributes may not be implemented.
                  ''',
                  count:    "NMioPads",
                  swaccess: "rw",
                  hwaccess: "hrw",
                  hwext:    "true",
                  regwen:   "REGEN",
                  cname:    "ATTR",
                  fields: [
                    { bits: "${attr_dw-1}:0",
                      name: "ATTR",
                      desc: '''Bit 0: input/output inversion,
                               Bit 1: Virtual open drain enable.
                               Bit 2: Pull-down enable.
                               Bit 3: Pull-up enable.
                               Bit 4: Keeper enable.
                               Bit 5: Drive strength (0: strong, 1: weak).
                      '''
                      resval: 0
                    }
                  ]
                }
    },
  ],
}


