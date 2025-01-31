# Registers

A number of memory-mapped registers are available to control Ibex-related functionality that's specific to OpenTitan.

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/top_darjeeling/ip_autogen/rv_core_ibex/data/rv_core_ibex.hjson -->
## Summary

| Name                                                        | Offset   |   Length | Description                                          |
|:------------------------------------------------------------|:---------|---------:|:-----------------------------------------------------|
| rv_core_ibex.[`ALERT_TEST`](#alert_test)                    | 0x0      |        4 | Alert Test Register                                  |
| rv_core_ibex.[`SW_RECOV_ERR`](#sw_recov_err)                | 0x4      |        4 | Software recoverable error                           |
| rv_core_ibex.[`SW_FATAL_ERR`](#sw_fatal_err)                | 0x8      |        4 | Software fatal error                                 |
| rv_core_ibex.[`IBUS_REGWEN_0`](#ibus_regwen)                | 0xc      |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_1`](#ibus_regwen)                | 0x10     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_2`](#ibus_regwen)                | 0x14     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_3`](#ibus_regwen)                | 0x18     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_4`](#ibus_regwen)                | 0x1c     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_5`](#ibus_regwen)                | 0x20     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_6`](#ibus_regwen)                | 0x24     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_7`](#ibus_regwen)                | 0x28     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_8`](#ibus_regwen)                | 0x2c     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_9`](#ibus_regwen)                | 0x30     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_10`](#ibus_regwen)               | 0x34     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_11`](#ibus_regwen)               | 0x38     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_12`](#ibus_regwen)               | 0x3c     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_13`](#ibus_regwen)               | 0x40     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_14`](#ibus_regwen)               | 0x44     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_15`](#ibus_regwen)               | 0x48     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_16`](#ibus_regwen)               | 0x4c     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_17`](#ibus_regwen)               | 0x50     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_18`](#ibus_regwen)               | 0x54     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_19`](#ibus_regwen)               | 0x58     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_20`](#ibus_regwen)               | 0x5c     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_21`](#ibus_regwen)               | 0x60     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_22`](#ibus_regwen)               | 0x64     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_23`](#ibus_regwen)               | 0x68     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_24`](#ibus_regwen)               | 0x6c     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_25`](#ibus_regwen)               | 0x70     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_26`](#ibus_regwen)               | 0x74     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_27`](#ibus_regwen)               | 0x78     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_28`](#ibus_regwen)               | 0x7c     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_29`](#ibus_regwen)               | 0x80     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_30`](#ibus_regwen)               | 0x84     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_31`](#ibus_regwen)               | 0x88     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_ADDR_EN_0`](#ibus_addr_en)              | 0x8c     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_1`](#ibus_addr_en)              | 0x90     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_2`](#ibus_addr_en)              | 0x94     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_3`](#ibus_addr_en)              | 0x98     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_4`](#ibus_addr_en)              | 0x9c     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_5`](#ibus_addr_en)              | 0xa0     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_6`](#ibus_addr_en)              | 0xa4     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_7`](#ibus_addr_en)              | 0xa8     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_8`](#ibus_addr_en)              | 0xac     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_9`](#ibus_addr_en)              | 0xb0     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_10`](#ibus_addr_en)             | 0xb4     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_11`](#ibus_addr_en)             | 0xb8     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_12`](#ibus_addr_en)             | 0xbc     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_13`](#ibus_addr_en)             | 0xc0     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_14`](#ibus_addr_en)             | 0xc4     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_15`](#ibus_addr_en)             | 0xc8     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_16`](#ibus_addr_en)             | 0xcc     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_17`](#ibus_addr_en)             | 0xd0     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_18`](#ibus_addr_en)             | 0xd4     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_19`](#ibus_addr_en)             | 0xd8     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_20`](#ibus_addr_en)             | 0xdc     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_21`](#ibus_addr_en)             | 0xe0     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_22`](#ibus_addr_en)             | 0xe4     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_23`](#ibus_addr_en)             | 0xe8     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_24`](#ibus_addr_en)             | 0xec     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_25`](#ibus_addr_en)             | 0xf0     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_26`](#ibus_addr_en)             | 0xf4     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_27`](#ibus_addr_en)             | 0xf8     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_28`](#ibus_addr_en)             | 0xfc     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_29`](#ibus_addr_en)             | 0x100    |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_30`](#ibus_addr_en)             | 0x104    |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_31`](#ibus_addr_en)             | 0x108    |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_0`](#ibus_addr_matching)  | 0x10c    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_1`](#ibus_addr_matching)  | 0x110    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_2`](#ibus_addr_matching)  | 0x114    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_3`](#ibus_addr_matching)  | 0x118    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_4`](#ibus_addr_matching)  | 0x11c    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_5`](#ibus_addr_matching)  | 0x120    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_6`](#ibus_addr_matching)  | 0x124    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_7`](#ibus_addr_matching)  | 0x128    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_8`](#ibus_addr_matching)  | 0x12c    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_9`](#ibus_addr_matching)  | 0x130    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_10`](#ibus_addr_matching) | 0x134    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_11`](#ibus_addr_matching) | 0x138    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_12`](#ibus_addr_matching) | 0x13c    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_13`](#ibus_addr_matching) | 0x140    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_14`](#ibus_addr_matching) | 0x144    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_15`](#ibus_addr_matching) | 0x148    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_16`](#ibus_addr_matching) | 0x14c    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_17`](#ibus_addr_matching) | 0x150    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_18`](#ibus_addr_matching) | 0x154    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_19`](#ibus_addr_matching) | 0x158    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_20`](#ibus_addr_matching) | 0x15c    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_21`](#ibus_addr_matching) | 0x160    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_22`](#ibus_addr_matching) | 0x164    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_23`](#ibus_addr_matching) | 0x168    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_24`](#ibus_addr_matching) | 0x16c    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_25`](#ibus_addr_matching) | 0x170    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_26`](#ibus_addr_matching) | 0x174    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_27`](#ibus_addr_matching) | 0x178    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_28`](#ibus_addr_matching) | 0x17c    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_29`](#ibus_addr_matching) | 0x180    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_30`](#ibus_addr_matching) | 0x184    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_31`](#ibus_addr_matching) | 0x188    |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_REMAP_ADDR_0`](#ibus_remap_addr)        | 0x18c    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_1`](#ibus_remap_addr)        | 0x190    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_2`](#ibus_remap_addr)        | 0x194    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_3`](#ibus_remap_addr)        | 0x198    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_4`](#ibus_remap_addr)        | 0x19c    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_5`](#ibus_remap_addr)        | 0x1a0    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_6`](#ibus_remap_addr)        | 0x1a4    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_7`](#ibus_remap_addr)        | 0x1a8    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_8`](#ibus_remap_addr)        | 0x1ac    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_9`](#ibus_remap_addr)        | 0x1b0    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_10`](#ibus_remap_addr)       | 0x1b4    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_11`](#ibus_remap_addr)       | 0x1b8    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_12`](#ibus_remap_addr)       | 0x1bc    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_13`](#ibus_remap_addr)       | 0x1c0    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_14`](#ibus_remap_addr)       | 0x1c4    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_15`](#ibus_remap_addr)       | 0x1c8    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_16`](#ibus_remap_addr)       | 0x1cc    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_17`](#ibus_remap_addr)       | 0x1d0    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_18`](#ibus_remap_addr)       | 0x1d4    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_19`](#ibus_remap_addr)       | 0x1d8    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_20`](#ibus_remap_addr)       | 0x1dc    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_21`](#ibus_remap_addr)       | 0x1e0    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_22`](#ibus_remap_addr)       | 0x1e4    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_23`](#ibus_remap_addr)       | 0x1e8    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_24`](#ibus_remap_addr)       | 0x1ec    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_25`](#ibus_remap_addr)       | 0x1f0    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_26`](#ibus_remap_addr)       | 0x1f4    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_27`](#ibus_remap_addr)       | 0x1f8    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_28`](#ibus_remap_addr)       | 0x1fc    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_29`](#ibus_remap_addr)       | 0x200    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_30`](#ibus_remap_addr)       | 0x204    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_31`](#ibus_remap_addr)       | 0x208    |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`DBUS_REGWEN_0`](#dbus_regwen)                | 0x20c    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_1`](#dbus_regwen)                | 0x210    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_2`](#dbus_regwen)                | 0x214    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_3`](#dbus_regwen)                | 0x218    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_4`](#dbus_regwen)                | 0x21c    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_5`](#dbus_regwen)                | 0x220    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_6`](#dbus_regwen)                | 0x224    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_7`](#dbus_regwen)                | 0x228    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_8`](#dbus_regwen)                | 0x22c    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_9`](#dbus_regwen)                | 0x230    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_10`](#dbus_regwen)               | 0x234    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_11`](#dbus_regwen)               | 0x238    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_12`](#dbus_regwen)               | 0x23c    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_13`](#dbus_regwen)               | 0x240    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_14`](#dbus_regwen)               | 0x244    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_15`](#dbus_regwen)               | 0x248    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_16`](#dbus_regwen)               | 0x24c    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_17`](#dbus_regwen)               | 0x250    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_18`](#dbus_regwen)               | 0x254    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_19`](#dbus_regwen)               | 0x258    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_20`](#dbus_regwen)               | 0x25c    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_21`](#dbus_regwen)               | 0x260    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_22`](#dbus_regwen)               | 0x264    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_23`](#dbus_regwen)               | 0x268    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_24`](#dbus_regwen)               | 0x26c    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_25`](#dbus_regwen)               | 0x270    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_26`](#dbus_regwen)               | 0x274    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_27`](#dbus_regwen)               | 0x278    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_28`](#dbus_regwen)               | 0x27c    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_29`](#dbus_regwen)               | 0x280    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_30`](#dbus_regwen)               | 0x284    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_31`](#dbus_regwen)               | 0x288    |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_ADDR_EN_0`](#dbus_addr_en)              | 0x28c    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_1`](#dbus_addr_en)              | 0x290    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_2`](#dbus_addr_en)              | 0x294    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_3`](#dbus_addr_en)              | 0x298    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_4`](#dbus_addr_en)              | 0x29c    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_5`](#dbus_addr_en)              | 0x2a0    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_6`](#dbus_addr_en)              | 0x2a4    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_7`](#dbus_addr_en)              | 0x2a8    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_8`](#dbus_addr_en)              | 0x2ac    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_9`](#dbus_addr_en)              | 0x2b0    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_10`](#dbus_addr_en)             | 0x2b4    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_11`](#dbus_addr_en)             | 0x2b8    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_12`](#dbus_addr_en)             | 0x2bc    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_13`](#dbus_addr_en)             | 0x2c0    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_14`](#dbus_addr_en)             | 0x2c4    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_15`](#dbus_addr_en)             | 0x2c8    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_16`](#dbus_addr_en)             | 0x2cc    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_17`](#dbus_addr_en)             | 0x2d0    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_18`](#dbus_addr_en)             | 0x2d4    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_19`](#dbus_addr_en)             | 0x2d8    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_20`](#dbus_addr_en)             | 0x2dc    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_21`](#dbus_addr_en)             | 0x2e0    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_22`](#dbus_addr_en)             | 0x2e4    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_23`](#dbus_addr_en)             | 0x2e8    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_24`](#dbus_addr_en)             | 0x2ec    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_25`](#dbus_addr_en)             | 0x2f0    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_26`](#dbus_addr_en)             | 0x2f4    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_27`](#dbus_addr_en)             | 0x2f8    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_28`](#dbus_addr_en)             | 0x2fc    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_29`](#dbus_addr_en)             | 0x300    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_30`](#dbus_addr_en)             | 0x304    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_31`](#dbus_addr_en)             | 0x308    |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_0`](#dbus_addr_matching)  | 0x30c    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_1`](#dbus_addr_matching)  | 0x310    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_2`](#dbus_addr_matching)  | 0x314    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_3`](#dbus_addr_matching)  | 0x318    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_4`](#dbus_addr_matching)  | 0x31c    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_5`](#dbus_addr_matching)  | 0x320    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_6`](#dbus_addr_matching)  | 0x324    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_7`](#dbus_addr_matching)  | 0x328    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_8`](#dbus_addr_matching)  | 0x32c    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_9`](#dbus_addr_matching)  | 0x330    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_10`](#dbus_addr_matching) | 0x334    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_11`](#dbus_addr_matching) | 0x338    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_12`](#dbus_addr_matching) | 0x33c    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_13`](#dbus_addr_matching) | 0x340    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_14`](#dbus_addr_matching) | 0x344    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_15`](#dbus_addr_matching) | 0x348    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_16`](#dbus_addr_matching) | 0x34c    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_17`](#dbus_addr_matching) | 0x350    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_18`](#dbus_addr_matching) | 0x354    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_19`](#dbus_addr_matching) | 0x358    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_20`](#dbus_addr_matching) | 0x35c    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_21`](#dbus_addr_matching) | 0x360    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_22`](#dbus_addr_matching) | 0x364    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_23`](#dbus_addr_matching) | 0x368    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_24`](#dbus_addr_matching) | 0x36c    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_25`](#dbus_addr_matching) | 0x370    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_26`](#dbus_addr_matching) | 0x374    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_27`](#dbus_addr_matching) | 0x378    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_28`](#dbus_addr_matching) | 0x37c    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_29`](#dbus_addr_matching) | 0x380    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_30`](#dbus_addr_matching) | 0x384    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_31`](#dbus_addr_matching) | 0x388    |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_REMAP_ADDR_0`](#dbus_remap_addr)        | 0x38c    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_1`](#dbus_remap_addr)        | 0x390    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_2`](#dbus_remap_addr)        | 0x394    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_3`](#dbus_remap_addr)        | 0x398    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_4`](#dbus_remap_addr)        | 0x39c    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_5`](#dbus_remap_addr)        | 0x3a0    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_6`](#dbus_remap_addr)        | 0x3a4    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_7`](#dbus_remap_addr)        | 0x3a8    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_8`](#dbus_remap_addr)        | 0x3ac    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_9`](#dbus_remap_addr)        | 0x3b0    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_10`](#dbus_remap_addr)       | 0x3b4    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_11`](#dbus_remap_addr)       | 0x3b8    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_12`](#dbus_remap_addr)       | 0x3bc    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_13`](#dbus_remap_addr)       | 0x3c0    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_14`](#dbus_remap_addr)       | 0x3c4    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_15`](#dbus_remap_addr)       | 0x3c8    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_16`](#dbus_remap_addr)       | 0x3cc    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_17`](#dbus_remap_addr)       | 0x3d0    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_18`](#dbus_remap_addr)       | 0x3d4    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_19`](#dbus_remap_addr)       | 0x3d8    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_20`](#dbus_remap_addr)       | 0x3dc    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_21`](#dbus_remap_addr)       | 0x3e0    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_22`](#dbus_remap_addr)       | 0x3e4    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_23`](#dbus_remap_addr)       | 0x3e8    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_24`](#dbus_remap_addr)       | 0x3ec    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_25`](#dbus_remap_addr)       | 0x3f0    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_26`](#dbus_remap_addr)       | 0x3f4    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_27`](#dbus_remap_addr)       | 0x3f8    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_28`](#dbus_remap_addr)       | 0x3fc    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_29`](#dbus_remap_addr)       | 0x400    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_30`](#dbus_remap_addr)       | 0x404    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_31`](#dbus_remap_addr)       | 0x408    |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`NMI_ENABLE`](#nmi_enable)                    | 0x40c    |        4 | Enable mask for NMI.                                 |
| rv_core_ibex.[`NMI_STATE`](#nmi_state)                      | 0x410    |        4 | Current NMI state                                    |
| rv_core_ibex.[`ERR_STATUS`](#err_status)                    | 0x414    |        4 | error status                                         |
| rv_core_ibex.[`RND_DATA`](#rnd_data)                        | 0x418    |        4 | Random data from EDN                                 |
| rv_core_ibex.[`RND_STATUS`](#rnd_status)                    | 0x41c    |        4 | Status of random data in !!RND_DATA                  |
| rv_core_ibex.[`FPGA_INFO`](#fpga_info)                      | 0x420    |        4 | FPGA build timestamp info.                           |
| rv_core_ibex.[`DV_SIM_WINDOW`](#dv_sim_window)              | 0x440    |       32 | Exposed tlul window for DV only purposes.            |

## ALERT_TEST
Alert Test Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "fatal_sw_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "recov_sw_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_hw_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "recov_hw_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                      |
|:------:|:------:|:-------:|:-------------|:-------------------------------------------------|
|  31:4  |        |         |              | Reserved                                         |
|   3    |   wo   |   0x0   | recov_hw_err | Write 1 to trigger one alert event of this kind. |
|   2    |   wo   |   0x0   | fatal_hw_err | Write 1 to trigger one alert event of this kind. |
|   1    |   wo   |   0x0   | recov_sw_err | Write 1 to trigger one alert event of this kind. |
|   0    |   wo   |   0x0   | fatal_sw_err | Write 1 to trigger one alert event of this kind. |

## SW_RECOV_ERR
Software recoverable error
- Offset: `0x4`
- Reset default: `0x9`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                            |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:4  |        |         |        | Reserved                                                                                                                                                                               |
|  3:0   |   rw   |   0x9   | VAL    | Software recoverable alert. When set to any value other than kMultiBitBool4False, a recoverable alert is sent. Once the alert is sent, the field is then reset to kMultiBitBool4False. |

## SW_FATAL_ERR
Software fatal error
- Offset: `0x8`
- Reset default: `0x9`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 4, "attr": ["rw1s"], "rotate": 0}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                              |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:4  |        |         |        | Reserved                                                                                                                                                                                 |
|  3:0   |  rw1s  |   0x9   | VAL    | Software fatal alert. When set to any value other than kMultiBitBool4False, a fatal alert is sent. Note, this field once cleared cannot be set and will continuously cause alert events. |

## IBUS_REGWEN
Ibus address control regwen.
- Reset default: `0x1`
- Reset mask: `0x1`

### Instances

| Name           | Offset   |
|:---------------|:---------|
| IBUS_REGWEN_0  | 0xc      |
| IBUS_REGWEN_1  | 0x10     |
| IBUS_REGWEN_2  | 0x14     |
| IBUS_REGWEN_3  | 0x18     |
| IBUS_REGWEN_4  | 0x1c     |
| IBUS_REGWEN_5  | 0x20     |
| IBUS_REGWEN_6  | 0x24     |
| IBUS_REGWEN_7  | 0x28     |
| IBUS_REGWEN_8  | 0x2c     |
| IBUS_REGWEN_9  | 0x30     |
| IBUS_REGWEN_10 | 0x34     |
| IBUS_REGWEN_11 | 0x38     |
| IBUS_REGWEN_12 | 0x3c     |
| IBUS_REGWEN_13 | 0x40     |
| IBUS_REGWEN_14 | 0x44     |
| IBUS_REGWEN_15 | 0x48     |
| IBUS_REGWEN_16 | 0x4c     |
| IBUS_REGWEN_17 | 0x50     |
| IBUS_REGWEN_18 | 0x54     |
| IBUS_REGWEN_19 | 0x58     |
| IBUS_REGWEN_20 | 0x5c     |
| IBUS_REGWEN_21 | 0x60     |
| IBUS_REGWEN_22 | 0x64     |
| IBUS_REGWEN_23 | 0x68     |
| IBUS_REGWEN_24 | 0x6c     |
| IBUS_REGWEN_25 | 0x70     |
| IBUS_REGWEN_26 | 0x74     |
| IBUS_REGWEN_27 | 0x78     |
| IBUS_REGWEN_28 | 0x7c     |
| IBUS_REGWEN_29 | 0x80     |
| IBUS_REGWEN_30 | 0x84     |
| IBUS_REGWEN_31 | 0x88     |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                   |
|:------:|:------:|:-------:|:-----------------------|
|  31:1  |        |         | Reserved               |
|   0    |  rw0c  |   0x1   | [EN](#ibus_regwen--en) |

### IBUS_REGWEN . EN
Ibus address controls write enable.  Once set to 0, it can longer be configured to 1

| Value   | Name    | Description                                                    |
|:--------|:--------|:---------------------------------------------------------------|
| 0x0     | locked  | Address controls can no longer be configured until next reset. |
| 0x1     | enabled | Address controls can still be configured.                      |


## IBUS_ADDR_EN
Enable Ibus address matching
- Reset default: `0x0`
- Reset mask: `0x1`
- Register enable: [`IBUS_REGWEN`](#ibus_regwen)

### Instances

| Name            | Offset   |
|:----------------|:---------|
| IBUS_ADDR_EN_0  | 0x8c     |
| IBUS_ADDR_EN_1  | 0x90     |
| IBUS_ADDR_EN_2  | 0x94     |
| IBUS_ADDR_EN_3  | 0x98     |
| IBUS_ADDR_EN_4  | 0x9c     |
| IBUS_ADDR_EN_5  | 0xa0     |
| IBUS_ADDR_EN_6  | 0xa4     |
| IBUS_ADDR_EN_7  | 0xa8     |
| IBUS_ADDR_EN_8  | 0xac     |
| IBUS_ADDR_EN_9  | 0xb0     |
| IBUS_ADDR_EN_10 | 0xb4     |
| IBUS_ADDR_EN_11 | 0xb8     |
| IBUS_ADDR_EN_12 | 0xbc     |
| IBUS_ADDR_EN_13 | 0xc0     |
| IBUS_ADDR_EN_14 | 0xc4     |
| IBUS_ADDR_EN_15 | 0xc8     |
| IBUS_ADDR_EN_16 | 0xcc     |
| IBUS_ADDR_EN_17 | 0xd0     |
| IBUS_ADDR_EN_18 | 0xd4     |
| IBUS_ADDR_EN_19 | 0xd8     |
| IBUS_ADDR_EN_20 | 0xdc     |
| IBUS_ADDR_EN_21 | 0xe0     |
| IBUS_ADDR_EN_22 | 0xe4     |
| IBUS_ADDR_EN_23 | 0xe8     |
| IBUS_ADDR_EN_24 | 0xec     |
| IBUS_ADDR_EN_25 | 0xf0     |
| IBUS_ADDR_EN_26 | 0xf4     |
| IBUS_ADDR_EN_27 | 0xf8     |
| IBUS_ADDR_EN_28 | 0xfc     |
| IBUS_ADDR_EN_29 | 0x100    |
| IBUS_ADDR_EN_30 | 0x104    |
| IBUS_ADDR_EN_31 | 0x108    |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                   |
|:------:|:------:|:-------:|:-------|:------------------------------|
|  31:1  |        |         |        | Reserved                      |
|   0    |   rw   |   0x0   | EN     | Enable ibus address matching. |

## IBUS_ADDR_MATCHING
  Matching region programming for ibus.

  The value programmed is done at power-of-2 alignment.
  For example, if the intended matching region is 0x8000_0000 to 0x8000_FFFF, the value programmed is 0x8000_7FFF.

  The value programmed can be determined from the translation granule.
  Assume the user wishes to translate a specific 64KB block to a different address:
  64KB has a hex value of 0x10000.
  Subtract 1 from this value and then right shift by one to obtain 0x7FFF.
  This value is then logically OR'd with the upper address bits that would select which 64KB to translate.

  In this example, the user wishes to translate the 0x8000-th 64KB block.
  The value programmed is then 0x8000_7FFF.

  If the user were to translate the 0x8001-th 64KB block, the value programmed would be 0x8001_7FFF.
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`IBUS_REGWEN`](#ibus_regwen)

### Instances

| Name                  | Offset   |
|:----------------------|:---------|
| IBUS_ADDR_MATCHING_0  | 0x10c    |
| IBUS_ADDR_MATCHING_1  | 0x110    |
| IBUS_ADDR_MATCHING_2  | 0x114    |
| IBUS_ADDR_MATCHING_3  | 0x118    |
| IBUS_ADDR_MATCHING_4  | 0x11c    |
| IBUS_ADDR_MATCHING_5  | 0x120    |
| IBUS_ADDR_MATCHING_6  | 0x124    |
| IBUS_ADDR_MATCHING_7  | 0x128    |
| IBUS_ADDR_MATCHING_8  | 0x12c    |
| IBUS_ADDR_MATCHING_9  | 0x130    |
| IBUS_ADDR_MATCHING_10 | 0x134    |
| IBUS_ADDR_MATCHING_11 | 0x138    |
| IBUS_ADDR_MATCHING_12 | 0x13c    |
| IBUS_ADDR_MATCHING_13 | 0x140    |
| IBUS_ADDR_MATCHING_14 | 0x144    |
| IBUS_ADDR_MATCHING_15 | 0x148    |
| IBUS_ADDR_MATCHING_16 | 0x14c    |
| IBUS_ADDR_MATCHING_17 | 0x150    |
| IBUS_ADDR_MATCHING_18 | 0x154    |
| IBUS_ADDR_MATCHING_19 | 0x158    |
| IBUS_ADDR_MATCHING_20 | 0x15c    |
| IBUS_ADDR_MATCHING_21 | 0x160    |
| IBUS_ADDR_MATCHING_22 | 0x164    |
| IBUS_ADDR_MATCHING_23 | 0x168    |
| IBUS_ADDR_MATCHING_24 | 0x16c    |
| IBUS_ADDR_MATCHING_25 | 0x170    |
| IBUS_ADDR_MATCHING_26 | 0x174    |
| IBUS_ADDR_MATCHING_27 | 0x178    |
| IBUS_ADDR_MATCHING_28 | 0x17c    |
| IBUS_ADDR_MATCHING_29 | 0x180    |
| IBUS_ADDR_MATCHING_30 | 0x184    |
| IBUS_ADDR_MATCHING_31 | 0x188    |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description           |
|:------:|:------:|:-------:|:-------|:----------------------|
|  31:0  |   rw   |   0x0   | VAL    | Matching region value |

## IBUS_REMAP_ADDR
  The remap address after a match has been made.
  The remap bits apply only to top portion of address bits not covered by the matching region.

  For example, if the translation region is 64KB, the remapped address applies only to the upper
  address bits that select which 64KB to be translated.
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`IBUS_REGWEN`](#ibus_regwen)

### Instances

| Name               | Offset   |
|:-------------------|:---------|
| IBUS_REMAP_ADDR_0  | 0x18c    |
| IBUS_REMAP_ADDR_1  | 0x190    |
| IBUS_REMAP_ADDR_2  | 0x194    |
| IBUS_REMAP_ADDR_3  | 0x198    |
| IBUS_REMAP_ADDR_4  | 0x19c    |
| IBUS_REMAP_ADDR_5  | 0x1a0    |
| IBUS_REMAP_ADDR_6  | 0x1a4    |
| IBUS_REMAP_ADDR_7  | 0x1a8    |
| IBUS_REMAP_ADDR_8  | 0x1ac    |
| IBUS_REMAP_ADDR_9  | 0x1b0    |
| IBUS_REMAP_ADDR_10 | 0x1b4    |
| IBUS_REMAP_ADDR_11 | 0x1b8    |
| IBUS_REMAP_ADDR_12 | 0x1bc    |
| IBUS_REMAP_ADDR_13 | 0x1c0    |
| IBUS_REMAP_ADDR_14 | 0x1c4    |
| IBUS_REMAP_ADDR_15 | 0x1c8    |
| IBUS_REMAP_ADDR_16 | 0x1cc    |
| IBUS_REMAP_ADDR_17 | 0x1d0    |
| IBUS_REMAP_ADDR_18 | 0x1d4    |
| IBUS_REMAP_ADDR_19 | 0x1d8    |
| IBUS_REMAP_ADDR_20 | 0x1dc    |
| IBUS_REMAP_ADDR_21 | 0x1e0    |
| IBUS_REMAP_ADDR_22 | 0x1e4    |
| IBUS_REMAP_ADDR_23 | 0x1e8    |
| IBUS_REMAP_ADDR_24 | 0x1ec    |
| IBUS_REMAP_ADDR_25 | 0x1f0    |
| IBUS_REMAP_ADDR_26 | 0x1f4    |
| IBUS_REMAP_ADDR_27 | 0x1f8    |
| IBUS_REMAP_ADDR_28 | 0x1fc    |
| IBUS_REMAP_ADDR_29 | 0x200    |
| IBUS_REMAP_ADDR_30 | 0x204    |
| IBUS_REMAP_ADDR_31 | 0x208    |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description      |
|:------:|:------:|:-------:|:-------|:-----------------|
|  31:0  |   rw   |   0x0   | VAL    | Remap addr value |

## DBUS_REGWEN
Dbus address control regwen.
- Reset default: `0x1`
- Reset mask: `0x1`

### Instances

| Name           | Offset   |
|:---------------|:---------|
| DBUS_REGWEN_0  | 0x20c    |
| DBUS_REGWEN_1  | 0x210    |
| DBUS_REGWEN_2  | 0x214    |
| DBUS_REGWEN_3  | 0x218    |
| DBUS_REGWEN_4  | 0x21c    |
| DBUS_REGWEN_5  | 0x220    |
| DBUS_REGWEN_6  | 0x224    |
| DBUS_REGWEN_7  | 0x228    |
| DBUS_REGWEN_8  | 0x22c    |
| DBUS_REGWEN_9  | 0x230    |
| DBUS_REGWEN_10 | 0x234    |
| DBUS_REGWEN_11 | 0x238    |
| DBUS_REGWEN_12 | 0x23c    |
| DBUS_REGWEN_13 | 0x240    |
| DBUS_REGWEN_14 | 0x244    |
| DBUS_REGWEN_15 | 0x248    |
| DBUS_REGWEN_16 | 0x24c    |
| DBUS_REGWEN_17 | 0x250    |
| DBUS_REGWEN_18 | 0x254    |
| DBUS_REGWEN_19 | 0x258    |
| DBUS_REGWEN_20 | 0x25c    |
| DBUS_REGWEN_21 | 0x260    |
| DBUS_REGWEN_22 | 0x264    |
| DBUS_REGWEN_23 | 0x268    |
| DBUS_REGWEN_24 | 0x26c    |
| DBUS_REGWEN_25 | 0x270    |
| DBUS_REGWEN_26 | 0x274    |
| DBUS_REGWEN_27 | 0x278    |
| DBUS_REGWEN_28 | 0x27c    |
| DBUS_REGWEN_29 | 0x280    |
| DBUS_REGWEN_30 | 0x284    |
| DBUS_REGWEN_31 | 0x288    |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                   |
|:------:|:------:|:-------:|:-----------------------|
|  31:1  |        |         | Reserved               |
|   0    |  rw0c  |   0x1   | [EN](#dbus_regwen--en) |

### DBUS_REGWEN . EN
Ibus address controls write enable.  Once set to 0, it can longer be configured to 1

| Value   | Name    | Description                                                    |
|:--------|:--------|:---------------------------------------------------------------|
| 0x0     | locked  | Address controls can no longer be configured until next reset. |
| 0x1     | enabled | Address controls can still be configured.                      |


## DBUS_ADDR_EN
Enable dbus address matching
- Reset default: `0x0`
- Reset mask: `0x1`
- Register enable: [`DBUS_REGWEN`](#dbus_regwen)

### Instances

| Name            | Offset   |
|:----------------|:---------|
| DBUS_ADDR_EN_0  | 0x28c    |
| DBUS_ADDR_EN_1  | 0x290    |
| DBUS_ADDR_EN_2  | 0x294    |
| DBUS_ADDR_EN_3  | 0x298    |
| DBUS_ADDR_EN_4  | 0x29c    |
| DBUS_ADDR_EN_5  | 0x2a0    |
| DBUS_ADDR_EN_6  | 0x2a4    |
| DBUS_ADDR_EN_7  | 0x2a8    |
| DBUS_ADDR_EN_8  | 0x2ac    |
| DBUS_ADDR_EN_9  | 0x2b0    |
| DBUS_ADDR_EN_10 | 0x2b4    |
| DBUS_ADDR_EN_11 | 0x2b8    |
| DBUS_ADDR_EN_12 | 0x2bc    |
| DBUS_ADDR_EN_13 | 0x2c0    |
| DBUS_ADDR_EN_14 | 0x2c4    |
| DBUS_ADDR_EN_15 | 0x2c8    |
| DBUS_ADDR_EN_16 | 0x2cc    |
| DBUS_ADDR_EN_17 | 0x2d0    |
| DBUS_ADDR_EN_18 | 0x2d4    |
| DBUS_ADDR_EN_19 | 0x2d8    |
| DBUS_ADDR_EN_20 | 0x2dc    |
| DBUS_ADDR_EN_21 | 0x2e0    |
| DBUS_ADDR_EN_22 | 0x2e4    |
| DBUS_ADDR_EN_23 | 0x2e8    |
| DBUS_ADDR_EN_24 | 0x2ec    |
| DBUS_ADDR_EN_25 | 0x2f0    |
| DBUS_ADDR_EN_26 | 0x2f4    |
| DBUS_ADDR_EN_27 | 0x2f8    |
| DBUS_ADDR_EN_28 | 0x2fc    |
| DBUS_ADDR_EN_29 | 0x300    |
| DBUS_ADDR_EN_30 | 0x304    |
| DBUS_ADDR_EN_31 | 0x308    |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                   |
|:------:|:------:|:-------:|:-------|:------------------------------|
|  31:1  |        |         |        | Reserved                      |
|   0    |   rw   |   0x0   | EN     | Enable dbus address matching. |

## DBUS_ADDR_MATCHING
See [`IBUS_ADDR_MATCHING_0`](#ibus_addr_matching_0) for detailed description.
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`DBUS_REGWEN`](#dbus_regwen)

### Instances

| Name                  | Offset   |
|:----------------------|:---------|
| DBUS_ADDR_MATCHING_0  | 0x30c    |
| DBUS_ADDR_MATCHING_1  | 0x310    |
| DBUS_ADDR_MATCHING_2  | 0x314    |
| DBUS_ADDR_MATCHING_3  | 0x318    |
| DBUS_ADDR_MATCHING_4  | 0x31c    |
| DBUS_ADDR_MATCHING_5  | 0x320    |
| DBUS_ADDR_MATCHING_6  | 0x324    |
| DBUS_ADDR_MATCHING_7  | 0x328    |
| DBUS_ADDR_MATCHING_8  | 0x32c    |
| DBUS_ADDR_MATCHING_9  | 0x330    |
| DBUS_ADDR_MATCHING_10 | 0x334    |
| DBUS_ADDR_MATCHING_11 | 0x338    |
| DBUS_ADDR_MATCHING_12 | 0x33c    |
| DBUS_ADDR_MATCHING_13 | 0x340    |
| DBUS_ADDR_MATCHING_14 | 0x344    |
| DBUS_ADDR_MATCHING_15 | 0x348    |
| DBUS_ADDR_MATCHING_16 | 0x34c    |
| DBUS_ADDR_MATCHING_17 | 0x350    |
| DBUS_ADDR_MATCHING_18 | 0x354    |
| DBUS_ADDR_MATCHING_19 | 0x358    |
| DBUS_ADDR_MATCHING_20 | 0x35c    |
| DBUS_ADDR_MATCHING_21 | 0x360    |
| DBUS_ADDR_MATCHING_22 | 0x364    |
| DBUS_ADDR_MATCHING_23 | 0x368    |
| DBUS_ADDR_MATCHING_24 | 0x36c    |
| DBUS_ADDR_MATCHING_25 | 0x370    |
| DBUS_ADDR_MATCHING_26 | 0x374    |
| DBUS_ADDR_MATCHING_27 | 0x378    |
| DBUS_ADDR_MATCHING_28 | 0x37c    |
| DBUS_ADDR_MATCHING_29 | 0x380    |
| DBUS_ADDR_MATCHING_30 | 0x384    |
| DBUS_ADDR_MATCHING_31 | 0x388    |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description           |
|:------:|:------:|:-------:|:-------|:----------------------|
|  31:0  |   rw   |   0x0   | VAL    | Matching region value |

## DBUS_REMAP_ADDR
See [`IBUS_REMAP_ADDR_0`](#ibus_remap_addr_0) for a detailed description.
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`DBUS_REGWEN`](#dbus_regwen)

### Instances

| Name               | Offset   |
|:-------------------|:---------|
| DBUS_REMAP_ADDR_0  | 0x38c    |
| DBUS_REMAP_ADDR_1  | 0x390    |
| DBUS_REMAP_ADDR_2  | 0x394    |
| DBUS_REMAP_ADDR_3  | 0x398    |
| DBUS_REMAP_ADDR_4  | 0x39c    |
| DBUS_REMAP_ADDR_5  | 0x3a0    |
| DBUS_REMAP_ADDR_6  | 0x3a4    |
| DBUS_REMAP_ADDR_7  | 0x3a8    |
| DBUS_REMAP_ADDR_8  | 0x3ac    |
| DBUS_REMAP_ADDR_9  | 0x3b0    |
| DBUS_REMAP_ADDR_10 | 0x3b4    |
| DBUS_REMAP_ADDR_11 | 0x3b8    |
| DBUS_REMAP_ADDR_12 | 0x3bc    |
| DBUS_REMAP_ADDR_13 | 0x3c0    |
| DBUS_REMAP_ADDR_14 | 0x3c4    |
| DBUS_REMAP_ADDR_15 | 0x3c8    |
| DBUS_REMAP_ADDR_16 | 0x3cc    |
| DBUS_REMAP_ADDR_17 | 0x3d0    |
| DBUS_REMAP_ADDR_18 | 0x3d4    |
| DBUS_REMAP_ADDR_19 | 0x3d8    |
| DBUS_REMAP_ADDR_20 | 0x3dc    |
| DBUS_REMAP_ADDR_21 | 0x3e0    |
| DBUS_REMAP_ADDR_22 | 0x3e4    |
| DBUS_REMAP_ADDR_23 | 0x3e8    |
| DBUS_REMAP_ADDR_24 | 0x3ec    |
| DBUS_REMAP_ADDR_25 | 0x3f0    |
| DBUS_REMAP_ADDR_26 | 0x3f4    |
| DBUS_REMAP_ADDR_27 | 0x3f8    |
| DBUS_REMAP_ADDR_28 | 0x3fc    |
| DBUS_REMAP_ADDR_29 | 0x400    |
| DBUS_REMAP_ADDR_30 | 0x404    |
| DBUS_REMAP_ADDR_31 | 0x408    |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description      |
|:------:|:------:|:-------:|:-------|:-----------------|
|  31:0  |   rw   |   0x0   | VAL    | Remap addr value |

## NMI_ENABLE
Enable mask for NMI.
Once an enable mask is set, it cannot be disabled.
- Offset: `0x40c`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "ALERT_EN", "bits": 1, "attr": ["rw1s"], "rotate": -90}, {"name": "WDOG_EN", "bits": 1, "attr": ["rw1s"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                  |
|:------:|:------:|:-------:|:---------|:-----------------------------|
|  31:2  |        |         |          | Reserved                     |
|   1    |  rw1s  |   0x0   | WDOG_EN  | Enable mask for watchdog NMI |
|   0    |  rw1s  |   0x0   | ALERT_EN | Enable mask for alert NMI    |

## NMI_STATE
Current NMI state
- Offset: `0x410`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "ALERT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "WDOG", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                    |
|:------:|:------:|:-------:|:-------|:-------------------------------|
|  31:2  |        |         |        | Reserved                       |
|   1    |  rw1c  |   0x0   | WDOG   | Current state for watchdog NMI |
|   0    |  rw1c  |   0x0   | ALERT  | Current state for alert NMI    |

## ERR_STATUS
error status
- Offset: `0x414`
- Reset default: `0x0`
- Reset mask: `0x701`

### Fields

```wavejson
{"reg": [{"name": "REG_INTG_ERR", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 7}, {"name": "FATAL_INTG_ERR", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "FATAL_CORE_ERR", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "RECOV_CORE_ERR", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 21}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                                                                              |
|:------:|:------:|:-------:|:---------------|:-----------------------------------------------------------------------------------------|
| 31:11  |        |         |                | Reserved                                                                                 |
|   10   |  rw1c  |   0x0   | RECOV_CORE_ERR | rv_core_ibex detected a recoverable internal error (``alert_minor`` from Ibex seen)      |
|   9    |  rw1c  |   0x0   | FATAL_CORE_ERR | rv_core_ibex detected a fatal internal error (``alert_major_internal_o`` from Ibex seen) |
|   8    |  rw1c  |   0x0   | FATAL_INTG_ERR | rv_core_ibex detected a response integrity error                                         |
|  7:1   |        |         |                | Reserved                                                                                 |
|   0    |  rw1c  |   0x0   | REG_INTG_ERR   | rv_core_ibex_peri detected a register transmission integrity error                       |

## RND_DATA
Random data from EDN
- Offset: `0x418`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "DATA", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                    |
|:------:|:------:|:-------:|:------------------------|
|  31:0  |   ro   |   0x0   | [DATA](#rnd_data--data) |

### RND_DATA . DATA
Random bits taken from the EDN. [`RND_STATUS.RND_DATA_VALID`](#rnd_status)
indicates if this data is valid. When valid, reading from this
register invalidates the data and requests new data from the EDN.
The register becomes valid again when the EDN provides new data.
When invalid the register value will read as 0x0 with an EDN
request for new data pending. Upon reset the data will be invalid
with a new EDN request pending.

## RND_STATUS
Status of random data in [`RND_DATA`](#rnd_data)
- Offset: `0x41c`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "RND_DATA_VALID", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "RND_DATA_FIPS", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                                                                                                                                                                                              |
|:------:|:------:|:-------:|:---------------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:2  |        |         |                | Reserved                                                                                                                                                                                                 |
|   1    |   ro   |   0x0   | RND_DATA_FIPS  | When [`RND_STATUS.RND_DATA_VALID`](#rnd_status) is 1, this bit indicates whether [`RND_DATA`](#rnd_data) is fips quality. When [`RND_STATUS.RND_DATA_VALID`](#rnd_status) is 0, this bit has no meaning. |
|   0    |   ro   |   0x0   | RND_DATA_VALID | When set, the data in [`RND_DATA`](#rnd_data) is valid. When clear an EDN request for new data for [`RND_DATA`](#rnd_data) is pending.                                                                   |

## FPGA_INFO
FPGA build timestamp info.
This register only contains valid data for fpga, for all other variants it is simply 0.
- Offset: `0x420`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                       |
|:------:|:------:|:-------:|:-------|:----------------------------------|
|  31:0  |   ro   |   0x0   | VAL    | FPGA build timestamp information. |

## DV_SIM_WINDOW
Exposed tlul window for DV only purposes.

- Word Aligned Offset Range: `0x440`to`0x45c`
- Size (words): `8`
- Access: `rw`
- Byte writes are  supported.


<!-- END CMDGEN -->
