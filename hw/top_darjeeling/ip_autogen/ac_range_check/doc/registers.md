# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/top_darjeeling/ip_autogen/ac_range_check/data/ac_range_check.hjson -->
## Summary

| Name                                                                          | Offset   |   Length | Description                                                                                                                                               |
|:------------------------------------------------------------------------------|:---------|---------:|:----------------------------------------------------------------------------------------------------------------------------------------------------------|
| ac_range_check.[`INTR_STATE`](#intr_state)                                    | 0x0      |        4 | Interrupt State Register                                                                                                                                  |
| ac_range_check.[`INTR_ENABLE`](#intr_enable)                                  | 0x4      |        4 | Interrupt Enable Register                                                                                                                                 |
| ac_range_check.[`INTR_TEST`](#intr_test)                                      | 0x8      |        4 | Interrupt Test Register                                                                                                                                   |
| ac_range_check.[`ALERT_TEST`](#alert_test)                                    | 0xc      |        4 | Alert Test Register                                                                                                                                       |
| ac_range_check.[`ALERT_STATUS`](#alert_status)                                | 0x10     |        4 | Status of hardware alerts.                                                                                                                                |
| ac_range_check.[`LOG_CONFIG`](#log_config)                                    | 0x14     |        4 |                                                                                                                                                           |
| ac_range_check.[`LOG_STATUS`](#log_status)                                    | 0x18     |        4 | The LOG_STATUS register stores the number of denied accesses and gives more detailed diagnostics to the first denied request.                             |
| ac_range_check.[`LOG_ADDRESS`](#log_address)                                  | 0x1c     |        4 | First denied request address (if logging is enabled) gets written into that register.                                                                     |
| ac_range_check.[`RANGE_REGWEN_0`](#range_regwen)                              | 0x20     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_1`](#range_regwen)                              | 0x24     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_2`](#range_regwen)                              | 0x28     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_3`](#range_regwen)                              | 0x2c     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_4`](#range_regwen)                              | 0x30     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_5`](#range_regwen)                              | 0x34     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_6`](#range_regwen)                              | 0x38     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_7`](#range_regwen)                              | 0x3c     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_8`](#range_regwen)                              | 0x40     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_9`](#range_regwen)                              | 0x44     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_10`](#range_regwen)                             | 0x48     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_11`](#range_regwen)                             | 0x4c     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_12`](#range_regwen)                             | 0x50     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_13`](#range_regwen)                             | 0x54     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_14`](#range_regwen)                             | 0x58     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_15`](#range_regwen)                             | 0x5c     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_16`](#range_regwen)                             | 0x60     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_17`](#range_regwen)                             | 0x64     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_18`](#range_regwen)                             | 0x68     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_19`](#range_regwen)                             | 0x6c     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_20`](#range_regwen)                             | 0x70     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_21`](#range_regwen)                             | 0x74     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_22`](#range_regwen)                             | 0x78     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_23`](#range_regwen)                             | 0x7c     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_24`](#range_regwen)                             | 0x80     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_25`](#range_regwen)                             | 0x84     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_26`](#range_regwen)                             | 0x88     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_27`](#range_regwen)                             | 0x8c     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_28`](#range_regwen)                             | 0x90     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_29`](#range_regwen)                             | 0x94     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_30`](#range_regwen)                             | 0x98     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_31`](#range_regwen)                             | 0x9c     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_BASE_0`](#range_base)                                  | 0xa0     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_1`](#range_base)                                  | 0xa4     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_2`](#range_base)                                  | 0xa8     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_3`](#range_base)                                  | 0xac     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_4`](#range_base)                                  | 0xb0     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_5`](#range_base)                                  | 0xb4     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_6`](#range_base)                                  | 0xb8     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_7`](#range_base)                                  | 0xbc     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_8`](#range_base)                                  | 0xc0     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_9`](#range_base)                                  | 0xc4     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_10`](#range_base)                                 | 0xc8     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_11`](#range_base)                                 | 0xcc     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_12`](#range_base)                                 | 0xd0     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_13`](#range_base)                                 | 0xd4     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_14`](#range_base)                                 | 0xd8     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_15`](#range_base)                                 | 0xdc     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_16`](#range_base)                                 | 0xe0     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_17`](#range_base)                                 | 0xe4     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_18`](#range_base)                                 | 0xe8     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_19`](#range_base)                                 | 0xec     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_20`](#range_base)                                 | 0xf0     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_21`](#range_base)                                 | 0xf4     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_22`](#range_base)                                 | 0xf8     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_23`](#range_base)                                 | 0xfc     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_24`](#range_base)                                 | 0x100    |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_25`](#range_base)                                 | 0x104    |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_26`](#range_base)                                 | 0x108    |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_27`](#range_base)                                 | 0x10c    |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_28`](#range_base)                                 | 0x110    |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_29`](#range_base)                                 | 0x114    |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_30`](#range_base)                                 | 0x118    |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_31`](#range_base)                                 | 0x11c    |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_LIMIT_0`](#range_limit)                                | 0x120    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_1`](#range_limit)                                | 0x124    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_2`](#range_limit)                                | 0x128    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_3`](#range_limit)                                | 0x12c    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_4`](#range_limit)                                | 0x130    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_5`](#range_limit)                                | 0x134    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_6`](#range_limit)                                | 0x138    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_7`](#range_limit)                                | 0x13c    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_8`](#range_limit)                                | 0x140    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_9`](#range_limit)                                | 0x144    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_10`](#range_limit)                               | 0x148    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_11`](#range_limit)                               | 0x14c    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_12`](#range_limit)                               | 0x150    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_13`](#range_limit)                               | 0x154    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_14`](#range_limit)                               | 0x158    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_15`](#range_limit)                               | 0x15c    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_16`](#range_limit)                               | 0x160    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_17`](#range_limit)                               | 0x164    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_18`](#range_limit)                               | 0x168    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_19`](#range_limit)                               | 0x16c    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_20`](#range_limit)                               | 0x170    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_21`](#range_limit)                               | 0x174    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_22`](#range_limit)                               | 0x178    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_23`](#range_limit)                               | 0x17c    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_24`](#range_limit)                               | 0x180    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_25`](#range_limit)                               | 0x184    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_26`](#range_limit)                               | 0x188    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_27`](#range_limit)                               | 0x18c    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_28`](#range_limit)                               | 0x190    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_29`](#range_limit)                               | 0x194    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_30`](#range_limit)                               | 0x198    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_31`](#range_limit)                               | 0x19c    |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_ATTR_0`](#range_attr)                                  | 0x1a0    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_1`](#range_attr)                                  | 0x1a4    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_2`](#range_attr)                                  | 0x1a8    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_3`](#range_attr)                                  | 0x1ac    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_4`](#range_attr)                                  | 0x1b0    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_5`](#range_attr)                                  | 0x1b4    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_6`](#range_attr)                                  | 0x1b8    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_7`](#range_attr)                                  | 0x1bc    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_8`](#range_attr)                                  | 0x1c0    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_9`](#range_attr)                                  | 0x1c4    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_10`](#range_attr)                                 | 0x1c8    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_11`](#range_attr)                                 | 0x1cc    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_12`](#range_attr)                                 | 0x1d0    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_13`](#range_attr)                                 | 0x1d4    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_14`](#range_attr)                                 | 0x1d8    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_15`](#range_attr)                                 | 0x1dc    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_16`](#range_attr)                                 | 0x1e0    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_17`](#range_attr)                                 | 0x1e4    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_18`](#range_attr)                                 | 0x1e8    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_19`](#range_attr)                                 | 0x1ec    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_20`](#range_attr)                                 | 0x1f0    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_21`](#range_attr)                                 | 0x1f4    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_22`](#range_attr)                                 | 0x1f8    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_23`](#range_attr)                                 | 0x1fc    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_24`](#range_attr)                                 | 0x200    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_25`](#range_attr)                                 | 0x204    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_26`](#range_attr)                                 | 0x208    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_27`](#range_attr)                                 | 0x20c    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_28`](#range_attr)                                 | 0x210    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_29`](#range_attr)                                 | 0x214    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_30`](#range_attr)                                 | 0x218    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_ATTR_31`](#range_attr)                                 | 0x21c    |        4 | Attributes of the range.                                                                                                                                  |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_0`](#range_racl_policy_shadowed)  | 0x220    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_1`](#range_racl_policy_shadowed)  | 0x224    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_2`](#range_racl_policy_shadowed)  | 0x228    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_3`](#range_racl_policy_shadowed)  | 0x22c    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_4`](#range_racl_policy_shadowed)  | 0x230    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_5`](#range_racl_policy_shadowed)  | 0x234    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_6`](#range_racl_policy_shadowed)  | 0x238    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_7`](#range_racl_policy_shadowed)  | 0x23c    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_8`](#range_racl_policy_shadowed)  | 0x240    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_9`](#range_racl_policy_shadowed)  | 0x244    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_10`](#range_racl_policy_shadowed) | 0x248    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_11`](#range_racl_policy_shadowed) | 0x24c    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_12`](#range_racl_policy_shadowed) | 0x250    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_13`](#range_racl_policy_shadowed) | 0x254    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_14`](#range_racl_policy_shadowed) | 0x258    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_15`](#range_racl_policy_shadowed) | 0x25c    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_16`](#range_racl_policy_shadowed) | 0x260    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_17`](#range_racl_policy_shadowed) | 0x264    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_18`](#range_racl_policy_shadowed) | 0x268    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_19`](#range_racl_policy_shadowed) | 0x26c    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_20`](#range_racl_policy_shadowed) | 0x270    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_21`](#range_racl_policy_shadowed) | 0x274    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_22`](#range_racl_policy_shadowed) | 0x278    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_23`](#range_racl_policy_shadowed) | 0x27c    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_24`](#range_racl_policy_shadowed) | 0x280    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_25`](#range_racl_policy_shadowed) | 0x284    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_26`](#range_racl_policy_shadowed) | 0x288    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_27`](#range_racl_policy_shadowed) | 0x28c    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_28`](#range_racl_policy_shadowed) | 0x290    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_29`](#range_racl_policy_shadowed) | 0x294    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_30`](#range_racl_policy_shadowed) | 0x298    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_31`](#range_racl_policy_shadowed) | 0x29c    |        4 | The RACL policy register allows the system to further restrict the access to specific source roles.                                                       |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "deny_cnt_reached", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                         |
|:------:|:------:|:-------:|:-----------------|:------------------------------------|
|  31:1  |        |         |                  | Reserved                            |
|   0    |  rw1c  |   0x0   | deny_cnt_reached | Deny counter has reached threshold. |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "deny_cnt_reached", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                                |
|:------:|:------:|:-------:|:-----------------|:---------------------------------------------------------------------------|
|  31:1  |        |         |                  | Reserved                                                                   |
|   0    |   rw   |   0x0   | deny_cnt_reached | Enable interrupt when [`INTR_STATE.deny_cnt_reached`](#intr_state) is set. |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "deny_cnt_reached", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                         |
|:------:|:------:|:-------:|:-----------------|:--------------------------------------------------------------------|
|  31:1  |        |         |                  | Reserved                                                            |
|   0    |   wo   |   0x0   | deny_cnt_reached | Write 1 to force [`INTR_STATE.deny_cnt_reached`](#intr_state) to 1. |

## ALERT_TEST
Alert Test Register
- Offset: `0xc`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "recov_ctrl_update_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_fault", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                      |
|:------:|:------:|:-------:|:----------------------|:-------------------------------------------------|
|  31:2  |        |         |                       | Reserved                                         |
|   1    |   wo   |   0x0   | fatal_fault           | Write 1 to trigger one alert event of this kind. |
|   0    |   wo   |   0x0   | recov_ctrl_update_err | Write 1 to trigger one alert event of this kind. |

## ALERT_STATUS
Status of hardware alerts.
- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "SHADOWED_UPDATE_ERR", "bits": 1, "attr": ["rc"], "rotate": -90}, {"name": "SHADOWED_STORAGE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "REG_INTG_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "COUNTER_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                                                           |
|:------:|:------:|:-------:|:---------------------|:--------------------------------------------------------------------------------------------------------------------------------------|
|  31:4  |        |         |                      | Reserved                                                                                                                              |
|   3    |   ro   |   0x0   | COUNTER_ERR          | Integrity error in a counter. This is a fatal error. Once set, this field remains set until this HW IP block gets reset.              |
|   2    |   ro   |   0x0   | REG_INTG_ERR         | Integrity error in the register interface. This is a fatal error. Once set, this field remains set until this HW IP block gets reset. |
|   1    |   ro   |   0x0   | SHADOWED_STORAGE_ERR | Storage error of a shadowed register. This is a fatal error. Once set, this field remains set until this HW IP block gets reset.      |
|   0    |   rc   |   0x0   | SHADOWED_UPDATE_ERR  | Update error of a shadowed register. This is a recoverable error caused by SW misbehavior. This field gets cleared by a SW read.      |

## LOG_CONFIG

- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0x3ff`

### Fields

```wavejson
{"reg": [{"name": "log_enable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "log_clear", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "deny_cnt_threshold", "bits": 8, "attr": ["rw"], "rotate": -90}, {"bits": 22}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                                                                   |
|:------:|:------:|:-------:|:-------------------|:----------------------------------------------------------------------------------------------|
| 31:10  |        |         |                    | Reserved                                                                                      |
|  9:2   |   rw   |   0x0   | deny_cnt_threshold | An interrupt is raised (if enabled) when deny_cnt reaches the configured deny_cnt_threshold.  |
|   1    |   rw   |   0x0   | log_clear          | Clears all log information for the first denied access including: - LOG_STATUS - LOG_ADDRESS. |
|   0    |   rw   |   0x0   | log_enable         | When set, blocked requests are logged by the deny counter.                                    |

## LOG_STATUS
The LOG_STATUS register stores the number of denied accesses and gives more detailed diagnostics to the first denied request.
All fields of LOG_STATUS (other than deny_cnt) are only valid if deny_cnt > 0.
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0xfffffff`

### Fields

```wavejson
{"reg": [{"name": "deny_cnt", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "denied_read_access", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "denied_write_access", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "denied_execute_access", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "denied_no_match", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "denied_racl_read", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "denied_racl_write", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "denied_source_role", "bits": 4, "attr": ["ro"], "rotate": -90}, {"name": "denied_ctn_uid", "bits": 5, "attr": ["ro"], "rotate": -90}, {"name": "deny_range_index", "bits": 5, "attr": ["ro"], "rotate": -90}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                                                               |
|:------:|:------:|:-------:|:----------------------|:------------------------------------------------------------------------------------------|
| 31:28  |        |         |                       | Reserved                                                                                  |
| 27:23  |   ro   |   0x0   | deny_range_index      | Index of the range that caused the denied access.                                         |
| 22:18  |   ro   |   0x0   | denied_ctn_uid        | Source CTN UID that was denied access.                                                    |
| 17:14  |   ro   |   0x0   | denied_source_role    | Source RACL role that was denied access.                                                  |
|   13   |   ro   |   0x0   | denied_racl_write     | Indicates whether a write access was denied by RACL.                                      |
|   12   |   ro   |   0x0   | denied_racl_read      | Indicates whether a read access was denied by RACL.                                       |
|   11   |   ro   |   0x0   | denied_no_match       | Indicates whether the access was denied because no range matched.                         |
|   10   |   ro   |   0x0   | denied_execute_access | Indicates whether execution access was denied.                                            |
|   9    |   ro   |   0x0   | denied_write_access   | Indicates whether a write access was denied.                                              |
|   8    |   ro   |   0x0   | denied_read_access    | Indicates whether a read access was denied.                                               |
|  7:0   |   ro   |   0x0   | deny_cnt              | Software mirror of the internal deny counter. Gets incremented for every blocked request. |

## LOG_ADDRESS
First denied request address (if logging is enabled) gets written into that register.
- Offset: `0x1c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "log_address", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                   |
|:------:|:------:|:-------:|:------------|:------------------------------|
|  31:0  |   ro   |   0x0   | log_address | First denied request address. |

## RANGE_REGWEN
This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_ATTR_x, and RANGE_RACL_POLICY_SHADOWED_x register.
When cleared to Mubi4::False, the corresponding range configuration registers are locked and cannot be changed until the next reset.
- Reset default: `0x6`
- Reset mask: `0xf`

### Instances

| Name            | Offset   |
|:----------------|:---------|
| RANGE_REGWEN_0  | 0x20     |
| RANGE_REGWEN_1  | 0x24     |
| RANGE_REGWEN_2  | 0x28     |
| RANGE_REGWEN_3  | 0x2c     |
| RANGE_REGWEN_4  | 0x30     |
| RANGE_REGWEN_5  | 0x34     |
| RANGE_REGWEN_6  | 0x38     |
| RANGE_REGWEN_7  | 0x3c     |
| RANGE_REGWEN_8  | 0x40     |
| RANGE_REGWEN_9  | 0x44     |
| RANGE_REGWEN_10 | 0x48     |
| RANGE_REGWEN_11 | 0x4c     |
| RANGE_REGWEN_12 | 0x50     |
| RANGE_REGWEN_13 | 0x54     |
| RANGE_REGWEN_14 | 0x58     |
| RANGE_REGWEN_15 | 0x5c     |
| RANGE_REGWEN_16 | 0x60     |
| RANGE_REGWEN_17 | 0x64     |
| RANGE_REGWEN_18 | 0x68     |
| RANGE_REGWEN_19 | 0x6c     |
| RANGE_REGWEN_20 | 0x70     |
| RANGE_REGWEN_21 | 0x74     |
| RANGE_REGWEN_22 | 0x78     |
| RANGE_REGWEN_23 | 0x7c     |
| RANGE_REGWEN_24 | 0x80     |
| RANGE_REGWEN_25 | 0x84     |
| RANGE_REGWEN_26 | 0x88     |
| RANGE_REGWEN_27 | 0x8c     |
| RANGE_REGWEN_28 | 0x90     |
| RANGE_REGWEN_29 | 0x94     |
| RANGE_REGWEN_30 | 0x98     |
| RANGE_REGWEN_31 | 0x9c     |


### Fields

```wavejson
{"reg": [{"name": "regwen", "bits": 4, "attr": ["rw0c"], "rotate": 0}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                  |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------------------|
|  31:4  |        |         |        | Reserved                                                                                     |
|  3:0   |  rw0c  |   0x6   | regwen | Clearing this register locks the configuration registers of that range until the next reset. |

## RANGE_BASE
Base address for the range check.
The range base register exists per range and holds the base address for the range check.
The minimum granularity of the range is 4 bytes.
Therefore, the lowest 2 bits of the 32-bit base and limit registers are tied to zero.
- Reset default: `0x0`
- Reset mask: `0xfffffffc`
- Register enable: [`RANGE_REGWEN`](#range_regwen)

### Instances

| Name          | Offset   |
|:--------------|:---------|
| RANGE_BASE_0  | 0xa0     |
| RANGE_BASE_1  | 0xa4     |
| RANGE_BASE_2  | 0xa8     |
| RANGE_BASE_3  | 0xac     |
| RANGE_BASE_4  | 0xb0     |
| RANGE_BASE_5  | 0xb4     |
| RANGE_BASE_6  | 0xb8     |
| RANGE_BASE_7  | 0xbc     |
| RANGE_BASE_8  | 0xc0     |
| RANGE_BASE_9  | 0xc4     |
| RANGE_BASE_10 | 0xc8     |
| RANGE_BASE_11 | 0xcc     |
| RANGE_BASE_12 | 0xd0     |
| RANGE_BASE_13 | 0xd4     |
| RANGE_BASE_14 | 0xd8     |
| RANGE_BASE_15 | 0xdc     |
| RANGE_BASE_16 | 0xe0     |
| RANGE_BASE_17 | 0xe4     |
| RANGE_BASE_18 | 0xe8     |
| RANGE_BASE_19 | 0xec     |
| RANGE_BASE_20 | 0xf0     |
| RANGE_BASE_21 | 0xf4     |
| RANGE_BASE_22 | 0xf8     |
| RANGE_BASE_23 | 0xfc     |
| RANGE_BASE_24 | 0x100    |
| RANGE_BASE_25 | 0x104    |
| RANGE_BASE_26 | 0x108    |
| RANGE_BASE_27 | 0x10c    |
| RANGE_BASE_28 | 0x110    |
| RANGE_BASE_29 | 0x114    |
| RANGE_BASE_30 | 0x118    |
| RANGE_BASE_31 | 0x11c    |


### Fields

```wavejson
{"reg": [{"bits": 2}, {"name": "base", "bits": 30, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:2  |   rw   |   0x0   | base   | Base address  |
|  1:0   |        |         |        | Reserved      |

## RANGE_LIMIT
The (exclusive) limit address register used for the address matching.
- Reset default: `0x0`
- Reset mask: `0xfffffffc`
- Register enable: [`RANGE_REGWEN`](#range_regwen)

### Instances

| Name           | Offset   |
|:---------------|:---------|
| RANGE_LIMIT_0  | 0x120    |
| RANGE_LIMIT_1  | 0x124    |
| RANGE_LIMIT_2  | 0x128    |
| RANGE_LIMIT_3  | 0x12c    |
| RANGE_LIMIT_4  | 0x130    |
| RANGE_LIMIT_5  | 0x134    |
| RANGE_LIMIT_6  | 0x138    |
| RANGE_LIMIT_7  | 0x13c    |
| RANGE_LIMIT_8  | 0x140    |
| RANGE_LIMIT_9  | 0x144    |
| RANGE_LIMIT_10 | 0x148    |
| RANGE_LIMIT_11 | 0x14c    |
| RANGE_LIMIT_12 | 0x150    |
| RANGE_LIMIT_13 | 0x154    |
| RANGE_LIMIT_14 | 0x158    |
| RANGE_LIMIT_15 | 0x15c    |
| RANGE_LIMIT_16 | 0x160    |
| RANGE_LIMIT_17 | 0x164    |
| RANGE_LIMIT_18 | 0x168    |
| RANGE_LIMIT_19 | 0x16c    |
| RANGE_LIMIT_20 | 0x170    |
| RANGE_LIMIT_21 | 0x174    |
| RANGE_LIMIT_22 | 0x178    |
| RANGE_LIMIT_23 | 0x17c    |
| RANGE_LIMIT_24 | 0x180    |
| RANGE_LIMIT_25 | 0x184    |
| RANGE_LIMIT_26 | 0x188    |
| RANGE_LIMIT_27 | 0x18c    |
| RANGE_LIMIT_28 | 0x190    |
| RANGE_LIMIT_29 | 0x194    |
| RANGE_LIMIT_30 | 0x198    |
| RANGE_LIMIT_31 | 0x19c    |


### Fields

```wavejson
{"reg": [{"bits": 2}, {"name": "limit", "bits": 30, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description              |
|:------:|:------:|:-------:|:-------|:-------------------------|
|  31:2  |   rw   |   0x0   | limit  | Exclusive limit address. |
|  1:0   |        |         |        | Reserved                 |

## RANGE_ATTR
Attributes of the range.
This register exists per range and determines attributes (including permissions) of the particular range.
A range and its attributes are only considered if its `enable` field in this register is not set to `Mubi4::False`.
- Reset default: `0x69999`
- Reset mask: `0xfffff`
- Register enable: [`RANGE_REGWEN`](#range_regwen)

### Instances

| Name          | Offset   |
|:--------------|:---------|
| RANGE_ATTR_0  | 0x1a0    |
| RANGE_ATTR_1  | 0x1a4    |
| RANGE_ATTR_2  | 0x1a8    |
| RANGE_ATTR_3  | 0x1ac    |
| RANGE_ATTR_4  | 0x1b0    |
| RANGE_ATTR_5  | 0x1b4    |
| RANGE_ATTR_6  | 0x1b8    |
| RANGE_ATTR_7  | 0x1bc    |
| RANGE_ATTR_8  | 0x1c0    |
| RANGE_ATTR_9  | 0x1c4    |
| RANGE_ATTR_10 | 0x1c8    |
| RANGE_ATTR_11 | 0x1cc    |
| RANGE_ATTR_12 | 0x1d0    |
| RANGE_ATTR_13 | 0x1d4    |
| RANGE_ATTR_14 | 0x1d8    |
| RANGE_ATTR_15 | 0x1dc    |
| RANGE_ATTR_16 | 0x1e0    |
| RANGE_ATTR_17 | 0x1e4    |
| RANGE_ATTR_18 | 0x1e8    |
| RANGE_ATTR_19 | 0x1ec    |
| RANGE_ATTR_20 | 0x1f0    |
| RANGE_ATTR_21 | 0x1f4    |
| RANGE_ATTR_22 | 0x1f8    |
| RANGE_ATTR_23 | 0x1fc    |
| RANGE_ATTR_24 | 0x200    |
| RANGE_ATTR_25 | 0x204    |
| RANGE_ATTR_26 | 0x208    |
| RANGE_ATTR_27 | 0x20c    |
| RANGE_ATTR_28 | 0x210    |
| RANGE_ATTR_29 | 0x214    |
| RANGE_ATTR_30 | 0x218    |
| RANGE_ATTR_31 | 0x21c    |


### Fields

```wavejson
{"reg": [{"name": "enable", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "read_access", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "write_access", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "execute_access", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "log_denied_access", "bits": 4, "attr": ["rw"], "rotate": -90}, {"bits": 12}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                                                                                                                                    |
|:------:|:------:|:-------:|:------------------|:-----------------------------------------------------------------------------------------------------------------------------------------------|
| 31:20  |        |         |                   | Reserved                                                                                                                                       |
| 19:16  |   rw   |   0x6   | log_denied_access | When set to Mubi4::True, a denied access based on in this range is being logged.                                                               |
| 15:12  |   rw   |   0x9   | execute_access    | When set to Mubi4::True, code execution from this range is allowed.                                                                            |
|  11:8  |   rw   |   0x9   | write_access      | When set to Mubi4::True, write access to that range is allowed.                                                                                |
|  7:4   |   rw   |   0x9   | read_access       | When set to Mubi4::True, read access from that range is allowed.                                                                               |
|  3:0   |   rw   |   0x9   | enable            | When set to Mubi4::False, the range is _not_ considered in the range check; for any other value, the range _is_ considered in the range check. |

## RANGE_RACL_POLICY_SHADOWED
The RACL policy register allows the system to further restrict the access to specific source roles.
The default value for both the read and write permission bitmaps is to deny access for all roles.
This register is protected against fault attacks by using a shadow register implementation.
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`RANGE_REGWEN`](#range_regwen)

### Instances

| Name                          | Offset   |
|:------------------------------|:---------|
| RANGE_RACL_POLICY_SHADOWED_0  | 0x220    |
| RANGE_RACL_POLICY_SHADOWED_1  | 0x224    |
| RANGE_RACL_POLICY_SHADOWED_2  | 0x228    |
| RANGE_RACL_POLICY_SHADOWED_3  | 0x22c    |
| RANGE_RACL_POLICY_SHADOWED_4  | 0x230    |
| RANGE_RACL_POLICY_SHADOWED_5  | 0x234    |
| RANGE_RACL_POLICY_SHADOWED_6  | 0x238    |
| RANGE_RACL_POLICY_SHADOWED_7  | 0x23c    |
| RANGE_RACL_POLICY_SHADOWED_8  | 0x240    |
| RANGE_RACL_POLICY_SHADOWED_9  | 0x244    |
| RANGE_RACL_POLICY_SHADOWED_10 | 0x248    |
| RANGE_RACL_POLICY_SHADOWED_11 | 0x24c    |
| RANGE_RACL_POLICY_SHADOWED_12 | 0x250    |
| RANGE_RACL_POLICY_SHADOWED_13 | 0x254    |
| RANGE_RACL_POLICY_SHADOWED_14 | 0x258    |
| RANGE_RACL_POLICY_SHADOWED_15 | 0x25c    |
| RANGE_RACL_POLICY_SHADOWED_16 | 0x260    |
| RANGE_RACL_POLICY_SHADOWED_17 | 0x264    |
| RANGE_RACL_POLICY_SHADOWED_18 | 0x268    |
| RANGE_RACL_POLICY_SHADOWED_19 | 0x26c    |
| RANGE_RACL_POLICY_SHADOWED_20 | 0x270    |
| RANGE_RACL_POLICY_SHADOWED_21 | 0x274    |
| RANGE_RACL_POLICY_SHADOWED_22 | 0x278    |
| RANGE_RACL_POLICY_SHADOWED_23 | 0x27c    |
| RANGE_RACL_POLICY_SHADOWED_24 | 0x280    |
| RANGE_RACL_POLICY_SHADOWED_25 | 0x284    |
| RANGE_RACL_POLICY_SHADOWED_26 | 0x288    |
| RANGE_RACL_POLICY_SHADOWED_27 | 0x28c    |
| RANGE_RACL_POLICY_SHADOWED_28 | 0x290    |
| RANGE_RACL_POLICY_SHADOWED_29 | 0x294    |
| RANGE_RACL_POLICY_SHADOWED_30 | 0x298    |
| RANGE_RACL_POLICY_SHADOWED_31 | 0x29c    |


### Fields

```wavejson
{"reg": [{"name": "read_perm", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "write_perm", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                     |
|:------:|:------:|:-------:|:-----------|:--------------------------------|
| 31:16  |   rw   |   0x0   | write_perm | Write permission policy bitmap. |
|  15:0  |   rw   |   0x0   | read_perm  | Read permission policy bitmap.  |


<!-- END CMDGEN -->
