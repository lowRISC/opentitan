# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/top_earlgrey/ip_autogen/alert_handler/data/alert_handler.hjson -->
## Summary

| Name                                                                                    | Offset   |   Length | Description                                                                                     |
|:----------------------------------------------------------------------------------------|:---------|---------:|:------------------------------------------------------------------------------------------------|
| alert_handler.[`INTR_STATE`](#intr_state)                                               | 0x0      |        4 | Interrupt State Register                                                                        |
| alert_handler.[`INTR_ENABLE`](#intr_enable)                                             | 0x4      |        4 | Interrupt Enable Register                                                                       |
| alert_handler.[`INTR_TEST`](#intr_test)                                                 | 0x8      |        4 | Interrupt Test Register                                                                         |
| alert_handler.[`PING_TIMER_REGWEN`](#ping_timer_regwen)                                 | 0xc      |        4 | Register write enable for !!PING_TIMEOUT_CYC_SHADOWED and !!PING_TIMER_EN_SHADOWED.             |
| alert_handler.[`PING_TIMEOUT_CYC_SHADOWED`](#ping_timeout_cyc_shadowed)                 | 0x10     |        4 | Ping timeout cycle count.                                                                       |
| alert_handler.[`PING_TIMER_EN_SHADOWED`](#ping_timer_en_shadowed)                       | 0x14     |        4 | Ping timer enable.                                                                              |
| alert_handler.[`ALERT_REGWEN_0`](#alert_regwen)                                         | 0x18     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_1`](#alert_regwen)                                         | 0x1c     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_2`](#alert_regwen)                                         | 0x20     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_3`](#alert_regwen)                                         | 0x24     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_4`](#alert_regwen)                                         | 0x28     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_5`](#alert_regwen)                                         | 0x2c     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_6`](#alert_regwen)                                         | 0x30     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_7`](#alert_regwen)                                         | 0x34     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_8`](#alert_regwen)                                         | 0x38     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_9`](#alert_regwen)                                         | 0x3c     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_10`](#alert_regwen)                                        | 0x40     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_11`](#alert_regwen)                                        | 0x44     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_12`](#alert_regwen)                                        | 0x48     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_13`](#alert_regwen)                                        | 0x4c     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_14`](#alert_regwen)                                        | 0x50     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_15`](#alert_regwen)                                        | 0x54     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_16`](#alert_regwen)                                        | 0x58     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_17`](#alert_regwen)                                        | 0x5c     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_18`](#alert_regwen)                                        | 0x60     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_19`](#alert_regwen)                                        | 0x64     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_20`](#alert_regwen)                                        | 0x68     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_21`](#alert_regwen)                                        | 0x6c     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_22`](#alert_regwen)                                        | 0x70     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_23`](#alert_regwen)                                        | 0x74     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_24`](#alert_regwen)                                        | 0x78     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_25`](#alert_regwen)                                        | 0x7c     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_26`](#alert_regwen)                                        | 0x80     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_27`](#alert_regwen)                                        | 0x84     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_28`](#alert_regwen)                                        | 0x88     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_29`](#alert_regwen)                                        | 0x8c     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_30`](#alert_regwen)                                        | 0x90     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_31`](#alert_regwen)                                        | 0x94     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_32`](#alert_regwen)                                        | 0x98     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_33`](#alert_regwen)                                        | 0x9c     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_34`](#alert_regwen)                                        | 0xa0     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_35`](#alert_regwen)                                        | 0xa4     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_36`](#alert_regwen)                                        | 0xa8     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_37`](#alert_regwen)                                        | 0xac     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_38`](#alert_regwen)                                        | 0xb0     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_39`](#alert_regwen)                                        | 0xb4     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_40`](#alert_regwen)                                        | 0xb8     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_41`](#alert_regwen)                                        | 0xbc     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_42`](#alert_regwen)                                        | 0xc0     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_43`](#alert_regwen)                                        | 0xc4     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_44`](#alert_regwen)                                        | 0xc8     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_45`](#alert_regwen)                                        | 0xcc     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_46`](#alert_regwen)                                        | 0xd0     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_47`](#alert_regwen)                                        | 0xd4     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_48`](#alert_regwen)                                        | 0xd8     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_49`](#alert_regwen)                                        | 0xdc     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_50`](#alert_regwen)                                        | 0xe0     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_51`](#alert_regwen)                                        | 0xe4     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_52`](#alert_regwen)                                        | 0xe8     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_53`](#alert_regwen)                                        | 0xec     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_54`](#alert_regwen)                                        | 0xf0     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_55`](#alert_regwen)                                        | 0xf4     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_56`](#alert_regwen)                                        | 0xf8     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_57`](#alert_regwen)                                        | 0xfc     |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_58`](#alert_regwen)                                        | 0x100    |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_59`](#alert_regwen)                                        | 0x104    |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_60`](#alert_regwen)                                        | 0x108    |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_61`](#alert_regwen)                                        | 0x10c    |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_62`](#alert_regwen)                                        | 0x110    |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_63`](#alert_regwen)                                        | 0x114    |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_REGWEN_64`](#alert_regwen)                                        | 0x118    |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`ALERT_EN_SHADOWED_0`](#alert_en_shadowed)                               | 0x11c    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_1`](#alert_en_shadowed)                               | 0x120    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_2`](#alert_en_shadowed)                               | 0x124    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_3`](#alert_en_shadowed)                               | 0x128    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_4`](#alert_en_shadowed)                               | 0x12c    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_5`](#alert_en_shadowed)                               | 0x130    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_6`](#alert_en_shadowed)                               | 0x134    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_7`](#alert_en_shadowed)                               | 0x138    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_8`](#alert_en_shadowed)                               | 0x13c    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_9`](#alert_en_shadowed)                               | 0x140    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_10`](#alert_en_shadowed)                              | 0x144    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_11`](#alert_en_shadowed)                              | 0x148    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_12`](#alert_en_shadowed)                              | 0x14c    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_13`](#alert_en_shadowed)                              | 0x150    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_14`](#alert_en_shadowed)                              | 0x154    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_15`](#alert_en_shadowed)                              | 0x158    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_16`](#alert_en_shadowed)                              | 0x15c    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_17`](#alert_en_shadowed)                              | 0x160    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_18`](#alert_en_shadowed)                              | 0x164    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_19`](#alert_en_shadowed)                              | 0x168    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_20`](#alert_en_shadowed)                              | 0x16c    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_21`](#alert_en_shadowed)                              | 0x170    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_22`](#alert_en_shadowed)                              | 0x174    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_23`](#alert_en_shadowed)                              | 0x178    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_24`](#alert_en_shadowed)                              | 0x17c    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_25`](#alert_en_shadowed)                              | 0x180    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_26`](#alert_en_shadowed)                              | 0x184    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_27`](#alert_en_shadowed)                              | 0x188    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_28`](#alert_en_shadowed)                              | 0x18c    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_29`](#alert_en_shadowed)                              | 0x190    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_30`](#alert_en_shadowed)                              | 0x194    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_31`](#alert_en_shadowed)                              | 0x198    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_32`](#alert_en_shadowed)                              | 0x19c    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_33`](#alert_en_shadowed)                              | 0x1a0    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_34`](#alert_en_shadowed)                              | 0x1a4    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_35`](#alert_en_shadowed)                              | 0x1a8    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_36`](#alert_en_shadowed)                              | 0x1ac    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_37`](#alert_en_shadowed)                              | 0x1b0    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_38`](#alert_en_shadowed)                              | 0x1b4    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_39`](#alert_en_shadowed)                              | 0x1b8    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_40`](#alert_en_shadowed)                              | 0x1bc    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_41`](#alert_en_shadowed)                              | 0x1c0    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_42`](#alert_en_shadowed)                              | 0x1c4    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_43`](#alert_en_shadowed)                              | 0x1c8    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_44`](#alert_en_shadowed)                              | 0x1cc    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_45`](#alert_en_shadowed)                              | 0x1d0    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_46`](#alert_en_shadowed)                              | 0x1d4    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_47`](#alert_en_shadowed)                              | 0x1d8    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_48`](#alert_en_shadowed)                              | 0x1dc    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_49`](#alert_en_shadowed)                              | 0x1e0    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_50`](#alert_en_shadowed)                              | 0x1e4    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_51`](#alert_en_shadowed)                              | 0x1e8    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_52`](#alert_en_shadowed)                              | 0x1ec    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_53`](#alert_en_shadowed)                              | 0x1f0    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_54`](#alert_en_shadowed)                              | 0x1f4    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_55`](#alert_en_shadowed)                              | 0x1f8    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_56`](#alert_en_shadowed)                              | 0x1fc    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_57`](#alert_en_shadowed)                              | 0x200    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_58`](#alert_en_shadowed)                              | 0x204    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_59`](#alert_en_shadowed)                              | 0x208    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_60`](#alert_en_shadowed)                              | 0x20c    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_61`](#alert_en_shadowed)                              | 0x210    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_62`](#alert_en_shadowed)                              | 0x214    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_63`](#alert_en_shadowed)                              | 0x218    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_EN_SHADOWED_64`](#alert_en_shadowed)                              | 0x21c    |        4 | Enable register for alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_0`](#alert_class_shadowed)                         | 0x220    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_1`](#alert_class_shadowed)                         | 0x224    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_2`](#alert_class_shadowed)                         | 0x228    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_3`](#alert_class_shadowed)                         | 0x22c    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_4`](#alert_class_shadowed)                         | 0x230    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_5`](#alert_class_shadowed)                         | 0x234    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_6`](#alert_class_shadowed)                         | 0x238    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_7`](#alert_class_shadowed)                         | 0x23c    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_8`](#alert_class_shadowed)                         | 0x240    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_9`](#alert_class_shadowed)                         | 0x244    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_10`](#alert_class_shadowed)                        | 0x248    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_11`](#alert_class_shadowed)                        | 0x24c    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_12`](#alert_class_shadowed)                        | 0x250    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_13`](#alert_class_shadowed)                        | 0x254    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_14`](#alert_class_shadowed)                        | 0x258    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_15`](#alert_class_shadowed)                        | 0x25c    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_16`](#alert_class_shadowed)                        | 0x260    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_17`](#alert_class_shadowed)                        | 0x264    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_18`](#alert_class_shadowed)                        | 0x268    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_19`](#alert_class_shadowed)                        | 0x26c    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_20`](#alert_class_shadowed)                        | 0x270    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_21`](#alert_class_shadowed)                        | 0x274    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_22`](#alert_class_shadowed)                        | 0x278    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_23`](#alert_class_shadowed)                        | 0x27c    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_24`](#alert_class_shadowed)                        | 0x280    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_25`](#alert_class_shadowed)                        | 0x284    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_26`](#alert_class_shadowed)                        | 0x288    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_27`](#alert_class_shadowed)                        | 0x28c    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_28`](#alert_class_shadowed)                        | 0x290    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_29`](#alert_class_shadowed)                        | 0x294    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_30`](#alert_class_shadowed)                        | 0x298    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_31`](#alert_class_shadowed)                        | 0x29c    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_32`](#alert_class_shadowed)                        | 0x2a0    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_33`](#alert_class_shadowed)                        | 0x2a4    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_34`](#alert_class_shadowed)                        | 0x2a8    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_35`](#alert_class_shadowed)                        | 0x2ac    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_36`](#alert_class_shadowed)                        | 0x2b0    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_37`](#alert_class_shadowed)                        | 0x2b4    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_38`](#alert_class_shadowed)                        | 0x2b8    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_39`](#alert_class_shadowed)                        | 0x2bc    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_40`](#alert_class_shadowed)                        | 0x2c0    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_41`](#alert_class_shadowed)                        | 0x2c4    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_42`](#alert_class_shadowed)                        | 0x2c8    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_43`](#alert_class_shadowed)                        | 0x2cc    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_44`](#alert_class_shadowed)                        | 0x2d0    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_45`](#alert_class_shadowed)                        | 0x2d4    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_46`](#alert_class_shadowed)                        | 0x2d8    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_47`](#alert_class_shadowed)                        | 0x2dc    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_48`](#alert_class_shadowed)                        | 0x2e0    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_49`](#alert_class_shadowed)                        | 0x2e4    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_50`](#alert_class_shadowed)                        | 0x2e8    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_51`](#alert_class_shadowed)                        | 0x2ec    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_52`](#alert_class_shadowed)                        | 0x2f0    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_53`](#alert_class_shadowed)                        | 0x2f4    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_54`](#alert_class_shadowed)                        | 0x2f8    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_55`](#alert_class_shadowed)                        | 0x2fc    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_56`](#alert_class_shadowed)                        | 0x300    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_57`](#alert_class_shadowed)                        | 0x304    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_58`](#alert_class_shadowed)                        | 0x308    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_59`](#alert_class_shadowed)                        | 0x30c    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_60`](#alert_class_shadowed)                        | 0x310    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_61`](#alert_class_shadowed)                        | 0x314    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_62`](#alert_class_shadowed)                        | 0x318    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_63`](#alert_class_shadowed)                        | 0x31c    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CLASS_SHADOWED_64`](#alert_class_shadowed)                        | 0x320    |        4 | Class assignment of alerts.                                                                     |
| alert_handler.[`ALERT_CAUSE_0`](#alert_cause)                                           | 0x324    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_1`](#alert_cause)                                           | 0x328    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_2`](#alert_cause)                                           | 0x32c    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_3`](#alert_cause)                                           | 0x330    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_4`](#alert_cause)                                           | 0x334    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_5`](#alert_cause)                                           | 0x338    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_6`](#alert_cause)                                           | 0x33c    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_7`](#alert_cause)                                           | 0x340    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_8`](#alert_cause)                                           | 0x344    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_9`](#alert_cause)                                           | 0x348    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_10`](#alert_cause)                                          | 0x34c    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_11`](#alert_cause)                                          | 0x350    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_12`](#alert_cause)                                          | 0x354    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_13`](#alert_cause)                                          | 0x358    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_14`](#alert_cause)                                          | 0x35c    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_15`](#alert_cause)                                          | 0x360    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_16`](#alert_cause)                                          | 0x364    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_17`](#alert_cause)                                          | 0x368    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_18`](#alert_cause)                                          | 0x36c    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_19`](#alert_cause)                                          | 0x370    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_20`](#alert_cause)                                          | 0x374    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_21`](#alert_cause)                                          | 0x378    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_22`](#alert_cause)                                          | 0x37c    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_23`](#alert_cause)                                          | 0x380    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_24`](#alert_cause)                                          | 0x384    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_25`](#alert_cause)                                          | 0x388    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_26`](#alert_cause)                                          | 0x38c    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_27`](#alert_cause)                                          | 0x390    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_28`](#alert_cause)                                          | 0x394    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_29`](#alert_cause)                                          | 0x398    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_30`](#alert_cause)                                          | 0x39c    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_31`](#alert_cause)                                          | 0x3a0    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_32`](#alert_cause)                                          | 0x3a4    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_33`](#alert_cause)                                          | 0x3a8    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_34`](#alert_cause)                                          | 0x3ac    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_35`](#alert_cause)                                          | 0x3b0    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_36`](#alert_cause)                                          | 0x3b4    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_37`](#alert_cause)                                          | 0x3b8    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_38`](#alert_cause)                                          | 0x3bc    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_39`](#alert_cause)                                          | 0x3c0    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_40`](#alert_cause)                                          | 0x3c4    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_41`](#alert_cause)                                          | 0x3c8    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_42`](#alert_cause)                                          | 0x3cc    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_43`](#alert_cause)                                          | 0x3d0    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_44`](#alert_cause)                                          | 0x3d4    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_45`](#alert_cause)                                          | 0x3d8    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_46`](#alert_cause)                                          | 0x3dc    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_47`](#alert_cause)                                          | 0x3e0    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_48`](#alert_cause)                                          | 0x3e4    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_49`](#alert_cause)                                          | 0x3e8    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_50`](#alert_cause)                                          | 0x3ec    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_51`](#alert_cause)                                          | 0x3f0    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_52`](#alert_cause)                                          | 0x3f4    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_53`](#alert_cause)                                          | 0x3f8    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_54`](#alert_cause)                                          | 0x3fc    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_55`](#alert_cause)                                          | 0x400    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_56`](#alert_cause)                                          | 0x404    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_57`](#alert_cause)                                          | 0x408    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_58`](#alert_cause)                                          | 0x40c    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_59`](#alert_cause)                                          | 0x410    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_60`](#alert_cause)                                          | 0x414    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_61`](#alert_cause)                                          | 0x418    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_62`](#alert_cause)                                          | 0x41c    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_63`](#alert_cause)                                          | 0x420    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`ALERT_CAUSE_64`](#alert_cause)                                          | 0x424    |        4 | Alert Cause Register                                                                            |
| alert_handler.[`LOC_ALERT_REGWEN_0`](#loc_alert_regwen)                                 | 0x428    |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`LOC_ALERT_REGWEN_1`](#loc_alert_regwen)                                 | 0x42c    |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`LOC_ALERT_REGWEN_2`](#loc_alert_regwen)                                 | 0x430    |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`LOC_ALERT_REGWEN_3`](#loc_alert_regwen)                                 | 0x434    |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`LOC_ALERT_REGWEN_4`](#loc_alert_regwen)                                 | 0x438    |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`LOC_ALERT_REGWEN_5`](#loc_alert_regwen)                                 | 0x43c    |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`LOC_ALERT_REGWEN_6`](#loc_alert_regwen)                                 | 0x440    |        4 | Register write enable for alert enable bits.                                                    |
| alert_handler.[`LOC_ALERT_EN_SHADOWED_0`](#loc_alert_en_shadowed)                       | 0x444    |        4 | Enable register for the local alerts                                                            |
| alert_handler.[`LOC_ALERT_EN_SHADOWED_1`](#loc_alert_en_shadowed)                       | 0x448    |        4 | Enable register for the local alerts                                                            |
| alert_handler.[`LOC_ALERT_EN_SHADOWED_2`](#loc_alert_en_shadowed)                       | 0x44c    |        4 | Enable register for the local alerts                                                            |
| alert_handler.[`LOC_ALERT_EN_SHADOWED_3`](#loc_alert_en_shadowed)                       | 0x450    |        4 | Enable register for the local alerts                                                            |
| alert_handler.[`LOC_ALERT_EN_SHADOWED_4`](#loc_alert_en_shadowed)                       | 0x454    |        4 | Enable register for the local alerts                                                            |
| alert_handler.[`LOC_ALERT_EN_SHADOWED_5`](#loc_alert_en_shadowed)                       | 0x458    |        4 | Enable register for the local alerts                                                            |
| alert_handler.[`LOC_ALERT_EN_SHADOWED_6`](#loc_alert_en_shadowed)                       | 0x45c    |        4 | Enable register for the local alerts                                                            |
| alert_handler.[`LOC_ALERT_CLASS_SHADOWED_0`](#loc_alert_class_shadowed)                 | 0x460    |        4 | Class assignment of the local alerts                                                            |
| alert_handler.[`LOC_ALERT_CLASS_SHADOWED_1`](#loc_alert_class_shadowed)                 | 0x464    |        4 | Class assignment of the local alerts                                                            |
| alert_handler.[`LOC_ALERT_CLASS_SHADOWED_2`](#loc_alert_class_shadowed)                 | 0x468    |        4 | Class assignment of the local alerts                                                            |
| alert_handler.[`LOC_ALERT_CLASS_SHADOWED_3`](#loc_alert_class_shadowed)                 | 0x46c    |        4 | Class assignment of the local alerts                                                            |
| alert_handler.[`LOC_ALERT_CLASS_SHADOWED_4`](#loc_alert_class_shadowed)                 | 0x470    |        4 | Class assignment of the local alerts                                                            |
| alert_handler.[`LOC_ALERT_CLASS_SHADOWED_5`](#loc_alert_class_shadowed)                 | 0x474    |        4 | Class assignment of the local alerts                                                            |
| alert_handler.[`LOC_ALERT_CLASS_SHADOWED_6`](#loc_alert_class_shadowed)                 | 0x478    |        4 | Class assignment of the local alerts                                                            |
| alert_handler.[`LOC_ALERT_CAUSE_0`](#loc_alert_cause)                                   | 0x47c    |        4 | Alert Cause Register for the local alerts                                                       |
| alert_handler.[`LOC_ALERT_CAUSE_1`](#loc_alert_cause)                                   | 0x480    |        4 | Alert Cause Register for the local alerts                                                       |
| alert_handler.[`LOC_ALERT_CAUSE_2`](#loc_alert_cause)                                   | 0x484    |        4 | Alert Cause Register for the local alerts                                                       |
| alert_handler.[`LOC_ALERT_CAUSE_3`](#loc_alert_cause)                                   | 0x488    |        4 | Alert Cause Register for the local alerts                                                       |
| alert_handler.[`LOC_ALERT_CAUSE_4`](#loc_alert_cause)                                   | 0x48c    |        4 | Alert Cause Register for the local alerts                                                       |
| alert_handler.[`LOC_ALERT_CAUSE_5`](#loc_alert_cause)                                   | 0x490    |        4 | Alert Cause Register for the local alerts                                                       |
| alert_handler.[`LOC_ALERT_CAUSE_6`](#loc_alert_cause)                                   | 0x494    |        4 | Alert Cause Register for the local alerts                                                       |
| alert_handler.[`CLASSA_REGWEN`](#classa_regwen)                                         | 0x498    |        4 | Lock bit for Class A configuration.                                                             |
| alert_handler.[`CLASSA_CTRL_SHADOWED`](#classa_ctrl_shadowed)                           | 0x49c    |        4 | Escalation control register for alert Class A. Can not be modified if !!CLASSA_REGWEN is false. |
| alert_handler.[`CLASSA_CLR_REGWEN`](#classa_clr_regwen)                                 | 0x4a0    |        4 | Clear enable for escalation protocol of Class A alerts.                                         |
| alert_handler.[`CLASSA_CLR_SHADOWED`](#classa_clr_shadowed)                             | 0x4a4    |        4 | Clear for escalation protocol of Class A.                                                       |
| alert_handler.[`CLASSA_ACCUM_CNT`](#classa_accum_cnt)                                   | 0x4a8    |        4 | Current accumulation value for alert Class A. Software can clear this register                  |
| alert_handler.[`CLASSA_ACCUM_THRESH_SHADOWED`](#classa_accum_thresh_shadowed)           | 0x4ac    |        4 | Accumulation threshold value for alert Class A.                                                 |
| alert_handler.[`CLASSA_TIMEOUT_CYC_SHADOWED`](#classa_timeout_cyc_shadowed)             | 0x4b0    |        4 | Interrupt timeout in cycles.                                                                    |
| alert_handler.[`CLASSA_CRASHDUMP_TRIGGER_SHADOWED`](#classa_crashdump_trigger_shadowed) | 0x4b4    |        4 | Crashdump trigger configuration for Class A.                                                    |
| alert_handler.[`CLASSA_PHASE0_CYC_SHADOWED`](#classa_phase0_cyc_shadowed)               | 0x4b8    |        4 | Duration of escalation phase 0 for Class A.                                                     |
| alert_handler.[`CLASSA_PHASE1_CYC_SHADOWED`](#classa_phase1_cyc_shadowed)               | 0x4bc    |        4 | Duration of escalation phase 1 for Class A.                                                     |
| alert_handler.[`CLASSA_PHASE2_CYC_SHADOWED`](#classa_phase2_cyc_shadowed)               | 0x4c0    |        4 | Duration of escalation phase 2 for Class A.                                                     |
| alert_handler.[`CLASSA_PHASE3_CYC_SHADOWED`](#classa_phase3_cyc_shadowed)               | 0x4c4    |        4 | Duration of escalation phase 3 for Class A.                                                     |
| alert_handler.[`CLASSA_ESC_CNT`](#classa_esc_cnt)                                       | 0x4c8    |        4 | Escalation counter in cycles for Class A.                                                       |
| alert_handler.[`CLASSA_STATE`](#classa_state)                                           | 0x4cc    |        4 | Current escalation state of Class A. See also !!CLASSA_ESC_CNT.                                 |
| alert_handler.[`CLASSB_REGWEN`](#classb_regwen)                                         | 0x4d0    |        4 | Lock bit for Class B configuration.                                                             |
| alert_handler.[`CLASSB_CTRL_SHADOWED`](#classb_ctrl_shadowed)                           | 0x4d4    |        4 | Escalation control register for alert Class B. Can not be modified if !!CLASSB_REGWEN is false. |
| alert_handler.[`CLASSB_CLR_REGWEN`](#classb_clr_regwen)                                 | 0x4d8    |        4 | Clear enable for escalation protocol of Class B alerts.                                         |
| alert_handler.[`CLASSB_CLR_SHADOWED`](#classb_clr_shadowed)                             | 0x4dc    |        4 | Clear for escalation protocol of Class B.                                                       |
| alert_handler.[`CLASSB_ACCUM_CNT`](#classb_accum_cnt)                                   | 0x4e0    |        4 | Current accumulation value for alert Class B. Software can clear this register                  |
| alert_handler.[`CLASSB_ACCUM_THRESH_SHADOWED`](#classb_accum_thresh_shadowed)           | 0x4e4    |        4 | Accumulation threshold value for alert Class B.                                                 |
| alert_handler.[`CLASSB_TIMEOUT_CYC_SHADOWED`](#classb_timeout_cyc_shadowed)             | 0x4e8    |        4 | Interrupt timeout in cycles.                                                                    |
| alert_handler.[`CLASSB_CRASHDUMP_TRIGGER_SHADOWED`](#classb_crashdump_trigger_shadowed) | 0x4ec    |        4 | Crashdump trigger configuration for Class B.                                                    |
| alert_handler.[`CLASSB_PHASE0_CYC_SHADOWED`](#classb_phase0_cyc_shadowed)               | 0x4f0    |        4 | Duration of escalation phase 0 for Class B.                                                     |
| alert_handler.[`CLASSB_PHASE1_CYC_SHADOWED`](#classb_phase1_cyc_shadowed)               | 0x4f4    |        4 | Duration of escalation phase 1 for Class B.                                                     |
| alert_handler.[`CLASSB_PHASE2_CYC_SHADOWED`](#classb_phase2_cyc_shadowed)               | 0x4f8    |        4 | Duration of escalation phase 2 for Class B.                                                     |
| alert_handler.[`CLASSB_PHASE3_CYC_SHADOWED`](#classb_phase3_cyc_shadowed)               | 0x4fc    |        4 | Duration of escalation phase 3 for Class B.                                                     |
| alert_handler.[`CLASSB_ESC_CNT`](#classb_esc_cnt)                                       | 0x500    |        4 | Escalation counter in cycles for Class B.                                                       |
| alert_handler.[`CLASSB_STATE`](#classb_state)                                           | 0x504    |        4 | Current escalation state of Class B. See also !!CLASSB_ESC_CNT.                                 |
| alert_handler.[`CLASSC_REGWEN`](#classc_regwen)                                         | 0x508    |        4 | Lock bit for Class C configuration.                                                             |
| alert_handler.[`CLASSC_CTRL_SHADOWED`](#classc_ctrl_shadowed)                           | 0x50c    |        4 | Escalation control register for alert Class C. Can not be modified if !!CLASSC_REGWEN is false. |
| alert_handler.[`CLASSC_CLR_REGWEN`](#classc_clr_regwen)                                 | 0x510    |        4 | Clear enable for escalation protocol of Class C alerts.                                         |
| alert_handler.[`CLASSC_CLR_SHADOWED`](#classc_clr_shadowed)                             | 0x514    |        4 | Clear for escalation protocol of Class C.                                                       |
| alert_handler.[`CLASSC_ACCUM_CNT`](#classc_accum_cnt)                                   | 0x518    |        4 | Current accumulation value for alert Class C. Software can clear this register                  |
| alert_handler.[`CLASSC_ACCUM_THRESH_SHADOWED`](#classc_accum_thresh_shadowed)           | 0x51c    |        4 | Accumulation threshold value for alert Class C.                                                 |
| alert_handler.[`CLASSC_TIMEOUT_CYC_SHADOWED`](#classc_timeout_cyc_shadowed)             | 0x520    |        4 | Interrupt timeout in cycles.                                                                    |
| alert_handler.[`CLASSC_CRASHDUMP_TRIGGER_SHADOWED`](#classc_crashdump_trigger_shadowed) | 0x524    |        4 | Crashdump trigger configuration for Class C.                                                    |
| alert_handler.[`CLASSC_PHASE0_CYC_SHADOWED`](#classc_phase0_cyc_shadowed)               | 0x528    |        4 | Duration of escalation phase 0 for Class C.                                                     |
| alert_handler.[`CLASSC_PHASE1_CYC_SHADOWED`](#classc_phase1_cyc_shadowed)               | 0x52c    |        4 | Duration of escalation phase 1 for Class C.                                                     |
| alert_handler.[`CLASSC_PHASE2_CYC_SHADOWED`](#classc_phase2_cyc_shadowed)               | 0x530    |        4 | Duration of escalation phase 2 for Class C.                                                     |
| alert_handler.[`CLASSC_PHASE3_CYC_SHADOWED`](#classc_phase3_cyc_shadowed)               | 0x534    |        4 | Duration of escalation phase 3 for Class C.                                                     |
| alert_handler.[`CLASSC_ESC_CNT`](#classc_esc_cnt)                                       | 0x538    |        4 | Escalation counter in cycles for Class C.                                                       |
| alert_handler.[`CLASSC_STATE`](#classc_state)                                           | 0x53c    |        4 | Current escalation state of Class C. See also !!CLASSC_ESC_CNT.                                 |
| alert_handler.[`CLASSD_REGWEN`](#classd_regwen)                                         | 0x540    |        4 | Lock bit for Class D configuration.                                                             |
| alert_handler.[`CLASSD_CTRL_SHADOWED`](#classd_ctrl_shadowed)                           | 0x544    |        4 | Escalation control register for alert Class D. Can not be modified if !!CLASSD_REGWEN is false. |
| alert_handler.[`CLASSD_CLR_REGWEN`](#classd_clr_regwen)                                 | 0x548    |        4 | Clear enable for escalation protocol of Class D alerts.                                         |
| alert_handler.[`CLASSD_CLR_SHADOWED`](#classd_clr_shadowed)                             | 0x54c    |        4 | Clear for escalation protocol of Class D.                                                       |
| alert_handler.[`CLASSD_ACCUM_CNT`](#classd_accum_cnt)                                   | 0x550    |        4 | Current accumulation value for alert Class D. Software can clear this register                  |
| alert_handler.[`CLASSD_ACCUM_THRESH_SHADOWED`](#classd_accum_thresh_shadowed)           | 0x554    |        4 | Accumulation threshold value for alert Class D.                                                 |
| alert_handler.[`CLASSD_TIMEOUT_CYC_SHADOWED`](#classd_timeout_cyc_shadowed)             | 0x558    |        4 | Interrupt timeout in cycles.                                                                    |
| alert_handler.[`CLASSD_CRASHDUMP_TRIGGER_SHADOWED`](#classd_crashdump_trigger_shadowed) | 0x55c    |        4 | Crashdump trigger configuration for Class D.                                                    |
| alert_handler.[`CLASSD_PHASE0_CYC_SHADOWED`](#classd_phase0_cyc_shadowed)               | 0x560    |        4 | Duration of escalation phase 0 for Class D.                                                     |
| alert_handler.[`CLASSD_PHASE1_CYC_SHADOWED`](#classd_phase1_cyc_shadowed)               | 0x564    |        4 | Duration of escalation phase 1 for Class D.                                                     |
| alert_handler.[`CLASSD_PHASE2_CYC_SHADOWED`](#classd_phase2_cyc_shadowed)               | 0x568    |        4 | Duration of escalation phase 2 for Class D.                                                     |
| alert_handler.[`CLASSD_PHASE3_CYC_SHADOWED`](#classd_phase3_cyc_shadowed)               | 0x56c    |        4 | Duration of escalation phase 3 for Class D.                                                     |
| alert_handler.[`CLASSD_ESC_CNT`](#classd_esc_cnt)                                       | 0x570    |        4 | Escalation counter in cycles for Class D.                                                       |
| alert_handler.[`CLASSD_STATE`](#classd_state)                                           | 0x574    |        4 | Current escalation state of Class D. See also !!CLASSD_ESC_CNT.                                 |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "classa", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "classb", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "classc", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "classd", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------------------------------------------------|
|  31:4  |        |         |        | Reserved                                                                                                                   |
|   3    |  rw1c  |   0x0   | classd | Interrupt state bit of Class D. Set by HW in case an alert within this class triggered. Defaults true, write one to clear. |
|   2    |  rw1c  |   0x0   | classc | Interrupt state bit of Class C. Set by HW in case an alert within this class triggered. Defaults true, write one to clear. |
|   1    |  rw1c  |   0x0   | classb | Interrupt state bit of Class B. Set by HW in case an alert within this class triggered. Defaults true, write one to clear. |
|   0    |  rw1c  |   0x0   | classa | Interrupt state bit of Class A. Set by HW in case an alert within this class triggered. Defaults true, write one to clear. |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "classa", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "classb", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "classc", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "classd", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                      |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------|
|  31:4  |        |         |        | Reserved                                                         |
|   3    |   rw   |   0x0   | classd | Enable interrupt when [`INTR_STATE.classd`](#intr_state) is set. |
|   2    |   rw   |   0x0   | classc | Enable interrupt when [`INTR_STATE.classc`](#intr_state) is set. |
|   1    |   rw   |   0x0   | classb | Enable interrupt when [`INTR_STATE.classb`](#intr_state) is set. |
|   0    |   rw   |   0x0   | classa | Enable interrupt when [`INTR_STATE.classa`](#intr_state) is set. |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "classa", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "classb", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "classc", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "classd", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                               |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------|
|  31:4  |        |         |        | Reserved                                                  |
|   3    |   wo   |   0x0   | classd | Write 1 to force [`INTR_STATE.classd`](#intr_state) to 1. |
|   2    |   wo   |   0x0   | classc | Write 1 to force [`INTR_STATE.classc`](#intr_state) to 1. |
|   1    |   wo   |   0x0   | classb | Write 1 to force [`INTR_STATE.classb`](#intr_state) to 1. |
|   0    |   wo   |   0x0   | classa | Write 1 to force [`INTR_STATE.classa`](#intr_state) to 1. |

## PING_TIMER_REGWEN
Register write enable for [`PING_TIMEOUT_CYC_SHADOWED`](#ping_timeout_cyc_shadowed) and [`PING_TIMER_EN_SHADOWED.`](#ping_timer_en_shadowed)
- Offset: `0xc`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "PING_TIMER_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name                                                       |
|:------:|:------:|:-------:|:-----------------------------------------------------------|
|  31:1  |        |         | Reserved                                                   |
|   0    |  rw0c  |   0x1   | [PING_TIMER_REGWEN](#ping_timer_regwen--ping_timer_regwen) |

### PING_TIMER_REGWEN . PING_TIMER_REGWEN
When true, the [`PING_TIMEOUT_CYC_SHADOWED`](#ping_timeout_cyc_shadowed) and [`PING_TIMER_EN_SHADOWED`](#ping_timer_en_shadowed) registers can be modified.
When false, they become read-only. Defaults true, write one to clear.
This should be cleared once the alert handler has been configured and the ping
timer mechanism has been kicked off.

## PING_TIMEOUT_CYC_SHADOWED
Ping timeout cycle count.
- Offset: `0x10`
- Reset default: `0x100`
- Reset mask: `0xffff`
- Register enable: [`PING_TIMER_REGWEN`](#ping_timer_regwen)

### Fields

```wavejson
{"reg": [{"name": "PING_TIMEOUT_CYC_SHADOWED", "bits": 16, "attr": ["rw"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                                               |
|:------:|:------:|:-------:|:-----------------------------------------------------------------------------------|
| 31:16  |        |         | Reserved                                                                           |
|  15:0  |   rw   |  0x100  | [PING_TIMEOUT_CYC_SHADOWED](#ping_timeout_cyc_shadowed--ping_timeout_cyc_shadowed) |

### PING_TIMEOUT_CYC_SHADOWED . PING_TIMEOUT_CYC_SHADOWED
Timeout value in cycles.
If an alert receiver or an escalation sender does not respond to a ping within this timeout window, a pingfail alert will be raised.
It is recommended to set this value to the equivalent of 256 cycles of the slowest alert sender clock domain in the system (or greater).

## PING_TIMER_EN_SHADOWED
Ping timer enable.
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0x1`
- Register enable: [`PING_TIMER_REGWEN`](#ping_timer_regwen)

### Fields

```wavejson
{"reg": [{"name": "PING_TIMER_EN_SHADOWED", "bits": 1, "attr": ["rw1s"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 240}}
```

|  Bits  |  Type  |  Reset  | Name                   | Description                                                                                                                                                                                                   |
|:------:|:------:|:-------:|:-----------------------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                        | Reserved                                                                                                                                                                                                      |
|   0    |  rw1s  |   0x0   | PING_TIMER_EN_SHADOWED | Setting this to 1 enables the ping timer mechanism. This bit cannot be cleared to 0 once it has been set to 1. Note that the alert pinging mechanism will only ping alerts that have been enabled and locked. |

## ALERT_REGWEN
Register write enable for alert enable bits.
- Reset default: `0x1`
- Reset mask: `0x1`

### Instances

| Name            | Offset   |
|:----------------|:---------|
| ALERT_REGWEN_0  | 0x18     |
| ALERT_REGWEN_1  | 0x1c     |
| ALERT_REGWEN_2  | 0x20     |
| ALERT_REGWEN_3  | 0x24     |
| ALERT_REGWEN_4  | 0x28     |
| ALERT_REGWEN_5  | 0x2c     |
| ALERT_REGWEN_6  | 0x30     |
| ALERT_REGWEN_7  | 0x34     |
| ALERT_REGWEN_8  | 0x38     |
| ALERT_REGWEN_9  | 0x3c     |
| ALERT_REGWEN_10 | 0x40     |
| ALERT_REGWEN_11 | 0x44     |
| ALERT_REGWEN_12 | 0x48     |
| ALERT_REGWEN_13 | 0x4c     |
| ALERT_REGWEN_14 | 0x50     |
| ALERT_REGWEN_15 | 0x54     |
| ALERT_REGWEN_16 | 0x58     |
| ALERT_REGWEN_17 | 0x5c     |
| ALERT_REGWEN_18 | 0x60     |
| ALERT_REGWEN_19 | 0x64     |
| ALERT_REGWEN_20 | 0x68     |
| ALERT_REGWEN_21 | 0x6c     |
| ALERT_REGWEN_22 | 0x70     |
| ALERT_REGWEN_23 | 0x74     |
| ALERT_REGWEN_24 | 0x78     |
| ALERT_REGWEN_25 | 0x7c     |
| ALERT_REGWEN_26 | 0x80     |
| ALERT_REGWEN_27 | 0x84     |
| ALERT_REGWEN_28 | 0x88     |
| ALERT_REGWEN_29 | 0x8c     |
| ALERT_REGWEN_30 | 0x90     |
| ALERT_REGWEN_31 | 0x94     |
| ALERT_REGWEN_32 | 0x98     |
| ALERT_REGWEN_33 | 0x9c     |
| ALERT_REGWEN_34 | 0xa0     |
| ALERT_REGWEN_35 | 0xa4     |
| ALERT_REGWEN_36 | 0xa8     |
| ALERT_REGWEN_37 | 0xac     |
| ALERT_REGWEN_38 | 0xb0     |
| ALERT_REGWEN_39 | 0xb4     |
| ALERT_REGWEN_40 | 0xb8     |
| ALERT_REGWEN_41 | 0xbc     |
| ALERT_REGWEN_42 | 0xc0     |
| ALERT_REGWEN_43 | 0xc4     |
| ALERT_REGWEN_44 | 0xc8     |
| ALERT_REGWEN_45 | 0xcc     |
| ALERT_REGWEN_46 | 0xd0     |
| ALERT_REGWEN_47 | 0xd4     |
| ALERT_REGWEN_48 | 0xd8     |
| ALERT_REGWEN_49 | 0xdc     |
| ALERT_REGWEN_50 | 0xe0     |
| ALERT_REGWEN_51 | 0xe4     |
| ALERT_REGWEN_52 | 0xe8     |
| ALERT_REGWEN_53 | 0xec     |
| ALERT_REGWEN_54 | 0xf0     |
| ALERT_REGWEN_55 | 0xf4     |
| ALERT_REGWEN_56 | 0xf8     |
| ALERT_REGWEN_57 | 0xfc     |
| ALERT_REGWEN_58 | 0x100    |
| ALERT_REGWEN_59 | 0x104    |
| ALERT_REGWEN_60 | 0x108    |
| ALERT_REGWEN_61 | 0x10c    |
| ALERT_REGWEN_62 | 0x110    |
| ALERT_REGWEN_63 | 0x114    |
| ALERT_REGWEN_64 | 0x118    |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                    |
|:------:|:------:|:-------:|:------------------------|
|  31:1  |        |         | Reserved                |
|   0    |  rw0c  |   0x1   | [EN](#alert_regwen--en) |

### ALERT_REGWEN . EN
Alert configuration write enable bit.
If this is cleared to 0, the corresponding [`ALERT_EN_SHADOWED`](#alert_en_shadowed)
and [`ALERT_CLASS_SHADOWED`](#alert_class_shadowed) bits are not writable anymore.

Note that the alert pinging mechanism will only ping alerts that have been enabled and locked.

## ALERT_EN_SHADOWED
Enable register for alerts.
- Reset default: `0x0`
- Reset mask: `0x1`
- Register enable: [`ALERT_REGWEN`](#alert_regwen)

### Instances

| Name                 | Offset   |
|:---------------------|:---------|
| ALERT_EN_SHADOWED_0  | 0x11c    |
| ALERT_EN_SHADOWED_1  | 0x120    |
| ALERT_EN_SHADOWED_2  | 0x124    |
| ALERT_EN_SHADOWED_3  | 0x128    |
| ALERT_EN_SHADOWED_4  | 0x12c    |
| ALERT_EN_SHADOWED_5  | 0x130    |
| ALERT_EN_SHADOWED_6  | 0x134    |
| ALERT_EN_SHADOWED_7  | 0x138    |
| ALERT_EN_SHADOWED_8  | 0x13c    |
| ALERT_EN_SHADOWED_9  | 0x140    |
| ALERT_EN_SHADOWED_10 | 0x144    |
| ALERT_EN_SHADOWED_11 | 0x148    |
| ALERT_EN_SHADOWED_12 | 0x14c    |
| ALERT_EN_SHADOWED_13 | 0x150    |
| ALERT_EN_SHADOWED_14 | 0x154    |
| ALERT_EN_SHADOWED_15 | 0x158    |
| ALERT_EN_SHADOWED_16 | 0x15c    |
| ALERT_EN_SHADOWED_17 | 0x160    |
| ALERT_EN_SHADOWED_18 | 0x164    |
| ALERT_EN_SHADOWED_19 | 0x168    |
| ALERT_EN_SHADOWED_20 | 0x16c    |
| ALERT_EN_SHADOWED_21 | 0x170    |
| ALERT_EN_SHADOWED_22 | 0x174    |
| ALERT_EN_SHADOWED_23 | 0x178    |
| ALERT_EN_SHADOWED_24 | 0x17c    |
| ALERT_EN_SHADOWED_25 | 0x180    |
| ALERT_EN_SHADOWED_26 | 0x184    |
| ALERT_EN_SHADOWED_27 | 0x188    |
| ALERT_EN_SHADOWED_28 | 0x18c    |
| ALERT_EN_SHADOWED_29 | 0x190    |
| ALERT_EN_SHADOWED_30 | 0x194    |
| ALERT_EN_SHADOWED_31 | 0x198    |
| ALERT_EN_SHADOWED_32 | 0x19c    |
| ALERT_EN_SHADOWED_33 | 0x1a0    |
| ALERT_EN_SHADOWED_34 | 0x1a4    |
| ALERT_EN_SHADOWED_35 | 0x1a8    |
| ALERT_EN_SHADOWED_36 | 0x1ac    |
| ALERT_EN_SHADOWED_37 | 0x1b0    |
| ALERT_EN_SHADOWED_38 | 0x1b4    |
| ALERT_EN_SHADOWED_39 | 0x1b8    |
| ALERT_EN_SHADOWED_40 | 0x1bc    |
| ALERT_EN_SHADOWED_41 | 0x1c0    |
| ALERT_EN_SHADOWED_42 | 0x1c4    |
| ALERT_EN_SHADOWED_43 | 0x1c8    |
| ALERT_EN_SHADOWED_44 | 0x1cc    |
| ALERT_EN_SHADOWED_45 | 0x1d0    |
| ALERT_EN_SHADOWED_46 | 0x1d4    |
| ALERT_EN_SHADOWED_47 | 0x1d8    |
| ALERT_EN_SHADOWED_48 | 0x1dc    |
| ALERT_EN_SHADOWED_49 | 0x1e0    |
| ALERT_EN_SHADOWED_50 | 0x1e4    |
| ALERT_EN_SHADOWED_51 | 0x1e8    |
| ALERT_EN_SHADOWED_52 | 0x1ec    |
| ALERT_EN_SHADOWED_53 | 0x1f0    |
| ALERT_EN_SHADOWED_54 | 0x1f4    |
| ALERT_EN_SHADOWED_55 | 0x1f8    |
| ALERT_EN_SHADOWED_56 | 0x1fc    |
| ALERT_EN_SHADOWED_57 | 0x200    |
| ALERT_EN_SHADOWED_58 | 0x204    |
| ALERT_EN_SHADOWED_59 | 0x208    |
| ALERT_EN_SHADOWED_60 | 0x20c    |
| ALERT_EN_SHADOWED_61 | 0x210    |
| ALERT_EN_SHADOWED_62 | 0x214    |
| ALERT_EN_SHADOWED_63 | 0x218    |
| ALERT_EN_SHADOWED_64 | 0x21c    |


### Fields

```wavejson
{"reg": [{"name": "EN_A", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                      |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                                         |
|   0    |   rw   |   0x0   | EN_A   | Alert enable bit. Note that the alert pinging mechanism will only ping alerts that have been enabled and locked. |

## ALERT_CLASS_SHADOWED
Class assignment of alerts.
- Reset default: `0x0`
- Reset mask: `0x3`
- Register enable: [`ALERT_REGWEN`](#alert_regwen)

### Instances

| Name                    | Offset   |
|:------------------------|:---------|
| ALERT_CLASS_SHADOWED_0  | 0x220    |
| ALERT_CLASS_SHADOWED_1  | 0x224    |
| ALERT_CLASS_SHADOWED_2  | 0x228    |
| ALERT_CLASS_SHADOWED_3  | 0x22c    |
| ALERT_CLASS_SHADOWED_4  | 0x230    |
| ALERT_CLASS_SHADOWED_5  | 0x234    |
| ALERT_CLASS_SHADOWED_6  | 0x238    |
| ALERT_CLASS_SHADOWED_7  | 0x23c    |
| ALERT_CLASS_SHADOWED_8  | 0x240    |
| ALERT_CLASS_SHADOWED_9  | 0x244    |
| ALERT_CLASS_SHADOWED_10 | 0x248    |
| ALERT_CLASS_SHADOWED_11 | 0x24c    |
| ALERT_CLASS_SHADOWED_12 | 0x250    |
| ALERT_CLASS_SHADOWED_13 | 0x254    |
| ALERT_CLASS_SHADOWED_14 | 0x258    |
| ALERT_CLASS_SHADOWED_15 | 0x25c    |
| ALERT_CLASS_SHADOWED_16 | 0x260    |
| ALERT_CLASS_SHADOWED_17 | 0x264    |
| ALERT_CLASS_SHADOWED_18 | 0x268    |
| ALERT_CLASS_SHADOWED_19 | 0x26c    |
| ALERT_CLASS_SHADOWED_20 | 0x270    |
| ALERT_CLASS_SHADOWED_21 | 0x274    |
| ALERT_CLASS_SHADOWED_22 | 0x278    |
| ALERT_CLASS_SHADOWED_23 | 0x27c    |
| ALERT_CLASS_SHADOWED_24 | 0x280    |
| ALERT_CLASS_SHADOWED_25 | 0x284    |
| ALERT_CLASS_SHADOWED_26 | 0x288    |
| ALERT_CLASS_SHADOWED_27 | 0x28c    |
| ALERT_CLASS_SHADOWED_28 | 0x290    |
| ALERT_CLASS_SHADOWED_29 | 0x294    |
| ALERT_CLASS_SHADOWED_30 | 0x298    |
| ALERT_CLASS_SHADOWED_31 | 0x29c    |
| ALERT_CLASS_SHADOWED_32 | 0x2a0    |
| ALERT_CLASS_SHADOWED_33 | 0x2a4    |
| ALERT_CLASS_SHADOWED_34 | 0x2a8    |
| ALERT_CLASS_SHADOWED_35 | 0x2ac    |
| ALERT_CLASS_SHADOWED_36 | 0x2b0    |
| ALERT_CLASS_SHADOWED_37 | 0x2b4    |
| ALERT_CLASS_SHADOWED_38 | 0x2b8    |
| ALERT_CLASS_SHADOWED_39 | 0x2bc    |
| ALERT_CLASS_SHADOWED_40 | 0x2c0    |
| ALERT_CLASS_SHADOWED_41 | 0x2c4    |
| ALERT_CLASS_SHADOWED_42 | 0x2c8    |
| ALERT_CLASS_SHADOWED_43 | 0x2cc    |
| ALERT_CLASS_SHADOWED_44 | 0x2d0    |
| ALERT_CLASS_SHADOWED_45 | 0x2d4    |
| ALERT_CLASS_SHADOWED_46 | 0x2d8    |
| ALERT_CLASS_SHADOWED_47 | 0x2dc    |
| ALERT_CLASS_SHADOWED_48 | 0x2e0    |
| ALERT_CLASS_SHADOWED_49 | 0x2e4    |
| ALERT_CLASS_SHADOWED_50 | 0x2e8    |
| ALERT_CLASS_SHADOWED_51 | 0x2ec    |
| ALERT_CLASS_SHADOWED_52 | 0x2f0    |
| ALERT_CLASS_SHADOWED_53 | 0x2f4    |
| ALERT_CLASS_SHADOWED_54 | 0x2f8    |
| ALERT_CLASS_SHADOWED_55 | 0x2fc    |
| ALERT_CLASS_SHADOWED_56 | 0x300    |
| ALERT_CLASS_SHADOWED_57 | 0x304    |
| ALERT_CLASS_SHADOWED_58 | 0x308    |
| ALERT_CLASS_SHADOWED_59 | 0x30c    |
| ALERT_CLASS_SHADOWED_60 | 0x310    |
| ALERT_CLASS_SHADOWED_61 | 0x314    |
| ALERT_CLASS_SHADOWED_62 | 0x318    |
| ALERT_CLASS_SHADOWED_63 | 0x31c    |
| ALERT_CLASS_SHADOWED_64 | 0x320    |


### Fields

```wavejson
{"reg": [{"name": "CLASS_A", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 90}}
```

|  Bits  |  Type  |  Reset  | Name                                      |
|:------:|:------:|:-------:|:------------------------------------------|
|  31:2  |        |         | Reserved                                  |
|  1:0   |   rw   |   0x0   | [CLASS_A](#alert_class_shadowed--class_a) |

### ALERT_CLASS_SHADOWED . CLASS_A
Classification

| Value   | Name   | Description   |
|:--------|:-------|:--------------|
| 0x0     | ClassA |               |
| 0x1     | ClassB |               |
| 0x2     | ClassC |               |
| 0x3     | ClassD |               |


## ALERT_CAUSE
Alert Cause Register
- Reset default: `0x0`
- Reset mask: `0x1`

### Instances

| Name           | Offset   |
|:---------------|:---------|
| ALERT_CAUSE_0  | 0x324    |
| ALERT_CAUSE_1  | 0x328    |
| ALERT_CAUSE_2  | 0x32c    |
| ALERT_CAUSE_3  | 0x330    |
| ALERT_CAUSE_4  | 0x334    |
| ALERT_CAUSE_5  | 0x338    |
| ALERT_CAUSE_6  | 0x33c    |
| ALERT_CAUSE_7  | 0x340    |
| ALERT_CAUSE_8  | 0x344    |
| ALERT_CAUSE_9  | 0x348    |
| ALERT_CAUSE_10 | 0x34c    |
| ALERT_CAUSE_11 | 0x350    |
| ALERT_CAUSE_12 | 0x354    |
| ALERT_CAUSE_13 | 0x358    |
| ALERT_CAUSE_14 | 0x35c    |
| ALERT_CAUSE_15 | 0x360    |
| ALERT_CAUSE_16 | 0x364    |
| ALERT_CAUSE_17 | 0x368    |
| ALERT_CAUSE_18 | 0x36c    |
| ALERT_CAUSE_19 | 0x370    |
| ALERT_CAUSE_20 | 0x374    |
| ALERT_CAUSE_21 | 0x378    |
| ALERT_CAUSE_22 | 0x37c    |
| ALERT_CAUSE_23 | 0x380    |
| ALERT_CAUSE_24 | 0x384    |
| ALERT_CAUSE_25 | 0x388    |
| ALERT_CAUSE_26 | 0x38c    |
| ALERT_CAUSE_27 | 0x390    |
| ALERT_CAUSE_28 | 0x394    |
| ALERT_CAUSE_29 | 0x398    |
| ALERT_CAUSE_30 | 0x39c    |
| ALERT_CAUSE_31 | 0x3a0    |
| ALERT_CAUSE_32 | 0x3a4    |
| ALERT_CAUSE_33 | 0x3a8    |
| ALERT_CAUSE_34 | 0x3ac    |
| ALERT_CAUSE_35 | 0x3b0    |
| ALERT_CAUSE_36 | 0x3b4    |
| ALERT_CAUSE_37 | 0x3b8    |
| ALERT_CAUSE_38 | 0x3bc    |
| ALERT_CAUSE_39 | 0x3c0    |
| ALERT_CAUSE_40 | 0x3c4    |
| ALERT_CAUSE_41 | 0x3c8    |
| ALERT_CAUSE_42 | 0x3cc    |
| ALERT_CAUSE_43 | 0x3d0    |
| ALERT_CAUSE_44 | 0x3d4    |
| ALERT_CAUSE_45 | 0x3d8    |
| ALERT_CAUSE_46 | 0x3dc    |
| ALERT_CAUSE_47 | 0x3e0    |
| ALERT_CAUSE_48 | 0x3e4    |
| ALERT_CAUSE_49 | 0x3e8    |
| ALERT_CAUSE_50 | 0x3ec    |
| ALERT_CAUSE_51 | 0x3f0    |
| ALERT_CAUSE_52 | 0x3f4    |
| ALERT_CAUSE_53 | 0x3f8    |
| ALERT_CAUSE_54 | 0x3fc    |
| ALERT_CAUSE_55 | 0x400    |
| ALERT_CAUSE_56 | 0x404    |
| ALERT_CAUSE_57 | 0x408    |
| ALERT_CAUSE_58 | 0x40c    |
| ALERT_CAUSE_59 | 0x410    |
| ALERT_CAUSE_60 | 0x414    |
| ALERT_CAUSE_61 | 0x418    |
| ALERT_CAUSE_62 | 0x41c    |
| ALERT_CAUSE_63 | 0x420    |
| ALERT_CAUSE_64 | 0x424    |


### Fields

```wavejson
{"reg": [{"name": "A", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:1  |        |         |        | Reserved      |
|   0    |  rw1c  |   0x0   | A      | Cause bit     |

## LOC_ALERT_REGWEN
Register write enable for alert enable bits.
- Reset default: `0x1`
- Reset mask: `0x1`

### Instances

| Name               | Offset   |
|:-------------------|:---------|
| LOC_ALERT_REGWEN_0 | 0x428    |
| LOC_ALERT_REGWEN_1 | 0x42c    |
| LOC_ALERT_REGWEN_2 | 0x430    |
| LOC_ALERT_REGWEN_3 | 0x434    |
| LOC_ALERT_REGWEN_4 | 0x438    |
| LOC_ALERT_REGWEN_5 | 0x43c    |
| LOC_ALERT_REGWEN_6 | 0x440    |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                        |
|:------:|:------:|:-------:|:----------------------------|
|  31:1  |        |         | Reserved                    |
|   0    |  rw0c  |   0x1   | [EN](#loc_alert_regwen--en) |

### LOC_ALERT_REGWEN . EN
Alert configuration write enable bit.
If this is cleared to 0, the corresponding [`LOC_ALERT_EN_SHADOWED`](#loc_alert_en_shadowed)
and [`LOC_ALERT_CLASS_SHADOWED`](#loc_alert_class_shadowed) bits are not writable anymore.

Note that the alert pinging mechanism will only ping alerts that have been enabled and locked.

## LOC_ALERT_EN_SHADOWED
Enable register for the local alerts
"alert pingfail" (0), "escalation pingfail" (1),
"alert integfail" (2), "escalation integfail" (3),
"bus integrity failure" (4), "shadow reg update error" (5)
and "shadow reg storage error" (6).
- Reset default: `0x0`
- Reset mask: `0x1`
- Register enable: [`LOC_ALERT_REGWEN`](#loc_alert_regwen)

### Instances

| Name                    | Offset   |
|:------------------------|:---------|
| LOC_ALERT_EN_SHADOWED_0 | 0x444    |
| LOC_ALERT_EN_SHADOWED_1 | 0x448    |
| LOC_ALERT_EN_SHADOWED_2 | 0x44c    |
| LOC_ALERT_EN_SHADOWED_3 | 0x450    |
| LOC_ALERT_EN_SHADOWED_4 | 0x454    |
| LOC_ALERT_EN_SHADOWED_5 | 0x458    |
| LOC_ALERT_EN_SHADOWED_6 | 0x45c    |


### Fields

```wavejson
{"reg": [{"name": "EN_LA", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                      |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                                         |
|   0    |   rw   |   0x0   | EN_LA  | Alert enable bit. Note that the alert pinging mechanism will only ping alerts that have been enabled and locked. |

## LOC_ALERT_CLASS_SHADOWED
Class assignment of the local alerts
"alert pingfail" (0), "escalation pingfail" (1),
"alert integfail" (2), "escalation integfail" (3),
"bus integrity failure" (4), "shadow reg update error" (5)
and "shadow reg storage error" (6).
- Reset default: `0x0`
- Reset mask: `0x3`
- Register enable: [`LOC_ALERT_REGWEN`](#loc_alert_regwen)

### Instances

| Name                       | Offset   |
|:---------------------------|:---------|
| LOC_ALERT_CLASS_SHADOWED_0 | 0x460    |
| LOC_ALERT_CLASS_SHADOWED_1 | 0x464    |
| LOC_ALERT_CLASS_SHADOWED_2 | 0x468    |
| LOC_ALERT_CLASS_SHADOWED_3 | 0x46c    |
| LOC_ALERT_CLASS_SHADOWED_4 | 0x470    |
| LOC_ALERT_CLASS_SHADOWED_5 | 0x474    |
| LOC_ALERT_CLASS_SHADOWED_6 | 0x478    |


### Fields

```wavejson
{"reg": [{"name": "CLASS_LA", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name                                            |
|:------:|:------:|:-------:|:------------------------------------------------|
|  31:2  |        |         | Reserved                                        |
|  1:0   |   rw   |   0x0   | [CLASS_LA](#loc_alert_class_shadowed--class_la) |

### LOC_ALERT_CLASS_SHADOWED . CLASS_LA
Classification

| Value   | Name   | Description   |
|:--------|:-------|:--------------|
| 0x0     | ClassA |               |
| 0x1     | ClassB |               |
| 0x2     | ClassC |               |
| 0x3     | ClassD |               |


## LOC_ALERT_CAUSE
Alert Cause Register for the local alerts
"alert pingfail" (0), "escalation pingfail" (1),
"alert integfail" (2), "escalation integfail" (3),
"bus integrity failure" (4), "shadow reg update error" (5)
and "shadow reg storage error" (6).
- Reset default: `0x0`
- Reset mask: `0x1`

### Instances

| Name              | Offset   |
|:------------------|:---------|
| LOC_ALERT_CAUSE_0 | 0x47c    |
| LOC_ALERT_CAUSE_1 | 0x480    |
| LOC_ALERT_CAUSE_2 | 0x484    |
| LOC_ALERT_CAUSE_3 | 0x488    |
| LOC_ALERT_CAUSE_4 | 0x48c    |
| LOC_ALERT_CAUSE_5 | 0x490    |
| LOC_ALERT_CAUSE_6 | 0x494    |


### Fields

```wavejson
{"reg": [{"name": "LA", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:1  |        |         |        | Reserved      |
|   0    |  rw1c  |   0x0   | LA     | Cause bit     |

## CLASSA_REGWEN
Lock bit for Class A configuration.
- Offset: `0x498`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "CLASSA_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                                                                                         |
|:------:|:------:|:-------:|:--------------|:------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |               | Reserved                                                                                                                            |
|   0    |  rw0c  |   0x1   | CLASSA_REGWEN | Class configuration enable bit. If this is cleared to 0, the corresponding class configuration registers cannot be written anymore. |

## CLASSA_CTRL_SHADOWED
Escalation control register for alert Class A. Can not be modified if [`CLASSA_REGWEN`](#classa_regwen) is false.
- Offset: `0x49c`
- Reset default: `0x393c`
- Reset mask: `0x3fff`
- Register enable: [`CLASSA_REGWEN`](#classa_regwen)

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "LOCK", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_E0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_E1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_E2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_E3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "MAP_E0", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "MAP_E1", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "MAP_E2", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "MAP_E3", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 18}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                     |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:14  |        |         |        | Reserved                                                                                                                                                                                        |
| 13:12  |   rw   |   0x3   | MAP_E3 | Determines in which escalation phase escalation signal 3 shall be asserted.                                                                                                                     |
| 11:10  |   rw   |   0x2   | MAP_E2 | Determines in which escalation phase escalation signal 2 shall be asserted.                                                                                                                     |
|  9:8   |   rw   |   0x1   | MAP_E1 | Determines in which escalation phase escalation signal 1 shall be asserted.                                                                                                                     |
|  7:6   |   rw   |   0x0   | MAP_E0 | Determines in which escalation phase escalation signal 0 shall be asserted.                                                                                                                     |
|   5    |   rw   |   0x1   | EN_E3  | Enable escalation signal 3 for Class A                                                                                                                                                          |
|   4    |   rw   |   0x1   | EN_E2  | Enable escalation signal 2 for Class A                                                                                                                                                          |
|   3    |   rw   |   0x1   | EN_E1  | Enable escalation signal 1 for Class A                                                                                                                                                          |
|   2    |   rw   |   0x1   | EN_E0  | Enable escalation signal 0 for Class A                                                                                                                                                          |
|   1    |   rw   |   0x0   | LOCK   | Enable automatic locking of escalation counter for class A. If true, there is no way to stop the escalation protocol for class A once it has been triggered.                                    |
|   0    |   rw   |   0x0   | EN     | Enable escalation mechanisms (accumulation and interrupt timeout) for Class A. Note that interrupts can fire regardless of whether the escalation mechanisms are enabled for this class or not. |

## CLASSA_CLR_REGWEN
Clear enable for escalation protocol of Class A alerts.
- Offset: `0x4a0`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "CLASSA_CLR_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                                                                                                                                                                                                           |
|:------:|:------:|:-------:|:------------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                   | Reserved                                                                                                                                                                                                              |
|   0    |  rw0c  |   0x1   | CLASSA_CLR_REGWEN | Register defaults to true, can only be cleared. This register is set to false by the hardware if the escalation protocol has been triggered and the bit [`CLASSA_CTRL_SHADOWED.LOCK`](#classa_ctrl_shadowed) is true. |

## CLASSA_CLR_SHADOWED
Clear for escalation protocol of Class A.
- Offset: `0x4a4`
- Reset default: `0x0`
- Reset mask: `0x1`
- Register enable: [`CLASSA_CLR_REGWEN`](#classa_clr_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSA_CLR_SHADOWED", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 210}}
```

|  Bits  |  Type  |  Reset  | Name                | Description                                                                                                                                                                       |
|:------:|:------:|:-------:|:--------------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                     | Reserved                                                                                                                                                                          |
|   0    |   rw   |   0x0   | CLASSA_CLR_SHADOWED | Writing 1 to this register clears the accumulator and aborts escalation (if it has been triggered). This clear is disabled if [`CLASSA_CLR_REGWEN`](#classa_clr_regwen) is false. |

## CLASSA_ACCUM_CNT
Current accumulation value for alert Class A. Software can clear this register
with a write to [`CLASSA_CLR_SHADOWED`](#classa_clr_shadowed) register unless [`CLASSA_CLR_REGWEN`](#classa_clr_regwen) is false.
- Offset: `0x4a8`
- Reset default: `0x0`
- Reset mask: `0xffff`

### Fields

```wavejson
{"reg": [{"name": "CLASSA_ACCUM_CNT", "bits": 16, "attr": ["ro"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name             | Description   |
|:------:|:------:|:-------:|:-----------------|:--------------|
| 31:16  |        |         |                  | Reserved      |
|  15:0  |   ro   |    x    | CLASSA_ACCUM_CNT |               |

## CLASSA_ACCUM_THRESH_SHADOWED
Accumulation threshold value for alert Class A.
- Offset: `0x4ac`
- Reset default: `0x0`
- Reset mask: `0xffff`
- Register enable: [`CLASSA_REGWEN`](#classa_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSA_ACCUM_THRESH_SHADOWED", "bits": 16, "attr": ["rw"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                         | Description                                                                                                                                                                                                                                     |
|:------:|:------:|:-------:|:-----------------------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:16  |        |         |                              | Reserved                                                                                                                                                                                                                                        |
|  15:0  |   rw   |   0x0   | CLASSA_ACCUM_THRESH_SHADOWED | Once the accumulation value register is equal to the threshold escalation will be triggered on the next alert occurrence within this class A begins. Note that this register can not be modified if [`CLASSA_REGWEN`](#classa_regwen) is false. |

## CLASSA_TIMEOUT_CYC_SHADOWED
Interrupt timeout in cycles.
- Offset: `0x4b0`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CLASSA_REGWEN`](#classa_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSA_TIMEOUT_CYC_SHADOWED", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                                                     |
|:------:|:------:|:-------:|:-----------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | [CLASSA_TIMEOUT_CYC_SHADOWED](#classa_timeout_cyc_shadowed--classa_timeout_cyc_shadowed) |

### CLASSA_TIMEOUT_CYC_SHADOWED . CLASSA_TIMEOUT_CYC_SHADOWED
If the interrupt corresponding to this class is not
handled within the specified amount of cycles, escalation will be triggered.
Set to a positive value to enable the interrupt timeout for Class A. The timeout is set to zero
by default, which disables this feature. Note that this register can not be modified if
[`CLASSA_REGWEN`](#classa_regwen) is false.

## CLASSA_CRASHDUMP_TRIGGER_SHADOWED
Crashdump trigger configuration for Class A.
- Offset: `0x4b4`
- Reset default: `0x0`
- Reset mask: `0x3`
- Register enable: [`CLASSA_REGWEN`](#classa_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSA_CRASHDUMP_TRIGGER_SHADOWED", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 350}}
```

|  Bits  |  Type  |  Reset  | Name                                                                                                       |
|:------:|:------:|:-------:|:-----------------------------------------------------------------------------------------------------------|
|  31:2  |        |         | Reserved                                                                                                   |
|  1:0   |   rw   |   0x0   | [CLASSA_CRASHDUMP_TRIGGER_SHADOWED](#classa_crashdump_trigger_shadowed--classa_crashdump_trigger_shadowed) |

### CLASSA_CRASHDUMP_TRIGGER_SHADOWED . CLASSA_CRASHDUMP_TRIGGER_SHADOWED
Determine in which escalation phase to capture the crashdump containing all alert cause CSRs and escalation
timer states. It is recommended to capture the crashdump upon entering the first escalation phase
that activates a countermeasure with many side-effects (e.g. life cycle state scrapping) in order
to prevent spurious alert events from masking the original alert causes.
Note that this register can not be modified if [`CLASSA_REGWEN`](#classa_regwen) is false.

## CLASSA_PHASE0_CYC_SHADOWED
Duration of escalation phase 0 for Class A.
- Offset: `0x4b8`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CLASSA_REGWEN`](#classa_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSA_PHASE0_CYC_SHADOWED", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                                                                                     |
|:------:|:------:|:-------:|:---------------------------|:--------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | CLASSA_PHASE0_CYC_SHADOWED | Escalation phase duration in cycles. Note that this register can not be modified if [`CLASSA_REGWEN`](#classa_regwen) is false. |

## CLASSA_PHASE1_CYC_SHADOWED
Duration of escalation phase 1 for Class A.
- Offset: `0x4bc`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CLASSA_REGWEN`](#classa_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSA_PHASE1_CYC_SHADOWED", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                                                                                     |
|:------:|:------:|:-------:|:---------------------------|:--------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | CLASSA_PHASE1_CYC_SHADOWED | Escalation phase duration in cycles. Note that this register can not be modified if [`CLASSA_REGWEN`](#classa_regwen) is false. |

## CLASSA_PHASE2_CYC_SHADOWED
Duration of escalation phase 2 for Class A.
- Offset: `0x4c0`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CLASSA_REGWEN`](#classa_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSA_PHASE2_CYC_SHADOWED", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                                                                                     |
|:------:|:------:|:-------:|:---------------------------|:--------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | CLASSA_PHASE2_CYC_SHADOWED | Escalation phase duration in cycles. Note that this register can not be modified if [`CLASSA_REGWEN`](#classa_regwen) is false. |

## CLASSA_PHASE3_CYC_SHADOWED
Duration of escalation phase 3 for Class A.
- Offset: `0x4c4`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CLASSA_REGWEN`](#classa_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSA_PHASE3_CYC_SHADOWED", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                                                                                     |
|:------:|:------:|:-------:|:---------------------------|:--------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | CLASSA_PHASE3_CYC_SHADOWED | Escalation phase duration in cycles. Note that this register can not be modified if [`CLASSA_REGWEN`](#classa_regwen) is false. |

## CLASSA_ESC_CNT
Escalation counter in cycles for Class A.
- Offset: `0x4c8`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "CLASSA_ESC_CNT", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                              |
|:------:|:------:|:-------:|:--------------------------------------------------|
|  31:0  |   ro   |    x    | [CLASSA_ESC_CNT](#classa_esc_cnt--classa_esc_cnt) |

### CLASSA_ESC_CNT . CLASSA_ESC_CNT
Returns the current timeout or escalation count (depending on [`CLASSA_STATE`](#classa_state)).
This register can not be directly cleared. However, SW can indirectly clear as follows.

If the class is in the Timeout state, the timeout can be aborted by clearing the
corresponding interrupt bit.

If this class is in any of the escalation phases (e.g. Phase0), escalation protocol can be
aborted by writing to [`CLASSA_CLR_SHADOWED.`](#classa_clr_shadowed) Note however that has no effect if [`CLASSA_REGWEN`](#classa_regwen)
is set to false (either by SW or by HW via the [`CLASSA_CTRL_SHADOWED.LOCK`](#classa_ctrl_shadowed) feature).

## CLASSA_STATE
Current escalation state of Class A. See also [`CLASSA_ESC_CNT.`](#classa_esc_cnt)
- Offset: `0x4cc`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "CLASSA_STATE", "bits": 3, "attr": ["ro"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name                                        |
|:------:|:------:|:-------:|:--------------------------------------------|
|  31:3  |        |         | Reserved                                    |
|  2:0   |   ro   |    x    | [CLASSA_STATE](#classa_state--classa_state) |

### CLASSA_STATE . CLASSA_STATE

| Value   | Name     | Description                                    |
|:--------|:---------|:-----------------------------------------------|
| 0x0     | Idle     | No timeout or escalation triggered.            |
| 0x1     | Timeout  | IRQ timeout counter is active.                 |
| 0x2     | FsmError | Terminal error state if FSM has been glitched. |
| 0x3     | Terminal | Terminal state after escalation protocol.      |
| 0x4     | Phase0   | Escalation Phase0 is active.                   |
| 0x5     | Phase1   | Escalation Phase1 is active.                   |
| 0x6     | Phase2   | Escalation Phase2 is active.                   |
| 0x7     | Phase3   | Escalation Phase3 is active.                   |


## CLASSB_REGWEN
Lock bit for Class B configuration.
- Offset: `0x4d0`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "CLASSB_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                                                                                         |
|:------:|:------:|:-------:|:--------------|:------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |               | Reserved                                                                                                                            |
|   0    |  rw0c  |   0x1   | CLASSB_REGWEN | Class configuration enable bit. If this is cleared to 0, the corresponding class configuration registers cannot be written anymore. |

## CLASSB_CTRL_SHADOWED
Escalation control register for alert Class B. Can not be modified if [`CLASSB_REGWEN`](#classb_regwen) is false.
- Offset: `0x4d4`
- Reset default: `0x393c`
- Reset mask: `0x3fff`
- Register enable: [`CLASSB_REGWEN`](#classb_regwen)

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "LOCK", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_E0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_E1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_E2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_E3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "MAP_E0", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "MAP_E1", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "MAP_E2", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "MAP_E3", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 18}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                     |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:14  |        |         |        | Reserved                                                                                                                                                                                        |
| 13:12  |   rw   |   0x3   | MAP_E3 | Determines in which escalation phase escalation signal 3 shall be asserted.                                                                                                                     |
| 11:10  |   rw   |   0x2   | MAP_E2 | Determines in which escalation phase escalation signal 2 shall be asserted.                                                                                                                     |
|  9:8   |   rw   |   0x1   | MAP_E1 | Determines in which escalation phase escalation signal 1 shall be asserted.                                                                                                                     |
|  7:6   |   rw   |   0x0   | MAP_E0 | Determines in which escalation phase escalation signal 0 shall be asserted.                                                                                                                     |
|   5    |   rw   |   0x1   | EN_E3  | Enable escalation signal 3 for Class B                                                                                                                                                          |
|   4    |   rw   |   0x1   | EN_E2  | Enable escalation signal 2 for Class B                                                                                                                                                          |
|   3    |   rw   |   0x1   | EN_E1  | Enable escalation signal 1 for Class B                                                                                                                                                          |
|   2    |   rw   |   0x1   | EN_E0  | Enable escalation signal 0 for Class B                                                                                                                                                          |
|   1    |   rw   |   0x0   | LOCK   | Enable automatic locking of escalation counter for class B. If true, there is no way to stop the escalation protocol for class B once it has been triggered.                                    |
|   0    |   rw   |   0x0   | EN     | Enable escalation mechanisms (accumulation and interrupt timeout) for Class B. Note that interrupts can fire regardless of whether the escalation mechanisms are enabled for this class or not. |

## CLASSB_CLR_REGWEN
Clear enable for escalation protocol of Class B alerts.
- Offset: `0x4d8`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "CLASSB_CLR_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                                                                                                                                                                                                           |
|:------:|:------:|:-------:|:------------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                   | Reserved                                                                                                                                                                                                              |
|   0    |  rw0c  |   0x1   | CLASSB_CLR_REGWEN | Register defaults to true, can only be cleared. This register is set to false by the hardware if the escalation protocol has been triggered and the bit [`CLASSB_CTRL_SHADOWED.LOCK`](#classb_ctrl_shadowed) is true. |

## CLASSB_CLR_SHADOWED
Clear for escalation protocol of Class B.
- Offset: `0x4dc`
- Reset default: `0x0`
- Reset mask: `0x1`
- Register enable: [`CLASSB_CLR_REGWEN`](#classb_clr_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSB_CLR_SHADOWED", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 210}}
```

|  Bits  |  Type  |  Reset  | Name                | Description                                                                                                                                                                       |
|:------:|:------:|:-------:|:--------------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                     | Reserved                                                                                                                                                                          |
|   0    |   rw   |   0x0   | CLASSB_CLR_SHADOWED | Writing 1 to this register clears the accumulator and aborts escalation (if it has been triggered). This clear is disabled if [`CLASSB_CLR_REGWEN`](#classb_clr_regwen) is false. |

## CLASSB_ACCUM_CNT
Current accumulation value for alert Class B. Software can clear this register
with a write to [`CLASSB_CLR_SHADOWED`](#classb_clr_shadowed) register unless [`CLASSB_CLR_REGWEN`](#classb_clr_regwen) is false.
- Offset: `0x4e0`
- Reset default: `0x0`
- Reset mask: `0xffff`

### Fields

```wavejson
{"reg": [{"name": "CLASSB_ACCUM_CNT", "bits": 16, "attr": ["ro"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name             | Description   |
|:------:|:------:|:-------:|:-----------------|:--------------|
| 31:16  |        |         |                  | Reserved      |
|  15:0  |   ro   |    x    | CLASSB_ACCUM_CNT |               |

## CLASSB_ACCUM_THRESH_SHADOWED
Accumulation threshold value for alert Class B.
- Offset: `0x4e4`
- Reset default: `0x0`
- Reset mask: `0xffff`
- Register enable: [`CLASSB_REGWEN`](#classb_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSB_ACCUM_THRESH_SHADOWED", "bits": 16, "attr": ["rw"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                         | Description                                                                                                                                                                                                                                     |
|:------:|:------:|:-------:|:-----------------------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:16  |        |         |                              | Reserved                                                                                                                                                                                                                                        |
|  15:0  |   rw   |   0x0   | CLASSB_ACCUM_THRESH_SHADOWED | Once the accumulation value register is equal to the threshold escalation will be triggered on the next alert occurrence within this class B begins. Note that this register can not be modified if [`CLASSB_REGWEN`](#classb_regwen) is false. |

## CLASSB_TIMEOUT_CYC_SHADOWED
Interrupt timeout in cycles.
- Offset: `0x4e8`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CLASSB_REGWEN`](#classb_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSB_TIMEOUT_CYC_SHADOWED", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                                                     |
|:------:|:------:|:-------:|:-----------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | [CLASSB_TIMEOUT_CYC_SHADOWED](#classb_timeout_cyc_shadowed--classb_timeout_cyc_shadowed) |

### CLASSB_TIMEOUT_CYC_SHADOWED . CLASSB_TIMEOUT_CYC_SHADOWED
If the interrupt corresponding to this class is not
handled within the specified amount of cycles, escalation will be triggered.
Set to a positive value to enable the interrupt timeout for Class B. The timeout is set to zero
by default, which disables this feature. Note that this register can not be modified if
[`CLASSB_REGWEN`](#classb_regwen) is false.

## CLASSB_CRASHDUMP_TRIGGER_SHADOWED
Crashdump trigger configuration for Class B.
- Offset: `0x4ec`
- Reset default: `0x0`
- Reset mask: `0x3`
- Register enable: [`CLASSB_REGWEN`](#classb_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSB_CRASHDUMP_TRIGGER_SHADOWED", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 350}}
```

|  Bits  |  Type  |  Reset  | Name                                                                                                       |
|:------:|:------:|:-------:|:-----------------------------------------------------------------------------------------------------------|
|  31:2  |        |         | Reserved                                                                                                   |
|  1:0   |   rw   |   0x0   | [CLASSB_CRASHDUMP_TRIGGER_SHADOWED](#classb_crashdump_trigger_shadowed--classb_crashdump_trigger_shadowed) |

### CLASSB_CRASHDUMP_TRIGGER_SHADOWED . CLASSB_CRASHDUMP_TRIGGER_SHADOWED
Determine in which escalation phase to capture the crashdump containing all alert cause CSRs and escalation
timer states. It is recommended to capture the crashdump upon entering the first escalation phase
that activates a countermeasure with many side-effects (e.g. life cycle state scrapping) in order
to prevent spurious alert events from masking the original alert causes.
Note that this register can not be modified if [`CLASSB_REGWEN`](#classb_regwen) is false.

## CLASSB_PHASE0_CYC_SHADOWED
Duration of escalation phase 0 for Class B.
- Offset: `0x4f0`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CLASSB_REGWEN`](#classb_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSB_PHASE0_CYC_SHADOWED", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                                                                                     |
|:------:|:------:|:-------:|:---------------------------|:--------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | CLASSB_PHASE0_CYC_SHADOWED | Escalation phase duration in cycles. Note that this register can not be modified if [`CLASSB_REGWEN`](#classb_regwen) is false. |

## CLASSB_PHASE1_CYC_SHADOWED
Duration of escalation phase 1 for Class B.
- Offset: `0x4f4`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CLASSB_REGWEN`](#classb_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSB_PHASE1_CYC_SHADOWED", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                                                                                     |
|:------:|:------:|:-------:|:---------------------------|:--------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | CLASSB_PHASE1_CYC_SHADOWED | Escalation phase duration in cycles. Note that this register can not be modified if [`CLASSB_REGWEN`](#classb_regwen) is false. |

## CLASSB_PHASE2_CYC_SHADOWED
Duration of escalation phase 2 for Class B.
- Offset: `0x4f8`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CLASSB_REGWEN`](#classb_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSB_PHASE2_CYC_SHADOWED", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                                                                                     |
|:------:|:------:|:-------:|:---------------------------|:--------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | CLASSB_PHASE2_CYC_SHADOWED | Escalation phase duration in cycles. Note that this register can not be modified if [`CLASSB_REGWEN`](#classb_regwen) is false. |

## CLASSB_PHASE3_CYC_SHADOWED
Duration of escalation phase 3 for Class B.
- Offset: `0x4fc`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CLASSB_REGWEN`](#classb_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSB_PHASE3_CYC_SHADOWED", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                                                                                     |
|:------:|:------:|:-------:|:---------------------------|:--------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | CLASSB_PHASE3_CYC_SHADOWED | Escalation phase duration in cycles. Note that this register can not be modified if [`CLASSB_REGWEN`](#classb_regwen) is false. |

## CLASSB_ESC_CNT
Escalation counter in cycles for Class B.
- Offset: `0x500`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "CLASSB_ESC_CNT", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                              |
|:------:|:------:|:-------:|:--------------------------------------------------|
|  31:0  |   ro   |    x    | [CLASSB_ESC_CNT](#classb_esc_cnt--classb_esc_cnt) |

### CLASSB_ESC_CNT . CLASSB_ESC_CNT
Returns the current timeout or escalation count (depending on [`CLASSB_STATE`](#classb_state)).
This register can not be directly cleared. However, SW can indirectly clear as follows.

If the class is in the Timeout state, the timeout can be aborted by clearing the
corresponding interrupt bit.

If this class is in any of the escalation phases (e.g. Phase0), escalation protocol can be
aborted by writing to [`CLASSB_CLR_SHADOWED.`](#classb_clr_shadowed) Note however that has no effect if [`CLASSB_REGWEN`](#classb_regwen)
is set to false (either by SW or by HW via the [`CLASSB_CTRL_SHADOWED.LOCK`](#classb_ctrl_shadowed) feature).

## CLASSB_STATE
Current escalation state of Class B. See also [`CLASSB_ESC_CNT.`](#classb_esc_cnt)
- Offset: `0x504`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "CLASSB_STATE", "bits": 3, "attr": ["ro"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name                                        |
|:------:|:------:|:-------:|:--------------------------------------------|
|  31:3  |        |         | Reserved                                    |
|  2:0   |   ro   |    x    | [CLASSB_STATE](#classb_state--classb_state) |

### CLASSB_STATE . CLASSB_STATE

| Value   | Name     | Description                                    |
|:--------|:---------|:-----------------------------------------------|
| 0x0     | Idle     | No timeout or escalation triggered.            |
| 0x1     | Timeout  | IRQ timeout counter is active.                 |
| 0x2     | FsmError | Terminal error state if FSM has been glitched. |
| 0x3     | Terminal | Terminal state after escalation protocol.      |
| 0x4     | Phase0   | Escalation Phase0 is active.                   |
| 0x5     | Phase1   | Escalation Phase1 is active.                   |
| 0x6     | Phase2   | Escalation Phase2 is active.                   |
| 0x7     | Phase3   | Escalation Phase3 is active.                   |


## CLASSC_REGWEN
Lock bit for Class C configuration.
- Offset: `0x508`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "CLASSC_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                                                                                         |
|:------:|:------:|:-------:|:--------------|:------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |               | Reserved                                                                                                                            |
|   0    |  rw0c  |   0x1   | CLASSC_REGWEN | Class configuration enable bit. If this is cleared to 0, the corresponding class configuration registers cannot be written anymore. |

## CLASSC_CTRL_SHADOWED
Escalation control register for alert Class C. Can not be modified if [`CLASSC_REGWEN`](#classc_regwen) is false.
- Offset: `0x50c`
- Reset default: `0x393c`
- Reset mask: `0x3fff`
- Register enable: [`CLASSC_REGWEN`](#classc_regwen)

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "LOCK", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_E0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_E1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_E2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_E3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "MAP_E0", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "MAP_E1", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "MAP_E2", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "MAP_E3", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 18}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                     |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:14  |        |         |        | Reserved                                                                                                                                                                                        |
| 13:12  |   rw   |   0x3   | MAP_E3 | Determines in which escalation phase escalation signal 3 shall be asserted.                                                                                                                     |
| 11:10  |   rw   |   0x2   | MAP_E2 | Determines in which escalation phase escalation signal 2 shall be asserted.                                                                                                                     |
|  9:8   |   rw   |   0x1   | MAP_E1 | Determines in which escalation phase escalation signal 1 shall be asserted.                                                                                                                     |
|  7:6   |   rw   |   0x0   | MAP_E0 | Determines in which escalation phase escalation signal 0 shall be asserted.                                                                                                                     |
|   5    |   rw   |   0x1   | EN_E3  | Enable escalation signal 3 for Class C                                                                                                                                                          |
|   4    |   rw   |   0x1   | EN_E2  | Enable escalation signal 2 for Class C                                                                                                                                                          |
|   3    |   rw   |   0x1   | EN_E1  | Enable escalation signal 1 for Class C                                                                                                                                                          |
|   2    |   rw   |   0x1   | EN_E0  | Enable escalation signal 0 for Class C                                                                                                                                                          |
|   1    |   rw   |   0x0   | LOCK   | Enable automatic locking of escalation counter for class C. If true, there is no way to stop the escalation protocol for class C once it has been triggered.                                    |
|   0    |   rw   |   0x0   | EN     | Enable escalation mechanisms (accumulation and interrupt timeout) for Class C. Note that interrupts can fire regardless of whether the escalation mechanisms are enabled for this class or not. |

## CLASSC_CLR_REGWEN
Clear enable for escalation protocol of Class C alerts.
- Offset: `0x510`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "CLASSC_CLR_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                                                                                                                                                                                                           |
|:------:|:------:|:-------:|:------------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                   | Reserved                                                                                                                                                                                                              |
|   0    |  rw0c  |   0x1   | CLASSC_CLR_REGWEN | Register defaults to true, can only be cleared. This register is set to false by the hardware if the escalation protocol has been triggered and the bit [`CLASSC_CTRL_SHADOWED.LOCK`](#classc_ctrl_shadowed) is true. |

## CLASSC_CLR_SHADOWED
Clear for escalation protocol of Class C.
- Offset: `0x514`
- Reset default: `0x0`
- Reset mask: `0x1`
- Register enable: [`CLASSC_CLR_REGWEN`](#classc_clr_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSC_CLR_SHADOWED", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 210}}
```

|  Bits  |  Type  |  Reset  | Name                | Description                                                                                                                                                                       |
|:------:|:------:|:-------:|:--------------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                     | Reserved                                                                                                                                                                          |
|   0    |   rw   |   0x0   | CLASSC_CLR_SHADOWED | Writing 1 to this register clears the accumulator and aborts escalation (if it has been triggered). This clear is disabled if [`CLASSC_CLR_REGWEN`](#classc_clr_regwen) is false. |

## CLASSC_ACCUM_CNT
Current accumulation value for alert Class C. Software can clear this register
with a write to [`CLASSC_CLR_SHADOWED`](#classc_clr_shadowed) register unless [`CLASSC_CLR_REGWEN`](#classc_clr_regwen) is false.
- Offset: `0x518`
- Reset default: `0x0`
- Reset mask: `0xffff`

### Fields

```wavejson
{"reg": [{"name": "CLASSC_ACCUM_CNT", "bits": 16, "attr": ["ro"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name             | Description   |
|:------:|:------:|:-------:|:-----------------|:--------------|
| 31:16  |        |         |                  | Reserved      |
|  15:0  |   ro   |    x    | CLASSC_ACCUM_CNT |               |

## CLASSC_ACCUM_THRESH_SHADOWED
Accumulation threshold value for alert Class C.
- Offset: `0x51c`
- Reset default: `0x0`
- Reset mask: `0xffff`
- Register enable: [`CLASSC_REGWEN`](#classc_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSC_ACCUM_THRESH_SHADOWED", "bits": 16, "attr": ["rw"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                         | Description                                                                                                                                                                                                                                     |
|:------:|:------:|:-------:|:-----------------------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:16  |        |         |                              | Reserved                                                                                                                                                                                                                                        |
|  15:0  |   rw   |   0x0   | CLASSC_ACCUM_THRESH_SHADOWED | Once the accumulation value register is equal to the threshold escalation will be triggered on the next alert occurrence within this class C begins. Note that this register can not be modified if [`CLASSC_REGWEN`](#classc_regwen) is false. |

## CLASSC_TIMEOUT_CYC_SHADOWED
Interrupt timeout in cycles.
- Offset: `0x520`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CLASSC_REGWEN`](#classc_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSC_TIMEOUT_CYC_SHADOWED", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                                                     |
|:------:|:------:|:-------:|:-----------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | [CLASSC_TIMEOUT_CYC_SHADOWED](#classc_timeout_cyc_shadowed--classc_timeout_cyc_shadowed) |

### CLASSC_TIMEOUT_CYC_SHADOWED . CLASSC_TIMEOUT_CYC_SHADOWED
If the interrupt corresponding to this class is not
handled within the specified amount of cycles, escalation will be triggered.
Set to a positive value to enable the interrupt timeout for Class C. The timeout is set to zero
by default, which disables this feature. Note that this register can not be modified if
[`CLASSC_REGWEN`](#classc_regwen) is false.

## CLASSC_CRASHDUMP_TRIGGER_SHADOWED
Crashdump trigger configuration for Class C.
- Offset: `0x524`
- Reset default: `0x0`
- Reset mask: `0x3`
- Register enable: [`CLASSC_REGWEN`](#classc_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSC_CRASHDUMP_TRIGGER_SHADOWED", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 350}}
```

|  Bits  |  Type  |  Reset  | Name                                                                                                       |
|:------:|:------:|:-------:|:-----------------------------------------------------------------------------------------------------------|
|  31:2  |        |         | Reserved                                                                                                   |
|  1:0   |   rw   |   0x0   | [CLASSC_CRASHDUMP_TRIGGER_SHADOWED](#classc_crashdump_trigger_shadowed--classc_crashdump_trigger_shadowed) |

### CLASSC_CRASHDUMP_TRIGGER_SHADOWED . CLASSC_CRASHDUMP_TRIGGER_SHADOWED
Determine in which escalation phase to capture the crashdump containing all alert cause CSRs and escalation
timer states. It is recommended to capture the crashdump upon entering the first escalation phase
that activates a countermeasure with many side-effects (e.g. life cycle state scrapping) in order
to prevent spurious alert events from masking the original alert causes.
Note that this register can not be modified if [`CLASSC_REGWEN`](#classc_regwen) is false.

## CLASSC_PHASE0_CYC_SHADOWED
Duration of escalation phase 0 for Class C.
- Offset: `0x528`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CLASSC_REGWEN`](#classc_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSC_PHASE0_CYC_SHADOWED", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                                                                                     |
|:------:|:------:|:-------:|:---------------------------|:--------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | CLASSC_PHASE0_CYC_SHADOWED | Escalation phase duration in cycles. Note that this register can not be modified if [`CLASSC_REGWEN`](#classc_regwen) is false. |

## CLASSC_PHASE1_CYC_SHADOWED
Duration of escalation phase 1 for Class C.
- Offset: `0x52c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CLASSC_REGWEN`](#classc_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSC_PHASE1_CYC_SHADOWED", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                                                                                     |
|:------:|:------:|:-------:|:---------------------------|:--------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | CLASSC_PHASE1_CYC_SHADOWED | Escalation phase duration in cycles. Note that this register can not be modified if [`CLASSC_REGWEN`](#classc_regwen) is false. |

## CLASSC_PHASE2_CYC_SHADOWED
Duration of escalation phase 2 for Class C.
- Offset: `0x530`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CLASSC_REGWEN`](#classc_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSC_PHASE2_CYC_SHADOWED", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                                                                                     |
|:------:|:------:|:-------:|:---------------------------|:--------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | CLASSC_PHASE2_CYC_SHADOWED | Escalation phase duration in cycles. Note that this register can not be modified if [`CLASSC_REGWEN`](#classc_regwen) is false. |

## CLASSC_PHASE3_CYC_SHADOWED
Duration of escalation phase 3 for Class C.
- Offset: `0x534`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CLASSC_REGWEN`](#classc_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSC_PHASE3_CYC_SHADOWED", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                                                                                     |
|:------:|:------:|:-------:|:---------------------------|:--------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | CLASSC_PHASE3_CYC_SHADOWED | Escalation phase duration in cycles. Note that this register can not be modified if [`CLASSC_REGWEN`](#classc_regwen) is false. |

## CLASSC_ESC_CNT
Escalation counter in cycles for Class C.
- Offset: `0x538`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "CLASSC_ESC_CNT", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                              |
|:------:|:------:|:-------:|:--------------------------------------------------|
|  31:0  |   ro   |    x    | [CLASSC_ESC_CNT](#classc_esc_cnt--classc_esc_cnt) |

### CLASSC_ESC_CNT . CLASSC_ESC_CNT
Returns the current timeout or escalation count (depending on [`CLASSC_STATE`](#classc_state)).
This register can not be directly cleared. However, SW can indirectly clear as follows.

If the class is in the Timeout state, the timeout can be aborted by clearing the
corresponding interrupt bit.

If this class is in any of the escalation phases (e.g. Phase0), escalation protocol can be
aborted by writing to [`CLASSC_CLR_SHADOWED.`](#classc_clr_shadowed) Note however that has no effect if [`CLASSC_REGWEN`](#classc_regwen)
is set to false (either by SW or by HW via the [`CLASSC_CTRL_SHADOWED.LOCK`](#classc_ctrl_shadowed) feature).

## CLASSC_STATE
Current escalation state of Class C. See also [`CLASSC_ESC_CNT.`](#classc_esc_cnt)
- Offset: `0x53c`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "CLASSC_STATE", "bits": 3, "attr": ["ro"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name                                        |
|:------:|:------:|:-------:|:--------------------------------------------|
|  31:3  |        |         | Reserved                                    |
|  2:0   |   ro   |    x    | [CLASSC_STATE](#classc_state--classc_state) |

### CLASSC_STATE . CLASSC_STATE

| Value   | Name     | Description                                    |
|:--------|:---------|:-----------------------------------------------|
| 0x0     | Idle     | No timeout or escalation triggered.            |
| 0x1     | Timeout  | IRQ timeout counter is active.                 |
| 0x2     | FsmError | Terminal error state if FSM has been glitched. |
| 0x3     | Terminal | Terminal state after escalation protocol.      |
| 0x4     | Phase0   | Escalation Phase0 is active.                   |
| 0x5     | Phase1   | Escalation Phase1 is active.                   |
| 0x6     | Phase2   | Escalation Phase2 is active.                   |
| 0x7     | Phase3   | Escalation Phase3 is active.                   |


## CLASSD_REGWEN
Lock bit for Class D configuration.
- Offset: `0x540`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "CLASSD_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                                                                                         |
|:------:|:------:|:-------:|:--------------|:------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |               | Reserved                                                                                                                            |
|   0    |  rw0c  |   0x1   | CLASSD_REGWEN | Class configuration enable bit. If this is cleared to 0, the corresponding class configuration registers cannot be written anymore. |

## CLASSD_CTRL_SHADOWED
Escalation control register for alert Class D. Can not be modified if [`CLASSD_REGWEN`](#classd_regwen) is false.
- Offset: `0x544`
- Reset default: `0x393c`
- Reset mask: `0x3fff`
- Register enable: [`CLASSD_REGWEN`](#classd_regwen)

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "LOCK", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_E0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_E1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_E2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_E3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "MAP_E0", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "MAP_E1", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "MAP_E2", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "MAP_E3", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 18}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                     |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:14  |        |         |        | Reserved                                                                                                                                                                                        |
| 13:12  |   rw   |   0x3   | MAP_E3 | Determines in which escalation phase escalation signal 3 shall be asserted.                                                                                                                     |
| 11:10  |   rw   |   0x2   | MAP_E2 | Determines in which escalation phase escalation signal 2 shall be asserted.                                                                                                                     |
|  9:8   |   rw   |   0x1   | MAP_E1 | Determines in which escalation phase escalation signal 1 shall be asserted.                                                                                                                     |
|  7:6   |   rw   |   0x0   | MAP_E0 | Determines in which escalation phase escalation signal 0 shall be asserted.                                                                                                                     |
|   5    |   rw   |   0x1   | EN_E3  | Enable escalation signal 3 for Class D                                                                                                                                                          |
|   4    |   rw   |   0x1   | EN_E2  | Enable escalation signal 2 for Class D                                                                                                                                                          |
|   3    |   rw   |   0x1   | EN_E1  | Enable escalation signal 1 for Class D                                                                                                                                                          |
|   2    |   rw   |   0x1   | EN_E0  | Enable escalation signal 0 for Class D                                                                                                                                                          |
|   1    |   rw   |   0x0   | LOCK   | Enable automatic locking of escalation counter for class D. If true, there is no way to stop the escalation protocol for class D once it has been triggered.                                    |
|   0    |   rw   |   0x0   | EN     | Enable escalation mechanisms (accumulation and interrupt timeout) for Class D. Note that interrupts can fire regardless of whether the escalation mechanisms are enabled for this class or not. |

## CLASSD_CLR_REGWEN
Clear enable for escalation protocol of Class D alerts.
- Offset: `0x548`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "CLASSD_CLR_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                                                                                                                                                                                                           |
|:------:|:------:|:-------:|:------------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                   | Reserved                                                                                                                                                                                                              |
|   0    |  rw0c  |   0x1   | CLASSD_CLR_REGWEN | Register defaults to true, can only be cleared. This register is set to false by the hardware if the escalation protocol has been triggered and the bit [`CLASSD_CTRL_SHADOWED.LOCK`](#classd_ctrl_shadowed) is true. |

## CLASSD_CLR_SHADOWED
Clear for escalation protocol of Class D.
- Offset: `0x54c`
- Reset default: `0x0`
- Reset mask: `0x1`
- Register enable: [`CLASSD_CLR_REGWEN`](#classd_clr_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSD_CLR_SHADOWED", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 210}}
```

|  Bits  |  Type  |  Reset  | Name                | Description                                                                                                                                                                       |
|:------:|:------:|:-------:|:--------------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                     | Reserved                                                                                                                                                                          |
|   0    |   rw   |   0x0   | CLASSD_CLR_SHADOWED | Writing 1 to this register clears the accumulator and aborts escalation (if it has been triggered). This clear is disabled if [`CLASSD_CLR_REGWEN`](#classd_clr_regwen) is false. |

## CLASSD_ACCUM_CNT
Current accumulation value for alert Class D. Software can clear this register
with a write to [`CLASSD_CLR_SHADOWED`](#classd_clr_shadowed) register unless [`CLASSD_CLR_REGWEN`](#classd_clr_regwen) is false.
- Offset: `0x550`
- Reset default: `0x0`
- Reset mask: `0xffff`

### Fields

```wavejson
{"reg": [{"name": "CLASSD_ACCUM_CNT", "bits": 16, "attr": ["ro"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name             | Description   |
|:------:|:------:|:-------:|:-----------------|:--------------|
| 31:16  |        |         |                  | Reserved      |
|  15:0  |   ro   |    x    | CLASSD_ACCUM_CNT |               |

## CLASSD_ACCUM_THRESH_SHADOWED
Accumulation threshold value for alert Class D.
- Offset: `0x554`
- Reset default: `0x0`
- Reset mask: `0xffff`
- Register enable: [`CLASSD_REGWEN`](#classd_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSD_ACCUM_THRESH_SHADOWED", "bits": 16, "attr": ["rw"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                         | Description                                                                                                                                                                                                                                     |
|:------:|:------:|:-------:|:-----------------------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:16  |        |         |                              | Reserved                                                                                                                                                                                                                                        |
|  15:0  |   rw   |   0x0   | CLASSD_ACCUM_THRESH_SHADOWED | Once the accumulation value register is equal to the threshold escalation will be triggered on the next alert occurrence within this class D begins. Note that this register can not be modified if [`CLASSD_REGWEN`](#classd_regwen) is false. |

## CLASSD_TIMEOUT_CYC_SHADOWED
Interrupt timeout in cycles.
- Offset: `0x558`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CLASSD_REGWEN`](#classd_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSD_TIMEOUT_CYC_SHADOWED", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                                                     |
|:------:|:------:|:-------:|:-----------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | [CLASSD_TIMEOUT_CYC_SHADOWED](#classd_timeout_cyc_shadowed--classd_timeout_cyc_shadowed) |

### CLASSD_TIMEOUT_CYC_SHADOWED . CLASSD_TIMEOUT_CYC_SHADOWED
If the interrupt corresponding to this class is not
handled within the specified amount of cycles, escalation will be triggered.
Set to a positive value to enable the interrupt timeout for Class D. The timeout is set to zero
by default, which disables this feature. Note that this register can not be modified if
[`CLASSD_REGWEN`](#classd_regwen) is false.

## CLASSD_CRASHDUMP_TRIGGER_SHADOWED
Crashdump trigger configuration for Class D.
- Offset: `0x55c`
- Reset default: `0x0`
- Reset mask: `0x3`
- Register enable: [`CLASSD_REGWEN`](#classd_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSD_CRASHDUMP_TRIGGER_SHADOWED", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 350}}
```

|  Bits  |  Type  |  Reset  | Name                                                                                                       |
|:------:|:------:|:-------:|:-----------------------------------------------------------------------------------------------------------|
|  31:2  |        |         | Reserved                                                                                                   |
|  1:0   |   rw   |   0x0   | [CLASSD_CRASHDUMP_TRIGGER_SHADOWED](#classd_crashdump_trigger_shadowed--classd_crashdump_trigger_shadowed) |

### CLASSD_CRASHDUMP_TRIGGER_SHADOWED . CLASSD_CRASHDUMP_TRIGGER_SHADOWED
Determine in which escalation phase to capture the crashdump containing all alert cause CSRs and escalation
timer states. It is recommended to capture the crashdump upon entering the first escalation phase
that activates a countermeasure with many side-effects (e.g. life cycle state scrapping) in order
to prevent spurious alert events from masking the original alert causes.
Note that this register can not be modified if [`CLASSD_REGWEN`](#classd_regwen) is false.

## CLASSD_PHASE0_CYC_SHADOWED
Duration of escalation phase 0 for Class D.
- Offset: `0x560`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CLASSD_REGWEN`](#classd_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSD_PHASE0_CYC_SHADOWED", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                                                                                     |
|:------:|:------:|:-------:|:---------------------------|:--------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | CLASSD_PHASE0_CYC_SHADOWED | Escalation phase duration in cycles. Note that this register can not be modified if [`CLASSD_REGWEN`](#classd_regwen) is false. |

## CLASSD_PHASE1_CYC_SHADOWED
Duration of escalation phase 1 for Class D.
- Offset: `0x564`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CLASSD_REGWEN`](#classd_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSD_PHASE1_CYC_SHADOWED", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                                                                                     |
|:------:|:------:|:-------:|:---------------------------|:--------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | CLASSD_PHASE1_CYC_SHADOWED | Escalation phase duration in cycles. Note that this register can not be modified if [`CLASSD_REGWEN`](#classd_regwen) is false. |

## CLASSD_PHASE2_CYC_SHADOWED
Duration of escalation phase 2 for Class D.
- Offset: `0x568`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CLASSD_REGWEN`](#classd_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSD_PHASE2_CYC_SHADOWED", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                                                                                     |
|:------:|:------:|:-------:|:---------------------------|:--------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | CLASSD_PHASE2_CYC_SHADOWED | Escalation phase duration in cycles. Note that this register can not be modified if [`CLASSD_REGWEN`](#classd_regwen) is false. |

## CLASSD_PHASE3_CYC_SHADOWED
Duration of escalation phase 3 for Class D.
- Offset: `0x56c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CLASSD_REGWEN`](#classd_regwen)

### Fields

```wavejson
{"reg": [{"name": "CLASSD_PHASE3_CYC_SHADOWED", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                                                                                     |
|:------:|:------:|:-------:|:---------------------------|:--------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | CLASSD_PHASE3_CYC_SHADOWED | Escalation phase duration in cycles. Note that this register can not be modified if [`CLASSD_REGWEN`](#classd_regwen) is false. |

## CLASSD_ESC_CNT
Escalation counter in cycles for Class D.
- Offset: `0x570`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "CLASSD_ESC_CNT", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                              |
|:------:|:------:|:-------:|:--------------------------------------------------|
|  31:0  |   ro   |    x    | [CLASSD_ESC_CNT](#classd_esc_cnt--classd_esc_cnt) |

### CLASSD_ESC_CNT . CLASSD_ESC_CNT
Returns the current timeout or escalation count (depending on [`CLASSD_STATE`](#classd_state)).
This register can not be directly cleared. However, SW can indirectly clear as follows.

If the class is in the Timeout state, the timeout can be aborted by clearing the
corresponding interrupt bit.

If this class is in any of the escalation phases (e.g. Phase0), escalation protocol can be
aborted by writing to [`CLASSD_CLR_SHADOWED.`](#classd_clr_shadowed) Note however that has no effect if [`CLASSD_REGWEN`](#classd_regwen)
is set to false (either by SW or by HW via the [`CLASSD_CTRL_SHADOWED.LOCK`](#classd_ctrl_shadowed) feature).

## CLASSD_STATE
Current escalation state of Class D. See also [`CLASSD_ESC_CNT.`](#classd_esc_cnt)
- Offset: `0x574`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "CLASSD_STATE", "bits": 3, "attr": ["ro"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name                                        |
|:------:|:------:|:-------:|:--------------------------------------------|
|  31:3  |        |         | Reserved                                    |
|  2:0   |   ro   |    x    | [CLASSD_STATE](#classd_state--classd_state) |

### CLASSD_STATE . CLASSD_STATE

| Value   | Name     | Description                                    |
|:--------|:---------|:-----------------------------------------------|
| 0x0     | Idle     | No timeout or escalation triggered.            |
| 0x1     | Timeout  | IRQ timeout counter is active.                 |
| 0x2     | FsmError | Terminal error state if FSM has been glitched. |
| 0x3     | Terminal | Terminal state after escalation protocol.      |
| 0x4     | Phase0   | Escalation Phase0 is active.                   |
| 0x5     | Phase1   | Escalation Phase1 is active.                   |
| 0x6     | Phase2   | Escalation Phase2 is active.                   |
| 0x7     | Phase3   | Escalation Phase3 is active.                   |



<!-- END CMDGEN -->
