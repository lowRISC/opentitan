# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/top_earlgrey/ip_autogen/rv_plic/data/rv_plic.hjson -->
## Summary

| Name                                | Offset    |   Length | Description                                                        |
|:------------------------------------|:----------|---------:|:-------------------------------------------------------------------|
| rv_plic.[`PRIO_0`](#prio)           | 0x0       |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_1`](#prio)           | 0x4       |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_2`](#prio)           | 0x8       |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_3`](#prio)           | 0xc       |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_4`](#prio)           | 0x10      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_5`](#prio)           | 0x14      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_6`](#prio)           | 0x18      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_7`](#prio)           | 0x1c      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_8`](#prio)           | 0x20      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_9`](#prio)           | 0x24      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_10`](#prio)          | 0x28      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_11`](#prio)          | 0x2c      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_12`](#prio)          | 0x30      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_13`](#prio)          | 0x34      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_14`](#prio)          | 0x38      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_15`](#prio)          | 0x3c      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_16`](#prio)          | 0x40      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_17`](#prio)          | 0x44      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_18`](#prio)          | 0x48      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_19`](#prio)          | 0x4c      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_20`](#prio)          | 0x50      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_21`](#prio)          | 0x54      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_22`](#prio)          | 0x58      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_23`](#prio)          | 0x5c      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_24`](#prio)          | 0x60      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_25`](#prio)          | 0x64      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_26`](#prio)          | 0x68      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_27`](#prio)          | 0x6c      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_28`](#prio)          | 0x70      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_29`](#prio)          | 0x74      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_30`](#prio)          | 0x78      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_31`](#prio)          | 0x7c      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_32`](#prio)          | 0x80      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_33`](#prio)          | 0x84      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_34`](#prio)          | 0x88      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_35`](#prio)          | 0x8c      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_36`](#prio)          | 0x90      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_37`](#prio)          | 0x94      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_38`](#prio)          | 0x98      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_39`](#prio)          | 0x9c      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_40`](#prio)          | 0xa0      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_41`](#prio)          | 0xa4      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_42`](#prio)          | 0xa8      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_43`](#prio)          | 0xac      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_44`](#prio)          | 0xb0      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_45`](#prio)          | 0xb4      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_46`](#prio)          | 0xb8      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_47`](#prio)          | 0xbc      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_48`](#prio)          | 0xc0      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_49`](#prio)          | 0xc4      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_50`](#prio)          | 0xc8      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_51`](#prio)          | 0xcc      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_52`](#prio)          | 0xd0      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_53`](#prio)          | 0xd4      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_54`](#prio)          | 0xd8      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_55`](#prio)          | 0xdc      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_56`](#prio)          | 0xe0      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_57`](#prio)          | 0xe4      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_58`](#prio)          | 0xe8      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_59`](#prio)          | 0xec      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_60`](#prio)          | 0xf0      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_61`](#prio)          | 0xf4      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_62`](#prio)          | 0xf8      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_63`](#prio)          | 0xfc      |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_64`](#prio)          | 0x100     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_65`](#prio)          | 0x104     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_66`](#prio)          | 0x108     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_67`](#prio)          | 0x10c     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_68`](#prio)          | 0x110     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_69`](#prio)          | 0x114     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_70`](#prio)          | 0x118     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_71`](#prio)          | 0x11c     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_72`](#prio)          | 0x120     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_73`](#prio)          | 0x124     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_74`](#prio)          | 0x128     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_75`](#prio)          | 0x12c     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_76`](#prio)          | 0x130     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_77`](#prio)          | 0x134     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_78`](#prio)          | 0x138     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_79`](#prio)          | 0x13c     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_80`](#prio)          | 0x140     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_81`](#prio)          | 0x144     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_82`](#prio)          | 0x148     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_83`](#prio)          | 0x14c     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_84`](#prio)          | 0x150     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_85`](#prio)          | 0x154     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_86`](#prio)          | 0x158     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_87`](#prio)          | 0x15c     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_88`](#prio)          | 0x160     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_89`](#prio)          | 0x164     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_90`](#prio)          | 0x168     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_91`](#prio)          | 0x16c     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_92`](#prio)          | 0x170     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_93`](#prio)          | 0x174     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_94`](#prio)          | 0x178     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_95`](#prio)          | 0x17c     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_96`](#prio)          | 0x180     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_97`](#prio)          | 0x184     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_98`](#prio)          | 0x188     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_99`](#prio)          | 0x18c     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_100`](#prio)         | 0x190     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_101`](#prio)         | 0x194     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_102`](#prio)         | 0x198     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_103`](#prio)         | 0x19c     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_104`](#prio)         | 0x1a0     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_105`](#prio)         | 0x1a4     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_106`](#prio)         | 0x1a8     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_107`](#prio)         | 0x1ac     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_108`](#prio)         | 0x1b0     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_109`](#prio)         | 0x1b4     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_110`](#prio)         | 0x1b8     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_111`](#prio)         | 0x1bc     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_112`](#prio)         | 0x1c0     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_113`](#prio)         | 0x1c4     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_114`](#prio)         | 0x1c8     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_115`](#prio)         | 0x1cc     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_116`](#prio)         | 0x1d0     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_117`](#prio)         | 0x1d4     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_118`](#prio)         | 0x1d8     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_119`](#prio)         | 0x1dc     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_120`](#prio)         | 0x1e0     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_121`](#prio)         | 0x1e4     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_122`](#prio)         | 0x1e8     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_123`](#prio)         | 0x1ec     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_124`](#prio)         | 0x1f0     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_125`](#prio)         | 0x1f4     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_126`](#prio)         | 0x1f8     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_127`](#prio)         | 0x1fc     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_128`](#prio)         | 0x200     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_129`](#prio)         | 0x204     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_130`](#prio)         | 0x208     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_131`](#prio)         | 0x20c     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_132`](#prio)         | 0x210     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_133`](#prio)         | 0x214     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_134`](#prio)         | 0x218     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_135`](#prio)         | 0x21c     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_136`](#prio)         | 0x220     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_137`](#prio)         | 0x224     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_138`](#prio)         | 0x228     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_139`](#prio)         | 0x22c     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_140`](#prio)         | 0x230     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_141`](#prio)         | 0x234     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_142`](#prio)         | 0x238     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_143`](#prio)         | 0x23c     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_144`](#prio)         | 0x240     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_145`](#prio)         | 0x244     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_146`](#prio)         | 0x248     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_147`](#prio)         | 0x24c     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_148`](#prio)         | 0x250     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_149`](#prio)         | 0x254     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_150`](#prio)         | 0x258     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_151`](#prio)         | 0x25c     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_152`](#prio)         | 0x260     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_153`](#prio)         | 0x264     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_154`](#prio)         | 0x268     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_155`](#prio)         | 0x26c     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_156`](#prio)         | 0x270     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_157`](#prio)         | 0x274     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_158`](#prio)         | 0x278     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_159`](#prio)         | 0x27c     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_160`](#prio)         | 0x280     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_161`](#prio)         | 0x284     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_162`](#prio)         | 0x288     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_163`](#prio)         | 0x28c     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_164`](#prio)         | 0x290     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_165`](#prio)         | 0x294     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_166`](#prio)         | 0x298     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_167`](#prio)         | 0x29c     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_168`](#prio)         | 0x2a0     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_169`](#prio)         | 0x2a4     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_170`](#prio)         | 0x2a8     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_171`](#prio)         | 0x2ac     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_172`](#prio)         | 0x2b0     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_173`](#prio)         | 0x2b4     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_174`](#prio)         | 0x2b8     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_175`](#prio)         | 0x2bc     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_176`](#prio)         | 0x2c0     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_177`](#prio)         | 0x2c4     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_178`](#prio)         | 0x2c8     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_179`](#prio)         | 0x2cc     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_180`](#prio)         | 0x2d0     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_181`](#prio)         | 0x2d4     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_182`](#prio)         | 0x2d8     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_183`](#prio)         | 0x2dc     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_184`](#prio)         | 0x2e0     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`PRIO_185`](#prio)         | 0x2e4     |        4 | Interrupt Source Priority                                          |
| rv_plic.[`IP_0`](#IP_0)             | 0x1000    |        4 | Interrupt Pending                                                  |
| rv_plic.[`IP_1`](#IP_1)             | 0x1004    |        4 | Interrupt Pending                                                  |
| rv_plic.[`IP_2`](#IP_2)             | 0x1008    |        4 | Interrupt Pending                                                  |
| rv_plic.[`IP_3`](#IP_3)             | 0x100c    |        4 | Interrupt Pending                                                  |
| rv_plic.[`IP_4`](#IP_4)             | 0x1010    |        4 | Interrupt Pending                                                  |
| rv_plic.[`IP_5`](#IP_5)             | 0x1014    |        4 | Interrupt Pending                                                  |
| rv_plic.[`IE0_0`](#IE0_0)           | 0x2000    |        4 | Interrupt Enable for Target 0                                      |
| rv_plic.[`IE0_1`](#IE0_1)           | 0x2004    |        4 | Interrupt Enable for Target 0                                      |
| rv_plic.[`IE0_2`](#IE0_2)           | 0x2008    |        4 | Interrupt Enable for Target 0                                      |
| rv_plic.[`IE0_3`](#IE0_3)           | 0x200c    |        4 | Interrupt Enable for Target 0                                      |
| rv_plic.[`IE0_4`](#IE0_4)           | 0x2010    |        4 | Interrupt Enable for Target 0                                      |
| rv_plic.[`IE0_5`](#IE0_5)           | 0x2014    |        4 | Interrupt Enable for Target 0                                      |
| rv_plic.[`THRESHOLD0`](#threshold0) | 0x200000  |        4 | Threshold of priority for Target 0                                 |
| rv_plic.[`CC0`](#cc0)               | 0x200004  |        4 | Claim interrupt by read, complete interrupt by write for Target 0. |
| rv_plic.[`MSIP0`](#msip0)           | 0x4000000 |        4 | msip for Hart 0.                                                   |
| rv_plic.[`ALERT_TEST`](#alert_test) | 0x4004000 |        4 | Alert Test Register.                                               |

## PRIO
Interrupt Source Priority
- Reset default: `0x0`
- Reset mask: `0x3`

### Instances

| Name     | Offset   |
|:---------|:---------|
| PRIO_0   | 0x0      |
| PRIO_1   | 0x4      |
| PRIO_2   | 0x8      |
| PRIO_3   | 0xc      |
| PRIO_4   | 0x10     |
| PRIO_5   | 0x14     |
| PRIO_6   | 0x18     |
| PRIO_7   | 0x1c     |
| PRIO_8   | 0x20     |
| PRIO_9   | 0x24     |
| PRIO_10  | 0x28     |
| PRIO_11  | 0x2c     |
| PRIO_12  | 0x30     |
| PRIO_13  | 0x34     |
| PRIO_14  | 0x38     |
| PRIO_15  | 0x3c     |
| PRIO_16  | 0x40     |
| PRIO_17  | 0x44     |
| PRIO_18  | 0x48     |
| PRIO_19  | 0x4c     |
| PRIO_20  | 0x50     |
| PRIO_21  | 0x54     |
| PRIO_22  | 0x58     |
| PRIO_23  | 0x5c     |
| PRIO_24  | 0x60     |
| PRIO_25  | 0x64     |
| PRIO_26  | 0x68     |
| PRIO_27  | 0x6c     |
| PRIO_28  | 0x70     |
| PRIO_29  | 0x74     |
| PRIO_30  | 0x78     |
| PRIO_31  | 0x7c     |
| PRIO_32  | 0x80     |
| PRIO_33  | 0x84     |
| PRIO_34  | 0x88     |
| PRIO_35  | 0x8c     |
| PRIO_36  | 0x90     |
| PRIO_37  | 0x94     |
| PRIO_38  | 0x98     |
| PRIO_39  | 0x9c     |
| PRIO_40  | 0xa0     |
| PRIO_41  | 0xa4     |
| PRIO_42  | 0xa8     |
| PRIO_43  | 0xac     |
| PRIO_44  | 0xb0     |
| PRIO_45  | 0xb4     |
| PRIO_46  | 0xb8     |
| PRIO_47  | 0xbc     |
| PRIO_48  | 0xc0     |
| PRIO_49  | 0xc4     |
| PRIO_50  | 0xc8     |
| PRIO_51  | 0xcc     |
| PRIO_52  | 0xd0     |
| PRIO_53  | 0xd4     |
| PRIO_54  | 0xd8     |
| PRIO_55  | 0xdc     |
| PRIO_56  | 0xe0     |
| PRIO_57  | 0xe4     |
| PRIO_58  | 0xe8     |
| PRIO_59  | 0xec     |
| PRIO_60  | 0xf0     |
| PRIO_61  | 0xf4     |
| PRIO_62  | 0xf8     |
| PRIO_63  | 0xfc     |
| PRIO_64  | 0x100    |
| PRIO_65  | 0x104    |
| PRIO_66  | 0x108    |
| PRIO_67  | 0x10c    |
| PRIO_68  | 0x110    |
| PRIO_69  | 0x114    |
| PRIO_70  | 0x118    |
| PRIO_71  | 0x11c    |
| PRIO_72  | 0x120    |
| PRIO_73  | 0x124    |
| PRIO_74  | 0x128    |
| PRIO_75  | 0x12c    |
| PRIO_76  | 0x130    |
| PRIO_77  | 0x134    |
| PRIO_78  | 0x138    |
| PRIO_79  | 0x13c    |
| PRIO_80  | 0x140    |
| PRIO_81  | 0x144    |
| PRIO_82  | 0x148    |
| PRIO_83  | 0x14c    |
| PRIO_84  | 0x150    |
| PRIO_85  | 0x154    |
| PRIO_86  | 0x158    |
| PRIO_87  | 0x15c    |
| PRIO_88  | 0x160    |
| PRIO_89  | 0x164    |
| PRIO_90  | 0x168    |
| PRIO_91  | 0x16c    |
| PRIO_92  | 0x170    |
| PRIO_93  | 0x174    |
| PRIO_94  | 0x178    |
| PRIO_95  | 0x17c    |
| PRIO_96  | 0x180    |
| PRIO_97  | 0x184    |
| PRIO_98  | 0x188    |
| PRIO_99  | 0x18c    |
| PRIO_100 | 0x190    |
| PRIO_101 | 0x194    |
| PRIO_102 | 0x198    |
| PRIO_103 | 0x19c    |
| PRIO_104 | 0x1a0    |
| PRIO_105 | 0x1a4    |
| PRIO_106 | 0x1a8    |
| PRIO_107 | 0x1ac    |
| PRIO_108 | 0x1b0    |
| PRIO_109 | 0x1b4    |
| PRIO_110 | 0x1b8    |
| PRIO_111 | 0x1bc    |
| PRIO_112 | 0x1c0    |
| PRIO_113 | 0x1c4    |
| PRIO_114 | 0x1c8    |
| PRIO_115 | 0x1cc    |
| PRIO_116 | 0x1d0    |
| PRIO_117 | 0x1d4    |
| PRIO_118 | 0x1d8    |
| PRIO_119 | 0x1dc    |
| PRIO_120 | 0x1e0    |
| PRIO_121 | 0x1e4    |
| PRIO_122 | 0x1e8    |
| PRIO_123 | 0x1ec    |
| PRIO_124 | 0x1f0    |
| PRIO_125 | 0x1f4    |
| PRIO_126 | 0x1f8    |
| PRIO_127 | 0x1fc    |
| PRIO_128 | 0x200    |
| PRIO_129 | 0x204    |
| PRIO_130 | 0x208    |
| PRIO_131 | 0x20c    |
| PRIO_132 | 0x210    |
| PRIO_133 | 0x214    |
| PRIO_134 | 0x218    |
| PRIO_135 | 0x21c    |
| PRIO_136 | 0x220    |
| PRIO_137 | 0x224    |
| PRIO_138 | 0x228    |
| PRIO_139 | 0x22c    |
| PRIO_140 | 0x230    |
| PRIO_141 | 0x234    |
| PRIO_142 | 0x238    |
| PRIO_143 | 0x23c    |
| PRIO_144 | 0x240    |
| PRIO_145 | 0x244    |
| PRIO_146 | 0x248    |
| PRIO_147 | 0x24c    |
| PRIO_148 | 0x250    |
| PRIO_149 | 0x254    |
| PRIO_150 | 0x258    |
| PRIO_151 | 0x25c    |
| PRIO_152 | 0x260    |
| PRIO_153 | 0x264    |
| PRIO_154 | 0x268    |
| PRIO_155 | 0x26c    |
| PRIO_156 | 0x270    |
| PRIO_157 | 0x274    |
| PRIO_158 | 0x278    |
| PRIO_159 | 0x27c    |
| PRIO_160 | 0x280    |
| PRIO_161 | 0x284    |
| PRIO_162 | 0x288    |
| PRIO_163 | 0x28c    |
| PRIO_164 | 0x290    |
| PRIO_165 | 0x294    |
| PRIO_166 | 0x298    |
| PRIO_167 | 0x29c    |
| PRIO_168 | 0x2a0    |
| PRIO_169 | 0x2a4    |
| PRIO_170 | 0x2a8    |
| PRIO_171 | 0x2ac    |
| PRIO_172 | 0x2b0    |
| PRIO_173 | 0x2b4    |
| PRIO_174 | 0x2b8    |
| PRIO_175 | 0x2bc    |
| PRIO_176 | 0x2c0    |
| PRIO_177 | 0x2c4    |
| PRIO_178 | 0x2c8    |
| PRIO_179 | 0x2cc    |
| PRIO_180 | 0x2d0    |
| PRIO_181 | 0x2d4    |
| PRIO_182 | 0x2d8    |
| PRIO_183 | 0x2dc    |
| PRIO_184 | 0x2e0    |
| PRIO_185 | 0x2e4    |


### Fields

```wavejson
{"reg": [{"name": "PRIO", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:2  |        |         |        | Reserved      |
|  1:0   |   rw   |   0x0   | PRIO   |               |

## IP_0
Interrupt Pending
- Offset: `0x1000`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "P_0", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_1", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_2", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_3", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_4", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_5", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_6", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_7", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_8", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_9", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_10", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_11", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_12", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_13", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_14", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_15", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_16", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_17", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_18", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_19", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_20", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_21", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_22", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_23", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_24", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_25", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_26", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_27", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_28", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_29", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_30", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_31", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                 |
|:------:|:------:|:-------:|:-------|:----------------------------|
|   31   |   ro   |   0x0   | P_31   | Interrupt Pending of Source |
|   30   |   ro   |   0x0   | P_30   | Interrupt Pending of Source |
|   29   |   ro   |   0x0   | P_29   | Interrupt Pending of Source |
|   28   |   ro   |   0x0   | P_28   | Interrupt Pending of Source |
|   27   |   ro   |   0x0   | P_27   | Interrupt Pending of Source |
|   26   |   ro   |   0x0   | P_26   | Interrupt Pending of Source |
|   25   |   ro   |   0x0   | P_25   | Interrupt Pending of Source |
|   24   |   ro   |   0x0   | P_24   | Interrupt Pending of Source |
|   23   |   ro   |   0x0   | P_23   | Interrupt Pending of Source |
|   22   |   ro   |   0x0   | P_22   | Interrupt Pending of Source |
|   21   |   ro   |   0x0   | P_21   | Interrupt Pending of Source |
|   20   |   ro   |   0x0   | P_20   | Interrupt Pending of Source |
|   19   |   ro   |   0x0   | P_19   | Interrupt Pending of Source |
|   18   |   ro   |   0x0   | P_18   | Interrupt Pending of Source |
|   17   |   ro   |   0x0   | P_17   | Interrupt Pending of Source |
|   16   |   ro   |   0x0   | P_16   | Interrupt Pending of Source |
|   15   |   ro   |   0x0   | P_15   | Interrupt Pending of Source |
|   14   |   ro   |   0x0   | P_14   | Interrupt Pending of Source |
|   13   |   ro   |   0x0   | P_13   | Interrupt Pending of Source |
|   12   |   ro   |   0x0   | P_12   | Interrupt Pending of Source |
|   11   |   ro   |   0x0   | P_11   | Interrupt Pending of Source |
|   10   |   ro   |   0x0   | P_10   | Interrupt Pending of Source |
|   9    |   ro   |   0x0   | P_9    | Interrupt Pending of Source |
|   8    |   ro   |   0x0   | P_8    | Interrupt Pending of Source |
|   7    |   ro   |   0x0   | P_7    | Interrupt Pending of Source |
|   6    |   ro   |   0x0   | P_6    | Interrupt Pending of Source |
|   5    |   ro   |   0x0   | P_5    | Interrupt Pending of Source |
|   4    |   ro   |   0x0   | P_4    | Interrupt Pending of Source |
|   3    |   ro   |   0x0   | P_3    | Interrupt Pending of Source |
|   2    |   ro   |   0x0   | P_2    | Interrupt Pending of Source |
|   1    |   ro   |   0x0   | P_1    | Interrupt Pending of Source |
|   0    |   ro   |   0x0   | P_0    | Interrupt Pending of Source |

## IP_1
Interrupt Pending
- Offset: `0x1004`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "P_32", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_33", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_34", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_35", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_36", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_37", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_38", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_39", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_40", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_41", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_42", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_43", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_44", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_45", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_46", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_47", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_48", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_49", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_50", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_51", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_52", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_53", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_54", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_55", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_56", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_57", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_58", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_59", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_60", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_61", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_62", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_63", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|   31   |   ro   |   0x0   | P_63   | For RV_PLIC1  |
|   30   |   ro   |   0x0   | P_62   | For RV_PLIC1  |
|   29   |   ro   |   0x0   | P_61   | For RV_PLIC1  |
|   28   |   ro   |   0x0   | P_60   | For RV_PLIC1  |
|   27   |   ro   |   0x0   | P_59   | For RV_PLIC1  |
|   26   |   ro   |   0x0   | P_58   | For RV_PLIC1  |
|   25   |   ro   |   0x0   | P_57   | For RV_PLIC1  |
|   24   |   ro   |   0x0   | P_56   | For RV_PLIC1  |
|   23   |   ro   |   0x0   | P_55   | For RV_PLIC1  |
|   22   |   ro   |   0x0   | P_54   | For RV_PLIC1  |
|   21   |   ro   |   0x0   | P_53   | For RV_PLIC1  |
|   20   |   ro   |   0x0   | P_52   | For RV_PLIC1  |
|   19   |   ro   |   0x0   | P_51   | For RV_PLIC1  |
|   18   |   ro   |   0x0   | P_50   | For RV_PLIC1  |
|   17   |   ro   |   0x0   | P_49   | For RV_PLIC1  |
|   16   |   ro   |   0x0   | P_48   | For RV_PLIC1  |
|   15   |   ro   |   0x0   | P_47   | For RV_PLIC1  |
|   14   |   ro   |   0x0   | P_46   | For RV_PLIC1  |
|   13   |   ro   |   0x0   | P_45   | For RV_PLIC1  |
|   12   |   ro   |   0x0   | P_44   | For RV_PLIC1  |
|   11   |   ro   |   0x0   | P_43   | For RV_PLIC1  |
|   10   |   ro   |   0x0   | P_42   | For RV_PLIC1  |
|   9    |   ro   |   0x0   | P_41   | For RV_PLIC1  |
|   8    |   ro   |   0x0   | P_40   | For RV_PLIC1  |
|   7    |   ro   |   0x0   | P_39   | For RV_PLIC1  |
|   6    |   ro   |   0x0   | P_38   | For RV_PLIC1  |
|   5    |   ro   |   0x0   | P_37   | For RV_PLIC1  |
|   4    |   ro   |   0x0   | P_36   | For RV_PLIC1  |
|   3    |   ro   |   0x0   | P_35   | For RV_PLIC1  |
|   2    |   ro   |   0x0   | P_34   | For RV_PLIC1  |
|   1    |   ro   |   0x0   | P_33   | For RV_PLIC1  |
|   0    |   ro   |   0x0   | P_32   | For RV_PLIC1  |

## IP_2
Interrupt Pending
- Offset: `0x1008`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "P_64", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_65", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_66", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_67", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_68", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_69", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_70", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_71", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_72", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_73", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_74", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_75", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_76", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_77", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_78", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_79", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_80", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_81", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_82", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_83", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_84", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_85", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_86", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_87", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_88", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_89", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_90", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_91", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_92", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_93", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_94", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_95", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|   31   |   ro   |   0x0   | P_95   | For RV_PLIC2  |
|   30   |   ro   |   0x0   | P_94   | For RV_PLIC2  |
|   29   |   ro   |   0x0   | P_93   | For RV_PLIC2  |
|   28   |   ro   |   0x0   | P_92   | For RV_PLIC2  |
|   27   |   ro   |   0x0   | P_91   | For RV_PLIC2  |
|   26   |   ro   |   0x0   | P_90   | For RV_PLIC2  |
|   25   |   ro   |   0x0   | P_89   | For RV_PLIC2  |
|   24   |   ro   |   0x0   | P_88   | For RV_PLIC2  |
|   23   |   ro   |   0x0   | P_87   | For RV_PLIC2  |
|   22   |   ro   |   0x0   | P_86   | For RV_PLIC2  |
|   21   |   ro   |   0x0   | P_85   | For RV_PLIC2  |
|   20   |   ro   |   0x0   | P_84   | For RV_PLIC2  |
|   19   |   ro   |   0x0   | P_83   | For RV_PLIC2  |
|   18   |   ro   |   0x0   | P_82   | For RV_PLIC2  |
|   17   |   ro   |   0x0   | P_81   | For RV_PLIC2  |
|   16   |   ro   |   0x0   | P_80   | For RV_PLIC2  |
|   15   |   ro   |   0x0   | P_79   | For RV_PLIC2  |
|   14   |   ro   |   0x0   | P_78   | For RV_PLIC2  |
|   13   |   ro   |   0x0   | P_77   | For RV_PLIC2  |
|   12   |   ro   |   0x0   | P_76   | For RV_PLIC2  |
|   11   |   ro   |   0x0   | P_75   | For RV_PLIC2  |
|   10   |   ro   |   0x0   | P_74   | For RV_PLIC2  |
|   9    |   ro   |   0x0   | P_73   | For RV_PLIC2  |
|   8    |   ro   |   0x0   | P_72   | For RV_PLIC2  |
|   7    |   ro   |   0x0   | P_71   | For RV_PLIC2  |
|   6    |   ro   |   0x0   | P_70   | For RV_PLIC2  |
|   5    |   ro   |   0x0   | P_69   | For RV_PLIC2  |
|   4    |   ro   |   0x0   | P_68   | For RV_PLIC2  |
|   3    |   ro   |   0x0   | P_67   | For RV_PLIC2  |
|   2    |   ro   |   0x0   | P_66   | For RV_PLIC2  |
|   1    |   ro   |   0x0   | P_65   | For RV_PLIC2  |
|   0    |   ro   |   0x0   | P_64   | For RV_PLIC2  |

## IP_3
Interrupt Pending
- Offset: `0x100c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "P_96", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_97", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_98", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_99", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_100", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_101", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_102", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_103", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_104", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_105", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_106", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_107", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_108", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_109", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_110", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_111", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_112", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_113", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_114", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_115", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_116", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_117", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_118", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_119", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_120", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_121", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_122", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_123", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_124", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_125", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_126", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_127", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|   31   |   ro   |   0x0   | P_127  | For RV_PLIC3  |
|   30   |   ro   |   0x0   | P_126  | For RV_PLIC3  |
|   29   |   ro   |   0x0   | P_125  | For RV_PLIC3  |
|   28   |   ro   |   0x0   | P_124  | For RV_PLIC3  |
|   27   |   ro   |   0x0   | P_123  | For RV_PLIC3  |
|   26   |   ro   |   0x0   | P_122  | For RV_PLIC3  |
|   25   |   ro   |   0x0   | P_121  | For RV_PLIC3  |
|   24   |   ro   |   0x0   | P_120  | For RV_PLIC3  |
|   23   |   ro   |   0x0   | P_119  | For RV_PLIC3  |
|   22   |   ro   |   0x0   | P_118  | For RV_PLIC3  |
|   21   |   ro   |   0x0   | P_117  | For RV_PLIC3  |
|   20   |   ro   |   0x0   | P_116  | For RV_PLIC3  |
|   19   |   ro   |   0x0   | P_115  | For RV_PLIC3  |
|   18   |   ro   |   0x0   | P_114  | For RV_PLIC3  |
|   17   |   ro   |   0x0   | P_113  | For RV_PLIC3  |
|   16   |   ro   |   0x0   | P_112  | For RV_PLIC3  |
|   15   |   ro   |   0x0   | P_111  | For RV_PLIC3  |
|   14   |   ro   |   0x0   | P_110  | For RV_PLIC3  |
|   13   |   ro   |   0x0   | P_109  | For RV_PLIC3  |
|   12   |   ro   |   0x0   | P_108  | For RV_PLIC3  |
|   11   |   ro   |   0x0   | P_107  | For RV_PLIC3  |
|   10   |   ro   |   0x0   | P_106  | For RV_PLIC3  |
|   9    |   ro   |   0x0   | P_105  | For RV_PLIC3  |
|   8    |   ro   |   0x0   | P_104  | For RV_PLIC3  |
|   7    |   ro   |   0x0   | P_103  | For RV_PLIC3  |
|   6    |   ro   |   0x0   | P_102  | For RV_PLIC3  |
|   5    |   ro   |   0x0   | P_101  | For RV_PLIC3  |
|   4    |   ro   |   0x0   | P_100  | For RV_PLIC3  |
|   3    |   ro   |   0x0   | P_99   | For RV_PLIC3  |
|   2    |   ro   |   0x0   | P_98   | For RV_PLIC3  |
|   1    |   ro   |   0x0   | P_97   | For RV_PLIC3  |
|   0    |   ro   |   0x0   | P_96   | For RV_PLIC3  |

## IP_4
Interrupt Pending
- Offset: `0x1010`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "P_128", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_129", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_130", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_131", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_132", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_133", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_134", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_135", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_136", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_137", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_138", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_139", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_140", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_141", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_142", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_143", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_144", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_145", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_146", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_147", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_148", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_149", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_150", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_151", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_152", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_153", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_154", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_155", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_156", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_157", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_158", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_159", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|   31   |   ro   |   0x0   | P_159  | For RV_PLIC4  |
|   30   |   ro   |   0x0   | P_158  | For RV_PLIC4  |
|   29   |   ro   |   0x0   | P_157  | For RV_PLIC4  |
|   28   |   ro   |   0x0   | P_156  | For RV_PLIC4  |
|   27   |   ro   |   0x0   | P_155  | For RV_PLIC4  |
|   26   |   ro   |   0x0   | P_154  | For RV_PLIC4  |
|   25   |   ro   |   0x0   | P_153  | For RV_PLIC4  |
|   24   |   ro   |   0x0   | P_152  | For RV_PLIC4  |
|   23   |   ro   |   0x0   | P_151  | For RV_PLIC4  |
|   22   |   ro   |   0x0   | P_150  | For RV_PLIC4  |
|   21   |   ro   |   0x0   | P_149  | For RV_PLIC4  |
|   20   |   ro   |   0x0   | P_148  | For RV_PLIC4  |
|   19   |   ro   |   0x0   | P_147  | For RV_PLIC4  |
|   18   |   ro   |   0x0   | P_146  | For RV_PLIC4  |
|   17   |   ro   |   0x0   | P_145  | For RV_PLIC4  |
|   16   |   ro   |   0x0   | P_144  | For RV_PLIC4  |
|   15   |   ro   |   0x0   | P_143  | For RV_PLIC4  |
|   14   |   ro   |   0x0   | P_142  | For RV_PLIC4  |
|   13   |   ro   |   0x0   | P_141  | For RV_PLIC4  |
|   12   |   ro   |   0x0   | P_140  | For RV_PLIC4  |
|   11   |   ro   |   0x0   | P_139  | For RV_PLIC4  |
|   10   |   ro   |   0x0   | P_138  | For RV_PLIC4  |
|   9    |   ro   |   0x0   | P_137  | For RV_PLIC4  |
|   8    |   ro   |   0x0   | P_136  | For RV_PLIC4  |
|   7    |   ro   |   0x0   | P_135  | For RV_PLIC4  |
|   6    |   ro   |   0x0   | P_134  | For RV_PLIC4  |
|   5    |   ro   |   0x0   | P_133  | For RV_PLIC4  |
|   4    |   ro   |   0x0   | P_132  | For RV_PLIC4  |
|   3    |   ro   |   0x0   | P_131  | For RV_PLIC4  |
|   2    |   ro   |   0x0   | P_130  | For RV_PLIC4  |
|   1    |   ro   |   0x0   | P_129  | For RV_PLIC4  |
|   0    |   ro   |   0x0   | P_128  | For RV_PLIC4  |

## IP_5
Interrupt Pending
- Offset: `0x1014`
- Reset default: `0x0`
- Reset mask: `0x3ffffff`

### Fields

```wavejson
{"reg": [{"name": "P_160", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_161", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_162", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_163", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_164", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_165", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_166", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_167", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_168", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_169", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_170", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_171", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_172", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_173", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_174", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_175", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_176", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_177", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_178", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_179", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_180", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_181", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_182", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_183", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_184", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "P_185", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
| 31:26  |        |         |        | Reserved      |
|   25   |   ro   |   0x0   | P_185  | For RV_PLIC5  |
|   24   |   ro   |   0x0   | P_184  | For RV_PLIC5  |
|   23   |   ro   |   0x0   | P_183  | For RV_PLIC5  |
|   22   |   ro   |   0x0   | P_182  | For RV_PLIC5  |
|   21   |   ro   |   0x0   | P_181  | For RV_PLIC5  |
|   20   |   ro   |   0x0   | P_180  | For RV_PLIC5  |
|   19   |   ro   |   0x0   | P_179  | For RV_PLIC5  |
|   18   |   ro   |   0x0   | P_178  | For RV_PLIC5  |
|   17   |   ro   |   0x0   | P_177  | For RV_PLIC5  |
|   16   |   ro   |   0x0   | P_176  | For RV_PLIC5  |
|   15   |   ro   |   0x0   | P_175  | For RV_PLIC5  |
|   14   |   ro   |   0x0   | P_174  | For RV_PLIC5  |
|   13   |   ro   |   0x0   | P_173  | For RV_PLIC5  |
|   12   |   ro   |   0x0   | P_172  | For RV_PLIC5  |
|   11   |   ro   |   0x0   | P_171  | For RV_PLIC5  |
|   10   |   ro   |   0x0   | P_170  | For RV_PLIC5  |
|   9    |   ro   |   0x0   | P_169  | For RV_PLIC5  |
|   8    |   ro   |   0x0   | P_168  | For RV_PLIC5  |
|   7    |   ro   |   0x0   | P_167  | For RV_PLIC5  |
|   6    |   ro   |   0x0   | P_166  | For RV_PLIC5  |
|   5    |   ro   |   0x0   | P_165  | For RV_PLIC5  |
|   4    |   ro   |   0x0   | P_164  | For RV_PLIC5  |
|   3    |   ro   |   0x0   | P_163  | For RV_PLIC5  |
|   2    |   ro   |   0x0   | P_162  | For RV_PLIC5  |
|   1    |   ro   |   0x0   | P_161  | For RV_PLIC5  |
|   0    |   ro   |   0x0   | P_160  | For RV_PLIC5  |

## IE0_0
Interrupt Enable for Target 0
- Offset: `0x2000`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "E_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_4", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_5", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_6", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_7", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_8", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_9", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_10", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_11", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_12", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_13", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_14", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_15", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_16", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_17", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_18", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_19", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_20", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_21", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_22", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_23", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_24", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_25", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_26", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_27", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_28", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_29", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_30", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_31", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                |
|:------:|:------:|:-------:|:-------|:---------------------------|
|   31   |   rw   |   0x0   | E_31   | Interrupt Enable of Source |
|   30   |   rw   |   0x0   | E_30   | Interrupt Enable of Source |
|   29   |   rw   |   0x0   | E_29   | Interrupt Enable of Source |
|   28   |   rw   |   0x0   | E_28   | Interrupt Enable of Source |
|   27   |   rw   |   0x0   | E_27   | Interrupt Enable of Source |
|   26   |   rw   |   0x0   | E_26   | Interrupt Enable of Source |
|   25   |   rw   |   0x0   | E_25   | Interrupt Enable of Source |
|   24   |   rw   |   0x0   | E_24   | Interrupt Enable of Source |
|   23   |   rw   |   0x0   | E_23   | Interrupt Enable of Source |
|   22   |   rw   |   0x0   | E_22   | Interrupt Enable of Source |
|   21   |   rw   |   0x0   | E_21   | Interrupt Enable of Source |
|   20   |   rw   |   0x0   | E_20   | Interrupt Enable of Source |
|   19   |   rw   |   0x0   | E_19   | Interrupt Enable of Source |
|   18   |   rw   |   0x0   | E_18   | Interrupt Enable of Source |
|   17   |   rw   |   0x0   | E_17   | Interrupt Enable of Source |
|   16   |   rw   |   0x0   | E_16   | Interrupt Enable of Source |
|   15   |   rw   |   0x0   | E_15   | Interrupt Enable of Source |
|   14   |   rw   |   0x0   | E_14   | Interrupt Enable of Source |
|   13   |   rw   |   0x0   | E_13   | Interrupt Enable of Source |
|   12   |   rw   |   0x0   | E_12   | Interrupt Enable of Source |
|   11   |   rw   |   0x0   | E_11   | Interrupt Enable of Source |
|   10   |   rw   |   0x0   | E_10   | Interrupt Enable of Source |
|   9    |   rw   |   0x0   | E_9    | Interrupt Enable of Source |
|   8    |   rw   |   0x0   | E_8    | Interrupt Enable of Source |
|   7    |   rw   |   0x0   | E_7    | Interrupt Enable of Source |
|   6    |   rw   |   0x0   | E_6    | Interrupt Enable of Source |
|   5    |   rw   |   0x0   | E_5    | Interrupt Enable of Source |
|   4    |   rw   |   0x0   | E_4    | Interrupt Enable of Source |
|   3    |   rw   |   0x0   | E_3    | Interrupt Enable of Source |
|   2    |   rw   |   0x0   | E_2    | Interrupt Enable of Source |
|   1    |   rw   |   0x0   | E_1    | Interrupt Enable of Source |
|   0    |   rw   |   0x0   | E_0    | Interrupt Enable of Source |

## IE0_1
Interrupt Enable for Target 0
- Offset: `0x2004`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "E_32", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_33", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_34", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_35", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_36", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_37", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_38", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_39", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_40", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_41", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_42", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_43", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_44", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_45", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_46", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_47", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_48", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_49", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_50", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_51", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_52", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_53", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_54", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_55", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_56", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_57", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_58", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_59", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_60", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_61", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_62", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_63", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|   31   |   rw   |   0x0   | E_63   | For RV_PLIC1  |
|   30   |   rw   |   0x0   | E_62   | For RV_PLIC1  |
|   29   |   rw   |   0x0   | E_61   | For RV_PLIC1  |
|   28   |   rw   |   0x0   | E_60   | For RV_PLIC1  |
|   27   |   rw   |   0x0   | E_59   | For RV_PLIC1  |
|   26   |   rw   |   0x0   | E_58   | For RV_PLIC1  |
|   25   |   rw   |   0x0   | E_57   | For RV_PLIC1  |
|   24   |   rw   |   0x0   | E_56   | For RV_PLIC1  |
|   23   |   rw   |   0x0   | E_55   | For RV_PLIC1  |
|   22   |   rw   |   0x0   | E_54   | For RV_PLIC1  |
|   21   |   rw   |   0x0   | E_53   | For RV_PLIC1  |
|   20   |   rw   |   0x0   | E_52   | For RV_PLIC1  |
|   19   |   rw   |   0x0   | E_51   | For RV_PLIC1  |
|   18   |   rw   |   0x0   | E_50   | For RV_PLIC1  |
|   17   |   rw   |   0x0   | E_49   | For RV_PLIC1  |
|   16   |   rw   |   0x0   | E_48   | For RV_PLIC1  |
|   15   |   rw   |   0x0   | E_47   | For RV_PLIC1  |
|   14   |   rw   |   0x0   | E_46   | For RV_PLIC1  |
|   13   |   rw   |   0x0   | E_45   | For RV_PLIC1  |
|   12   |   rw   |   0x0   | E_44   | For RV_PLIC1  |
|   11   |   rw   |   0x0   | E_43   | For RV_PLIC1  |
|   10   |   rw   |   0x0   | E_42   | For RV_PLIC1  |
|   9    |   rw   |   0x0   | E_41   | For RV_PLIC1  |
|   8    |   rw   |   0x0   | E_40   | For RV_PLIC1  |
|   7    |   rw   |   0x0   | E_39   | For RV_PLIC1  |
|   6    |   rw   |   0x0   | E_38   | For RV_PLIC1  |
|   5    |   rw   |   0x0   | E_37   | For RV_PLIC1  |
|   4    |   rw   |   0x0   | E_36   | For RV_PLIC1  |
|   3    |   rw   |   0x0   | E_35   | For RV_PLIC1  |
|   2    |   rw   |   0x0   | E_34   | For RV_PLIC1  |
|   1    |   rw   |   0x0   | E_33   | For RV_PLIC1  |
|   0    |   rw   |   0x0   | E_32   | For RV_PLIC1  |

## IE0_2
Interrupt Enable for Target 0
- Offset: `0x2008`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "E_64", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_65", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_66", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_67", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_68", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_69", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_70", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_71", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_72", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_73", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_74", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_75", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_76", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_77", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_78", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_79", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_80", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_81", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_82", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_83", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_84", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_85", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_86", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_87", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_88", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_89", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_90", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_91", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_92", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_93", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_94", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_95", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|   31   |   rw   |   0x0   | E_95   | For RV_PLIC2  |
|   30   |   rw   |   0x0   | E_94   | For RV_PLIC2  |
|   29   |   rw   |   0x0   | E_93   | For RV_PLIC2  |
|   28   |   rw   |   0x0   | E_92   | For RV_PLIC2  |
|   27   |   rw   |   0x0   | E_91   | For RV_PLIC2  |
|   26   |   rw   |   0x0   | E_90   | For RV_PLIC2  |
|   25   |   rw   |   0x0   | E_89   | For RV_PLIC2  |
|   24   |   rw   |   0x0   | E_88   | For RV_PLIC2  |
|   23   |   rw   |   0x0   | E_87   | For RV_PLIC2  |
|   22   |   rw   |   0x0   | E_86   | For RV_PLIC2  |
|   21   |   rw   |   0x0   | E_85   | For RV_PLIC2  |
|   20   |   rw   |   0x0   | E_84   | For RV_PLIC2  |
|   19   |   rw   |   0x0   | E_83   | For RV_PLIC2  |
|   18   |   rw   |   0x0   | E_82   | For RV_PLIC2  |
|   17   |   rw   |   0x0   | E_81   | For RV_PLIC2  |
|   16   |   rw   |   0x0   | E_80   | For RV_PLIC2  |
|   15   |   rw   |   0x0   | E_79   | For RV_PLIC2  |
|   14   |   rw   |   0x0   | E_78   | For RV_PLIC2  |
|   13   |   rw   |   0x0   | E_77   | For RV_PLIC2  |
|   12   |   rw   |   0x0   | E_76   | For RV_PLIC2  |
|   11   |   rw   |   0x0   | E_75   | For RV_PLIC2  |
|   10   |   rw   |   0x0   | E_74   | For RV_PLIC2  |
|   9    |   rw   |   0x0   | E_73   | For RV_PLIC2  |
|   8    |   rw   |   0x0   | E_72   | For RV_PLIC2  |
|   7    |   rw   |   0x0   | E_71   | For RV_PLIC2  |
|   6    |   rw   |   0x0   | E_70   | For RV_PLIC2  |
|   5    |   rw   |   0x0   | E_69   | For RV_PLIC2  |
|   4    |   rw   |   0x0   | E_68   | For RV_PLIC2  |
|   3    |   rw   |   0x0   | E_67   | For RV_PLIC2  |
|   2    |   rw   |   0x0   | E_66   | For RV_PLIC2  |
|   1    |   rw   |   0x0   | E_65   | For RV_PLIC2  |
|   0    |   rw   |   0x0   | E_64   | For RV_PLIC2  |

## IE0_3
Interrupt Enable for Target 0
- Offset: `0x200c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "E_96", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_97", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_98", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_99", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_100", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_101", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_102", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_103", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_104", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_105", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_106", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_107", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_108", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_109", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_110", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_111", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_112", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_113", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_114", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_115", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_116", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_117", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_118", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_119", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_120", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_121", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_122", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_123", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_124", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_125", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_126", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_127", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|   31   |   rw   |   0x0   | E_127  | For RV_PLIC3  |
|   30   |   rw   |   0x0   | E_126  | For RV_PLIC3  |
|   29   |   rw   |   0x0   | E_125  | For RV_PLIC3  |
|   28   |   rw   |   0x0   | E_124  | For RV_PLIC3  |
|   27   |   rw   |   0x0   | E_123  | For RV_PLIC3  |
|   26   |   rw   |   0x0   | E_122  | For RV_PLIC3  |
|   25   |   rw   |   0x0   | E_121  | For RV_PLIC3  |
|   24   |   rw   |   0x0   | E_120  | For RV_PLIC3  |
|   23   |   rw   |   0x0   | E_119  | For RV_PLIC3  |
|   22   |   rw   |   0x0   | E_118  | For RV_PLIC3  |
|   21   |   rw   |   0x0   | E_117  | For RV_PLIC3  |
|   20   |   rw   |   0x0   | E_116  | For RV_PLIC3  |
|   19   |   rw   |   0x0   | E_115  | For RV_PLIC3  |
|   18   |   rw   |   0x0   | E_114  | For RV_PLIC3  |
|   17   |   rw   |   0x0   | E_113  | For RV_PLIC3  |
|   16   |   rw   |   0x0   | E_112  | For RV_PLIC3  |
|   15   |   rw   |   0x0   | E_111  | For RV_PLIC3  |
|   14   |   rw   |   0x0   | E_110  | For RV_PLIC3  |
|   13   |   rw   |   0x0   | E_109  | For RV_PLIC3  |
|   12   |   rw   |   0x0   | E_108  | For RV_PLIC3  |
|   11   |   rw   |   0x0   | E_107  | For RV_PLIC3  |
|   10   |   rw   |   0x0   | E_106  | For RV_PLIC3  |
|   9    |   rw   |   0x0   | E_105  | For RV_PLIC3  |
|   8    |   rw   |   0x0   | E_104  | For RV_PLIC3  |
|   7    |   rw   |   0x0   | E_103  | For RV_PLIC3  |
|   6    |   rw   |   0x0   | E_102  | For RV_PLIC3  |
|   5    |   rw   |   0x0   | E_101  | For RV_PLIC3  |
|   4    |   rw   |   0x0   | E_100  | For RV_PLIC3  |
|   3    |   rw   |   0x0   | E_99   | For RV_PLIC3  |
|   2    |   rw   |   0x0   | E_98   | For RV_PLIC3  |
|   1    |   rw   |   0x0   | E_97   | For RV_PLIC3  |
|   0    |   rw   |   0x0   | E_96   | For RV_PLIC3  |

## IE0_4
Interrupt Enable for Target 0
- Offset: `0x2010`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "E_128", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_129", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_130", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_131", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_132", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_133", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_134", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_135", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_136", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_137", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_138", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_139", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_140", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_141", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_142", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_143", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_144", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_145", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_146", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_147", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_148", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_149", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_150", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_151", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_152", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_153", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_154", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_155", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_156", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_157", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_158", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_159", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|   31   |   rw   |   0x0   | E_159  | For RV_PLIC4  |
|   30   |   rw   |   0x0   | E_158  | For RV_PLIC4  |
|   29   |   rw   |   0x0   | E_157  | For RV_PLIC4  |
|   28   |   rw   |   0x0   | E_156  | For RV_PLIC4  |
|   27   |   rw   |   0x0   | E_155  | For RV_PLIC4  |
|   26   |   rw   |   0x0   | E_154  | For RV_PLIC4  |
|   25   |   rw   |   0x0   | E_153  | For RV_PLIC4  |
|   24   |   rw   |   0x0   | E_152  | For RV_PLIC4  |
|   23   |   rw   |   0x0   | E_151  | For RV_PLIC4  |
|   22   |   rw   |   0x0   | E_150  | For RV_PLIC4  |
|   21   |   rw   |   0x0   | E_149  | For RV_PLIC4  |
|   20   |   rw   |   0x0   | E_148  | For RV_PLIC4  |
|   19   |   rw   |   0x0   | E_147  | For RV_PLIC4  |
|   18   |   rw   |   0x0   | E_146  | For RV_PLIC4  |
|   17   |   rw   |   0x0   | E_145  | For RV_PLIC4  |
|   16   |   rw   |   0x0   | E_144  | For RV_PLIC4  |
|   15   |   rw   |   0x0   | E_143  | For RV_PLIC4  |
|   14   |   rw   |   0x0   | E_142  | For RV_PLIC4  |
|   13   |   rw   |   0x0   | E_141  | For RV_PLIC4  |
|   12   |   rw   |   0x0   | E_140  | For RV_PLIC4  |
|   11   |   rw   |   0x0   | E_139  | For RV_PLIC4  |
|   10   |   rw   |   0x0   | E_138  | For RV_PLIC4  |
|   9    |   rw   |   0x0   | E_137  | For RV_PLIC4  |
|   8    |   rw   |   0x0   | E_136  | For RV_PLIC4  |
|   7    |   rw   |   0x0   | E_135  | For RV_PLIC4  |
|   6    |   rw   |   0x0   | E_134  | For RV_PLIC4  |
|   5    |   rw   |   0x0   | E_133  | For RV_PLIC4  |
|   4    |   rw   |   0x0   | E_132  | For RV_PLIC4  |
|   3    |   rw   |   0x0   | E_131  | For RV_PLIC4  |
|   2    |   rw   |   0x0   | E_130  | For RV_PLIC4  |
|   1    |   rw   |   0x0   | E_129  | For RV_PLIC4  |
|   0    |   rw   |   0x0   | E_128  | For RV_PLIC4  |

## IE0_5
Interrupt Enable for Target 0
- Offset: `0x2014`
- Reset default: `0x0`
- Reset mask: `0x3ffffff`

### Fields

```wavejson
{"reg": [{"name": "E_160", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_161", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_162", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_163", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_164", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_165", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_166", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_167", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_168", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_169", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_170", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_171", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_172", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_173", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_174", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_175", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_176", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_177", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_178", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_179", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_180", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_181", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_182", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_183", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_184", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "E_185", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
| 31:26  |        |         |        | Reserved      |
|   25   |   rw   |   0x0   | E_185  | For RV_PLIC5  |
|   24   |   rw   |   0x0   | E_184  | For RV_PLIC5  |
|   23   |   rw   |   0x0   | E_183  | For RV_PLIC5  |
|   22   |   rw   |   0x0   | E_182  | For RV_PLIC5  |
|   21   |   rw   |   0x0   | E_181  | For RV_PLIC5  |
|   20   |   rw   |   0x0   | E_180  | For RV_PLIC5  |
|   19   |   rw   |   0x0   | E_179  | For RV_PLIC5  |
|   18   |   rw   |   0x0   | E_178  | For RV_PLIC5  |
|   17   |   rw   |   0x0   | E_177  | For RV_PLIC5  |
|   16   |   rw   |   0x0   | E_176  | For RV_PLIC5  |
|   15   |   rw   |   0x0   | E_175  | For RV_PLIC5  |
|   14   |   rw   |   0x0   | E_174  | For RV_PLIC5  |
|   13   |   rw   |   0x0   | E_173  | For RV_PLIC5  |
|   12   |   rw   |   0x0   | E_172  | For RV_PLIC5  |
|   11   |   rw   |   0x0   | E_171  | For RV_PLIC5  |
|   10   |   rw   |   0x0   | E_170  | For RV_PLIC5  |
|   9    |   rw   |   0x0   | E_169  | For RV_PLIC5  |
|   8    |   rw   |   0x0   | E_168  | For RV_PLIC5  |
|   7    |   rw   |   0x0   | E_167  | For RV_PLIC5  |
|   6    |   rw   |   0x0   | E_166  | For RV_PLIC5  |
|   5    |   rw   |   0x0   | E_165  | For RV_PLIC5  |
|   4    |   rw   |   0x0   | E_164  | For RV_PLIC5  |
|   3    |   rw   |   0x0   | E_163  | For RV_PLIC5  |
|   2    |   rw   |   0x0   | E_162  | For RV_PLIC5  |
|   1    |   rw   |   0x0   | E_161  | For RV_PLIC5  |
|   0    |   rw   |   0x0   | E_160  | For RV_PLIC5  |

## THRESHOLD0
Threshold of priority for Target 0
- Offset: `0x200000`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "THRESHOLD0", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description   |
|:------:|:------:|:-------:|:-----------|:--------------|
|  31:2  |        |         |            | Reserved      |
|  1:0   |   rw   |   0x0   | THRESHOLD0 |               |

## CC0
Claim interrupt by read, complete interrupt by write for Target 0.
Value read/written is interrupt ID. Reading a value of 0 means no pending interrupts.
- Offset: `0x200004`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "CC0", "bits": 8, "attr": ["rw"], "rotate": 0}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:8  |        |         |        | Reserved      |
|  7:0   |   rw   |    x    | CC0    |               |

## MSIP0
msip for Hart 0.
Write 1 to here asserts software interrupt for Hart msip_o[0], write 0 to clear.
- Offset: `0x4000000`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "MSIP0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                         |
|:------:|:------:|:-------:|:-------|:------------------------------------|
|  31:1  |        |         |        | Reserved                            |
|   0    |   rw   |   0x0   | MSIP0  | Software Interrupt Pending register |

## ALERT_TEST
Alert Test Register.
- Offset: `0x4004000`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "fatal_fault", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                        |
|:------:|:------:|:-------:|:------------|:---------------------------------------------------|
|  31:1  |        |         |             | Reserved                                           |
|   0    |   wo   |    x    | fatal_fault | 'Write 1 to trigger one alert event of this kind.' |


<!-- END CMDGEN -->
