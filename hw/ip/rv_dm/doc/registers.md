# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/rv_dm/data/rv_dm.hjson -->
## Summary of the **`regs`** interface's registers

| Name                                                          | Offset   |   Length | Description                                |
|:--------------------------------------------------------------|:---------|---------:|:-------------------------------------------|
| rv_dm.[`ALERT_TEST`](#alert_test)                             | 0x0      |        4 | Alert Test Register                        |
| rv_dm.[`LATE_DEBUG_ENABLE_REGWEN`](#late_debug_enable_regwen) | 0x4      |        4 | Lock bit for !!LATE_DEBUG_ENABLE register. |
| rv_dm.[`LATE_DEBUG_ENABLE`](#late_debug_enable)               | 0x8      |        4 | Debug enable register.                     |

## ALERT_TEST
Alert Test Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "fatal_fault", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                      |
|:------:|:------:|:-------:|:------------|:-------------------------------------------------|
|  31:1  |        |         |             | Reserved                                         |
|   0    |   wo   |   0x0   | fatal_fault | Write 1 to trigger one alert event of this kind. |

## LATE_DEBUG_ENABLE_REGWEN
Lock bit for [`LATE_DEBUG_ENABLE`](#late_debug_enable) register.
- Offset: `0x4`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "LATE_DEBUG_ENABLE_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 260}}
```

|  Bits  |  Type  |  Reset  | Name                     | Description                                                                                                                                                                             |
|:------:|:------:|:-------:|:-------------------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                          | Reserved                                                                                                                                                                                |
|   0    |  rw0c  |   0x1   | LATE_DEBUG_ENABLE_REGWEN | [`LATE_DEBUG_ENABLE`](#late_debug_enable) register configuration enable bit. If this is cleared to 0, the [`LATE_DEBUG_ENABLE`](#late_debug_enable) register cannot be written anymore. |

## LATE_DEBUG_ENABLE
Debug enable register.

If the device is in the DEV lifecycle state and the
DIS_RV_DM_LATE_DEBUG_IN_DEV has been programmed to kMuBi8False
(or an invalid value), the RV_DM gating mechanisms are by default
not ungated until SW writes kMuBi32True to this register.

This can be leveraged to implement a "late debug enable in DEV"
policy, whereby ROM_EXT first locks out any sensitive areas and
functionalities of the device before enabling debug access via
RV_DM.

This register can be locked out via [`LATE_DEBUG_ENABLE_REGWEN.`](#late_debug_enable_regwen)

This register does not have any effect in the following cases:
  - If the device is in a DFT-enabled life cycle state (TEST_UNLOCKED*, RMA)
  - If the device is in the DEV life cycle state and DIS_RV_DM_LATE_DEBUG_IN_DEV has been programmed to kMuBi8True
  - If the device is in a life cycle state where hardware debugging is disabled (TEST_LOCKED*, PROD*, invalid states).
- Offset: `0x8`
- Reset default: `0x69696969`
- Reset mask: `0xffffffff`
- Register enable: [`LATE_DEBUG_ENABLE_REGWEN`](#late_debug_enable_regwen)

### Fields

```wavejson
{"reg": [{"name": "LATE_DEBUG_ENABLE", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |   Reset    | Name              | Description                                                                   |
|:------:|:------:|:----------:|:------------------|:------------------------------------------------------------------------------|
|  31:0  |   rw   | 0x69696969 | LATE_DEBUG_ENABLE | A value of kMuBi32True enables the debug module, all other values disable it. |

## Summary of the **`mem`** interface's registers

| Name                                        | Offset   |   Length | Description                                                                         |
|:--------------------------------------------|:---------|---------:|:------------------------------------------------------------------------------------|
| rv_dm.[`HALTED`](#halted)                   | 0x100    |        4 | Written by a hart whenever it enters debug mode.                                    |
| rv_dm.[`GOING`](#going)                     | 0x108    |        4 | Written by a hart to acknowledge a command.                                         |
| rv_dm.[`RESUMING`](#resuming)               | 0x110    |        4 | Written by a hart to acknowledge a resume request.                                  |
| rv_dm.[`EXCEPTION`](#exception)             | 0x118    |        4 | An exception was triggered while the core was in debug mode.                        |
| rv_dm.[`WHERETO`](#whereto)                 | 0x300    |        4 | A jump instruction the hart executes to begin a command.                            |
| rv_dm.[`ABSTRACTCMD_0`](#abstractcmd)       | 0x338    |        4 | A ROM containing instructions for implementing abstract commands.                   |
| rv_dm.[`ABSTRACTCMD_1`](#abstractcmd)       | 0x33c    |        4 | A ROM containing instructions for implementing abstract commands.                   |
| rv_dm.[`ABSTRACTCMD_2`](#abstractcmd)       | 0x340    |        4 | A ROM containing instructions for implementing abstract commands.                   |
| rv_dm.[`ABSTRACTCMD_3`](#abstractcmd)       | 0x344    |        4 | A ROM containing instructions for implementing abstract commands.                   |
| rv_dm.[`ABSTRACTCMD_4`](#abstractcmd)       | 0x348    |        4 | A ROM containing instructions for implementing abstract commands.                   |
| rv_dm.[`ABSTRACTCMD_5`](#abstractcmd)       | 0x34c    |        4 | A ROM containing instructions for implementing abstract commands.                   |
| rv_dm.[`ABSTRACTCMD_6`](#abstractcmd)       | 0x350    |        4 | A ROM containing instructions for implementing abstract commands.                   |
| rv_dm.[`ABSTRACTCMD_7`](#abstractcmd)       | 0x354    |        4 | A ROM containing instructions for implementing abstract commands.                   |
| rv_dm.[`ABSTRACTCMD_8`](#abstractcmd)       | 0x358    |        4 | A ROM containing instructions for implementing abstract commands.                   |
| rv_dm.[`ABSTRACTCMD_9`](#abstractcmd)       | 0x35c    |        4 | A ROM containing instructions for implementing abstract commands.                   |
| rv_dm.[`PROGRAM_BUFFER_0`](#program_buffer) | 0x360    |        4 | A buffer for the debugger to write small debug mode programs.                       |
| rv_dm.[`PROGRAM_BUFFER_1`](#program_buffer) | 0x364    |        4 | A buffer for the debugger to write small debug mode programs.                       |
| rv_dm.[`PROGRAM_BUFFER_2`](#program_buffer) | 0x368    |        4 | A buffer for the debugger to write small debug mode programs.                       |
| rv_dm.[`PROGRAM_BUFFER_3`](#program_buffer) | 0x36c    |        4 | A buffer for the debugger to write small debug mode programs.                       |
| rv_dm.[`PROGRAM_BUFFER_4`](#program_buffer) | 0x370    |        4 | A buffer for the debugger to write small debug mode programs.                       |
| rv_dm.[`PROGRAM_BUFFER_5`](#program_buffer) | 0x374    |        4 | A buffer for the debugger to write small debug mode programs.                       |
| rv_dm.[`PROGRAM_BUFFER_6`](#program_buffer) | 0x378    |        4 | A buffer for the debugger to write small debug mode programs.                       |
| rv_dm.[`PROGRAM_BUFFER_7`](#program_buffer) | 0x37c    |        4 | A buffer for the debugger to write small debug mode programs.                       |
| rv_dm.[`DATAADDR_0`](#dataaddr)             | 0x380    |        4 | Message Registers for passing arguments and/or return values for abstract commands. |
| rv_dm.[`DATAADDR_1`](#dataaddr)             | 0x384    |        4 | Message Registers for passing arguments and/or return values for abstract commands. |
| rv_dm.[`FLAGS_0`](#flags)                   | 0x400    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_1`](#flags)                   | 0x404    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_2`](#flags)                   | 0x408    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_3`](#flags)                   | 0x40c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_4`](#flags)                   | 0x410    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_5`](#flags)                   | 0x414    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_6`](#flags)                   | 0x418    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_7`](#flags)                   | 0x41c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_8`](#flags)                   | 0x420    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_9`](#flags)                   | 0x424    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_10`](#flags)                  | 0x428    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_11`](#flags)                  | 0x42c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_12`](#flags)                  | 0x430    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_13`](#flags)                  | 0x434    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_14`](#flags)                  | 0x438    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_15`](#flags)                  | 0x43c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_16`](#flags)                  | 0x440    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_17`](#flags)                  | 0x444    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_18`](#flags)                  | 0x448    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_19`](#flags)                  | 0x44c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_20`](#flags)                  | 0x450    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_21`](#flags)                  | 0x454    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_22`](#flags)                  | 0x458    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_23`](#flags)                  | 0x45c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_24`](#flags)                  | 0x460    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_25`](#flags)                  | 0x464    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_26`](#flags)                  | 0x468    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_27`](#flags)                  | 0x46c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_28`](#flags)                  | 0x470    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_29`](#flags)                  | 0x474    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_30`](#flags)                  | 0x478    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_31`](#flags)                  | 0x47c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_32`](#flags)                  | 0x480    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_33`](#flags)                  | 0x484    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_34`](#flags)                  | 0x488    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_35`](#flags)                  | 0x48c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_36`](#flags)                  | 0x490    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_37`](#flags)                  | 0x494    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_38`](#flags)                  | 0x498    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_39`](#flags)                  | 0x49c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_40`](#flags)                  | 0x4a0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_41`](#flags)                  | 0x4a4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_42`](#flags)                  | 0x4a8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_43`](#flags)                  | 0x4ac    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_44`](#flags)                  | 0x4b0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_45`](#flags)                  | 0x4b4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_46`](#flags)                  | 0x4b8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_47`](#flags)                  | 0x4bc    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_48`](#flags)                  | 0x4c0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_49`](#flags)                  | 0x4c4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_50`](#flags)                  | 0x4c8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_51`](#flags)                  | 0x4cc    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_52`](#flags)                  | 0x4d0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_53`](#flags)                  | 0x4d4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_54`](#flags)                  | 0x4d8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_55`](#flags)                  | 0x4dc    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_56`](#flags)                  | 0x4e0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_57`](#flags)                  | 0x4e4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_58`](#flags)                  | 0x4e8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_59`](#flags)                  | 0x4ec    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_60`](#flags)                  | 0x4f0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_61`](#flags)                  | 0x4f4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_62`](#flags)                  | 0x4f8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_63`](#flags)                  | 0x4fc    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_64`](#flags)                  | 0x500    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_65`](#flags)                  | 0x504    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_66`](#flags)                  | 0x508    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_67`](#flags)                  | 0x50c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_68`](#flags)                  | 0x510    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_69`](#flags)                  | 0x514    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_70`](#flags)                  | 0x518    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_71`](#flags)                  | 0x51c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_72`](#flags)                  | 0x520    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_73`](#flags)                  | 0x524    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_74`](#flags)                  | 0x528    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_75`](#flags)                  | 0x52c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_76`](#flags)                  | 0x530    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_77`](#flags)                  | 0x534    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_78`](#flags)                  | 0x538    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_79`](#flags)                  | 0x53c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_80`](#flags)                  | 0x540    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_81`](#flags)                  | 0x544    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_82`](#flags)                  | 0x548    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_83`](#flags)                  | 0x54c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_84`](#flags)                  | 0x550    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_85`](#flags)                  | 0x554    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_86`](#flags)                  | 0x558    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_87`](#flags)                  | 0x55c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_88`](#flags)                  | 0x560    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_89`](#flags)                  | 0x564    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_90`](#flags)                  | 0x568    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_91`](#flags)                  | 0x56c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_92`](#flags)                  | 0x570    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_93`](#flags)                  | 0x574    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_94`](#flags)                  | 0x578    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_95`](#flags)                  | 0x57c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_96`](#flags)                  | 0x580    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_97`](#flags)                  | 0x584    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_98`](#flags)                  | 0x588    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_99`](#flags)                  | 0x58c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_100`](#flags)                 | 0x590    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_101`](#flags)                 | 0x594    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_102`](#flags)                 | 0x598    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_103`](#flags)                 | 0x59c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_104`](#flags)                 | 0x5a0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_105`](#flags)                 | 0x5a4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_106`](#flags)                 | 0x5a8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_107`](#flags)                 | 0x5ac    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_108`](#flags)                 | 0x5b0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_109`](#flags)                 | 0x5b4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_110`](#flags)                 | 0x5b8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_111`](#flags)                 | 0x5bc    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_112`](#flags)                 | 0x5c0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_113`](#flags)                 | 0x5c4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_114`](#flags)                 | 0x5c8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_115`](#flags)                 | 0x5cc    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_116`](#flags)                 | 0x5d0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_117`](#flags)                 | 0x5d4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_118`](#flags)                 | 0x5d8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_119`](#flags)                 | 0x5dc    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_120`](#flags)                 | 0x5e0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_121`](#flags)                 | 0x5e4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_122`](#flags)                 | 0x5e8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_123`](#flags)                 | 0x5ec    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_124`](#flags)                 | 0x5f0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_125`](#flags)                 | 0x5f4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_126`](#flags)                 | 0x5f8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_127`](#flags)                 | 0x5fc    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_128`](#flags)                 | 0x600    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_129`](#flags)                 | 0x604    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_130`](#flags)                 | 0x608    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_131`](#flags)                 | 0x60c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_132`](#flags)                 | 0x610    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_133`](#flags)                 | 0x614    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_134`](#flags)                 | 0x618    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_135`](#flags)                 | 0x61c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_136`](#flags)                 | 0x620    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_137`](#flags)                 | 0x624    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_138`](#flags)                 | 0x628    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_139`](#flags)                 | 0x62c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_140`](#flags)                 | 0x630    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_141`](#flags)                 | 0x634    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_142`](#flags)                 | 0x638    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_143`](#flags)                 | 0x63c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_144`](#flags)                 | 0x640    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_145`](#flags)                 | 0x644    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_146`](#flags)                 | 0x648    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_147`](#flags)                 | 0x64c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_148`](#flags)                 | 0x650    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_149`](#flags)                 | 0x654    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_150`](#flags)                 | 0x658    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_151`](#flags)                 | 0x65c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_152`](#flags)                 | 0x660    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_153`](#flags)                 | 0x664    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_154`](#flags)                 | 0x668    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_155`](#flags)                 | 0x66c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_156`](#flags)                 | 0x670    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_157`](#flags)                 | 0x674    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_158`](#flags)                 | 0x678    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_159`](#flags)                 | 0x67c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_160`](#flags)                 | 0x680    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_161`](#flags)                 | 0x684    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_162`](#flags)                 | 0x688    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_163`](#flags)                 | 0x68c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_164`](#flags)                 | 0x690    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_165`](#flags)                 | 0x694    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_166`](#flags)                 | 0x698    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_167`](#flags)                 | 0x69c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_168`](#flags)                 | 0x6a0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_169`](#flags)                 | 0x6a4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_170`](#flags)                 | 0x6a8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_171`](#flags)                 | 0x6ac    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_172`](#flags)                 | 0x6b0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_173`](#flags)                 | 0x6b4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_174`](#flags)                 | 0x6b8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_175`](#flags)                 | 0x6bc    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_176`](#flags)                 | 0x6c0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_177`](#flags)                 | 0x6c4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_178`](#flags)                 | 0x6c8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_179`](#flags)                 | 0x6cc    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_180`](#flags)                 | 0x6d0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_181`](#flags)                 | 0x6d4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_182`](#flags)                 | 0x6d8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_183`](#flags)                 | 0x6dc    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_184`](#flags)                 | 0x6e0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_185`](#flags)                 | 0x6e4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_186`](#flags)                 | 0x6e8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_187`](#flags)                 | 0x6ec    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_188`](#flags)                 | 0x6f0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_189`](#flags)                 | 0x6f4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_190`](#flags)                 | 0x6f8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_191`](#flags)                 | 0x6fc    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_192`](#flags)                 | 0x700    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_193`](#flags)                 | 0x704    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_194`](#flags)                 | 0x708    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_195`](#flags)                 | 0x70c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_196`](#flags)                 | 0x710    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_197`](#flags)                 | 0x714    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_198`](#flags)                 | 0x718    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_199`](#flags)                 | 0x71c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_200`](#flags)                 | 0x720    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_201`](#flags)                 | 0x724    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_202`](#flags)                 | 0x728    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_203`](#flags)                 | 0x72c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_204`](#flags)                 | 0x730    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_205`](#flags)                 | 0x734    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_206`](#flags)                 | 0x738    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_207`](#flags)                 | 0x73c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_208`](#flags)                 | 0x740    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_209`](#flags)                 | 0x744    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_210`](#flags)                 | 0x748    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_211`](#flags)                 | 0x74c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_212`](#flags)                 | 0x750    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_213`](#flags)                 | 0x754    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_214`](#flags)                 | 0x758    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_215`](#flags)                 | 0x75c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_216`](#flags)                 | 0x760    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_217`](#flags)                 | 0x764    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_218`](#flags)                 | 0x768    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_219`](#flags)                 | 0x76c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_220`](#flags)                 | 0x770    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_221`](#flags)                 | 0x774    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_222`](#flags)                 | 0x778    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_223`](#flags)                 | 0x77c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_224`](#flags)                 | 0x780    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_225`](#flags)                 | 0x784    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_226`](#flags)                 | 0x788    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_227`](#flags)                 | 0x78c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_228`](#flags)                 | 0x790    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_229`](#flags)                 | 0x794    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_230`](#flags)                 | 0x798    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_231`](#flags)                 | 0x79c    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_232`](#flags)                 | 0x7a0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_233`](#flags)                 | 0x7a4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_234`](#flags)                 | 0x7a8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_235`](#flags)                 | 0x7ac    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_236`](#flags)                 | 0x7b0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_237`](#flags)                 | 0x7b4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_238`](#flags)                 | 0x7b8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_239`](#flags)                 | 0x7bc    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_240`](#flags)                 | 0x7c0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_241`](#flags)                 | 0x7c4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_242`](#flags)                 | 0x7c8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_243`](#flags)                 | 0x7cc    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_244`](#flags)                 | 0x7d0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_245`](#flags)                 | 0x7d4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_246`](#flags)                 | 0x7d8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_247`](#flags)                 | 0x7dc    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_248`](#flags)                 | 0x7e0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_249`](#flags)                 | 0x7e4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_250`](#flags)                 | 0x7e8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_251`](#flags)                 | 0x7ec    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_252`](#flags)                 | 0x7f0    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_253`](#flags)                 | 0x7f4    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_254`](#flags)                 | 0x7f8    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`FLAGS_255`](#flags)                 | 0x7fc    |        4 | Flags indicating what a hart in debug mode should do.                               |
| rv_dm.[`ROM`](#rom)                         | 0x800    |     2048 | Access window into the debug ROM.                                                   |

## HALTED
Written by a hart whenever it enters debug mode.

A hart entering debug mode must write its ID to this address to indicate that it has halted.
When the debug module triggers a debug mode (aka halt) request to the hart, the hart will jump to the debug ROM.
In that debug ROM, the hart must write its ID here to acknowledge completion of the request.
When the write is received, the debug module will record that the hart is halted in its status register.
In addition, the debug module may begin to accept abstract commands that run on that hart.

Note that this write upon entering debug mode is also important for indicating that a sequence of debug mode instructions completed.
In that case, the hart would write to this address while it was already halted.
- Offset: `0x100`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "HALTED", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:1  |        |         |        | Reserved      |
|   0    |   wo   |   0x0   | HALTED |               |

## GOING
Written by a hart to acknowledge a command.

A hart that receives an abstract command (indicated by its corresponds [`FLAGS`](#flags) register) must write to this address to acknowledge it received the command.
The value written is unused, but it is conventionally 0.

Upon receiving the write, the debug module will reset the GO field in the selected hart's [`FLAGS`](#flags) register.
The debug module will transition to a state where it awaits the write to [`HALTED`](#halted) to indicate the command has completed.
- Offset: `0x108`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "GOING", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:1  |        |         |        | Reserved      |
|   0    |   wo   |   0x0   | GOING  |               |

## RESUMING
Written by a hart to acknowledge a resume request.

A hart that receives the command to resume from debug mode (via the RESUME flag in its [`FLAGS`](#flags) register) must write its ID to this address.

This write tells the debug module that the command has been acknowledged, and the hart is no longer halted.
- Offset: `0x110`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "RESUMING", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name     | Description   |
|:------:|:------:|:-------:|:---------|:--------------|
|  31:1  |        |         |          | Reserved      |
|   0    |   wo   |   0x0   | RESUMING |               |

## EXCEPTION
An exception was triggered while the core was in debug mode.
- Offset: `0x118`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EXCEPTION", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description   |
|:------:|:------:|:-------:|:----------|:--------------|
|  31:1  |        |         |           | Reserved      |
|   0    |   wo   |   0x0   | EXCEPTION |               |

## WHERETO
A jump instruction the hart executes to begin a command.

When a debugger sends an abstract command to the debug module, the debug module indicates the instruction to run here, which is invariably a jump.
The hart receiving the command must execute the instruction at this address after acknowledging the command with the write to [`GOING.`](#going)

Similarly, when a debugger requests that a hart resume, the debug module supplies a jump instruction to execute here.
In the resume request case, the hart must execute the indicated instruction after acknolwedging the request with the write to [`RESUMING.`](#resuming)
- Offset: `0x300`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "WHERETO", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name    | Description   |
|:------:|:------:|:-------:|:--------|:--------------|
|  31:0  |   ro   |   0x0   | WHERETO |               |

## ABSTRACTCMD
A ROM containing instructions for implementing abstract commands.

The hart executes these instructions at the debug modules behest.
The debug module's jump instruction at [`WHERETO`](#whereto) will land here, except for the AccessRegister command with the "postexec" bit set and the "transfer" bit unset.
See the RISC-V Debug Specification for more information on the encoding of abstract commands.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name          | Offset   |
|:--------------|:---------|
| ABSTRACTCMD_0 | 0x338    |
| ABSTRACTCMD_1 | 0x33c    |
| ABSTRACTCMD_2 | 0x340    |
| ABSTRACTCMD_3 | 0x344    |
| ABSTRACTCMD_4 | 0x348    |
| ABSTRACTCMD_5 | 0x34c    |
| ABSTRACTCMD_6 | 0x350    |
| ABSTRACTCMD_7 | 0x354    |
| ABSTRACTCMD_8 | 0x358    |
| ABSTRACTCMD_9 | 0x35c    |


### Fields

```wavejson
{"reg": [{"name": "ABSTRACTCMD", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name        | Description   |
|:------:|:------:|:-------:|:------------|:--------------|
|  31:0  |   ro   |   0x0   | ABSTRACTCMD |               |

## PROGRAM_BUFFER
A buffer for the debugger to write small debug mode programs.

The hart may run these programs by command from the debugger.
See the RISC-V Debug Specification for more information about the Program Buffer and how it is used with abstract commands and the "postexec" bit.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name             | Offset   |
|:-----------------|:---------|
| PROGRAM_BUFFER_0 | 0x360    |
| PROGRAM_BUFFER_1 | 0x364    |
| PROGRAM_BUFFER_2 | 0x368    |
| PROGRAM_BUFFER_3 | 0x36c    |
| PROGRAM_BUFFER_4 | 0x370    |
| PROGRAM_BUFFER_5 | 0x374    |
| PROGRAM_BUFFER_6 | 0x378    |
| PROGRAM_BUFFER_7 | 0x37c    |


### Fields

```wavejson
{"reg": [{"name": "PROGRAM_BUFFER", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name           | Description   |
|:------:|:------:|:-------:|:---------------|:--------------|
|  31:0  |   ro   |   0x0   | PROGRAM_BUFFER |               |

## DATAADDR
Message Registers for passing arguments and/or return values for abstract commands.

See the RISC-V Debug Specification for more information about Message Registers and their relationship to abstract commands.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name       | Offset   |
|:-----------|:---------|
| DATAADDR_0 | 0x380    |
| DATAADDR_1 | 0x384    |


### Fields

```wavejson
{"reg": [{"name": "DATAADDR", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description   |
|:------:|:------:|:-------:|:---------|:--------------|
|  31:0  |   rw   |   0x0   | DATAADDR |               |

## FLAGS
Flags indicating what a hart in debug mode should do.

These flags are how a debug module signals whether a hart should execute an abstract command, resume from debug mode, or remain idle.

Each hart has its own FLAGS register that is a single byte.
Bit 0 is the GO flag, indicating a request for the selected hart to execute the command.
Bit 1 is the RESUME flag, indication a request for the selected hart to resume from halt/ debug mode.
The other bits are reserved.

The hart finds its own FLAGS register by taking the base address of this group and adding the hart's ID to the byte address.

These are written by the debug module.
When a selected hart writes the [`GOING`](#going) register, the corresponding GO flag is cleared.
When a selected hart writes the [`RESUMING`](#resuming) register, the corresponding RESUME flag is cleared.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name      | Offset   |
|:----------|:---------|
| FLAGS_0   | 0x400    |
| FLAGS_1   | 0x404    |
| FLAGS_2   | 0x408    |
| FLAGS_3   | 0x40c    |
| FLAGS_4   | 0x410    |
| FLAGS_5   | 0x414    |
| FLAGS_6   | 0x418    |
| FLAGS_7   | 0x41c    |
| FLAGS_8   | 0x420    |
| FLAGS_9   | 0x424    |
| FLAGS_10  | 0x428    |
| FLAGS_11  | 0x42c    |
| FLAGS_12  | 0x430    |
| FLAGS_13  | 0x434    |
| FLAGS_14  | 0x438    |
| FLAGS_15  | 0x43c    |
| FLAGS_16  | 0x440    |
| FLAGS_17  | 0x444    |
| FLAGS_18  | 0x448    |
| FLAGS_19  | 0x44c    |
| FLAGS_20  | 0x450    |
| FLAGS_21  | 0x454    |
| FLAGS_22  | 0x458    |
| FLAGS_23  | 0x45c    |
| FLAGS_24  | 0x460    |
| FLAGS_25  | 0x464    |
| FLAGS_26  | 0x468    |
| FLAGS_27  | 0x46c    |
| FLAGS_28  | 0x470    |
| FLAGS_29  | 0x474    |
| FLAGS_30  | 0x478    |
| FLAGS_31  | 0x47c    |
| FLAGS_32  | 0x480    |
| FLAGS_33  | 0x484    |
| FLAGS_34  | 0x488    |
| FLAGS_35  | 0x48c    |
| FLAGS_36  | 0x490    |
| FLAGS_37  | 0x494    |
| FLAGS_38  | 0x498    |
| FLAGS_39  | 0x49c    |
| FLAGS_40  | 0x4a0    |
| FLAGS_41  | 0x4a4    |
| FLAGS_42  | 0x4a8    |
| FLAGS_43  | 0x4ac    |
| FLAGS_44  | 0x4b0    |
| FLAGS_45  | 0x4b4    |
| FLAGS_46  | 0x4b8    |
| FLAGS_47  | 0x4bc    |
| FLAGS_48  | 0x4c0    |
| FLAGS_49  | 0x4c4    |
| FLAGS_50  | 0x4c8    |
| FLAGS_51  | 0x4cc    |
| FLAGS_52  | 0x4d0    |
| FLAGS_53  | 0x4d4    |
| FLAGS_54  | 0x4d8    |
| FLAGS_55  | 0x4dc    |
| FLAGS_56  | 0x4e0    |
| FLAGS_57  | 0x4e4    |
| FLAGS_58  | 0x4e8    |
| FLAGS_59  | 0x4ec    |
| FLAGS_60  | 0x4f0    |
| FLAGS_61  | 0x4f4    |
| FLAGS_62  | 0x4f8    |
| FLAGS_63  | 0x4fc    |
| FLAGS_64  | 0x500    |
| FLAGS_65  | 0x504    |
| FLAGS_66  | 0x508    |
| FLAGS_67  | 0x50c    |
| FLAGS_68  | 0x510    |
| FLAGS_69  | 0x514    |
| FLAGS_70  | 0x518    |
| FLAGS_71  | 0x51c    |
| FLAGS_72  | 0x520    |
| FLAGS_73  | 0x524    |
| FLAGS_74  | 0x528    |
| FLAGS_75  | 0x52c    |
| FLAGS_76  | 0x530    |
| FLAGS_77  | 0x534    |
| FLAGS_78  | 0x538    |
| FLAGS_79  | 0x53c    |
| FLAGS_80  | 0x540    |
| FLAGS_81  | 0x544    |
| FLAGS_82  | 0x548    |
| FLAGS_83  | 0x54c    |
| FLAGS_84  | 0x550    |
| FLAGS_85  | 0x554    |
| FLAGS_86  | 0x558    |
| FLAGS_87  | 0x55c    |
| FLAGS_88  | 0x560    |
| FLAGS_89  | 0x564    |
| FLAGS_90  | 0x568    |
| FLAGS_91  | 0x56c    |
| FLAGS_92  | 0x570    |
| FLAGS_93  | 0x574    |
| FLAGS_94  | 0x578    |
| FLAGS_95  | 0x57c    |
| FLAGS_96  | 0x580    |
| FLAGS_97  | 0x584    |
| FLAGS_98  | 0x588    |
| FLAGS_99  | 0x58c    |
| FLAGS_100 | 0x590    |
| FLAGS_101 | 0x594    |
| FLAGS_102 | 0x598    |
| FLAGS_103 | 0x59c    |
| FLAGS_104 | 0x5a0    |
| FLAGS_105 | 0x5a4    |
| FLAGS_106 | 0x5a8    |
| FLAGS_107 | 0x5ac    |
| FLAGS_108 | 0x5b0    |
| FLAGS_109 | 0x5b4    |
| FLAGS_110 | 0x5b8    |
| FLAGS_111 | 0x5bc    |
| FLAGS_112 | 0x5c0    |
| FLAGS_113 | 0x5c4    |
| FLAGS_114 | 0x5c8    |
| FLAGS_115 | 0x5cc    |
| FLAGS_116 | 0x5d0    |
| FLAGS_117 | 0x5d4    |
| FLAGS_118 | 0x5d8    |
| FLAGS_119 | 0x5dc    |
| FLAGS_120 | 0x5e0    |
| FLAGS_121 | 0x5e4    |
| FLAGS_122 | 0x5e8    |
| FLAGS_123 | 0x5ec    |
| FLAGS_124 | 0x5f0    |
| FLAGS_125 | 0x5f4    |
| FLAGS_126 | 0x5f8    |
| FLAGS_127 | 0x5fc    |
| FLAGS_128 | 0x600    |
| FLAGS_129 | 0x604    |
| FLAGS_130 | 0x608    |
| FLAGS_131 | 0x60c    |
| FLAGS_132 | 0x610    |
| FLAGS_133 | 0x614    |
| FLAGS_134 | 0x618    |
| FLAGS_135 | 0x61c    |
| FLAGS_136 | 0x620    |
| FLAGS_137 | 0x624    |
| FLAGS_138 | 0x628    |
| FLAGS_139 | 0x62c    |
| FLAGS_140 | 0x630    |
| FLAGS_141 | 0x634    |
| FLAGS_142 | 0x638    |
| FLAGS_143 | 0x63c    |
| FLAGS_144 | 0x640    |
| FLAGS_145 | 0x644    |
| FLAGS_146 | 0x648    |
| FLAGS_147 | 0x64c    |
| FLAGS_148 | 0x650    |
| FLAGS_149 | 0x654    |
| FLAGS_150 | 0x658    |
| FLAGS_151 | 0x65c    |
| FLAGS_152 | 0x660    |
| FLAGS_153 | 0x664    |
| FLAGS_154 | 0x668    |
| FLAGS_155 | 0x66c    |
| FLAGS_156 | 0x670    |
| FLAGS_157 | 0x674    |
| FLAGS_158 | 0x678    |
| FLAGS_159 | 0x67c    |
| FLAGS_160 | 0x680    |
| FLAGS_161 | 0x684    |
| FLAGS_162 | 0x688    |
| FLAGS_163 | 0x68c    |
| FLAGS_164 | 0x690    |
| FLAGS_165 | 0x694    |
| FLAGS_166 | 0x698    |
| FLAGS_167 | 0x69c    |
| FLAGS_168 | 0x6a0    |
| FLAGS_169 | 0x6a4    |
| FLAGS_170 | 0x6a8    |
| FLAGS_171 | 0x6ac    |
| FLAGS_172 | 0x6b0    |
| FLAGS_173 | 0x6b4    |
| FLAGS_174 | 0x6b8    |
| FLAGS_175 | 0x6bc    |
| FLAGS_176 | 0x6c0    |
| FLAGS_177 | 0x6c4    |
| FLAGS_178 | 0x6c8    |
| FLAGS_179 | 0x6cc    |
| FLAGS_180 | 0x6d0    |
| FLAGS_181 | 0x6d4    |
| FLAGS_182 | 0x6d8    |
| FLAGS_183 | 0x6dc    |
| FLAGS_184 | 0x6e0    |
| FLAGS_185 | 0x6e4    |
| FLAGS_186 | 0x6e8    |
| FLAGS_187 | 0x6ec    |
| FLAGS_188 | 0x6f0    |
| FLAGS_189 | 0x6f4    |
| FLAGS_190 | 0x6f8    |
| FLAGS_191 | 0x6fc    |
| FLAGS_192 | 0x700    |
| FLAGS_193 | 0x704    |
| FLAGS_194 | 0x708    |
| FLAGS_195 | 0x70c    |
| FLAGS_196 | 0x710    |
| FLAGS_197 | 0x714    |
| FLAGS_198 | 0x718    |
| FLAGS_199 | 0x71c    |
| FLAGS_200 | 0x720    |
| FLAGS_201 | 0x724    |
| FLAGS_202 | 0x728    |
| FLAGS_203 | 0x72c    |
| FLAGS_204 | 0x730    |
| FLAGS_205 | 0x734    |
| FLAGS_206 | 0x738    |
| FLAGS_207 | 0x73c    |
| FLAGS_208 | 0x740    |
| FLAGS_209 | 0x744    |
| FLAGS_210 | 0x748    |
| FLAGS_211 | 0x74c    |
| FLAGS_212 | 0x750    |
| FLAGS_213 | 0x754    |
| FLAGS_214 | 0x758    |
| FLAGS_215 | 0x75c    |
| FLAGS_216 | 0x760    |
| FLAGS_217 | 0x764    |
| FLAGS_218 | 0x768    |
| FLAGS_219 | 0x76c    |
| FLAGS_220 | 0x770    |
| FLAGS_221 | 0x774    |
| FLAGS_222 | 0x778    |
| FLAGS_223 | 0x77c    |
| FLAGS_224 | 0x780    |
| FLAGS_225 | 0x784    |
| FLAGS_226 | 0x788    |
| FLAGS_227 | 0x78c    |
| FLAGS_228 | 0x790    |
| FLAGS_229 | 0x794    |
| FLAGS_230 | 0x798    |
| FLAGS_231 | 0x79c    |
| FLAGS_232 | 0x7a0    |
| FLAGS_233 | 0x7a4    |
| FLAGS_234 | 0x7a8    |
| FLAGS_235 | 0x7ac    |
| FLAGS_236 | 0x7b0    |
| FLAGS_237 | 0x7b4    |
| FLAGS_238 | 0x7b8    |
| FLAGS_239 | 0x7bc    |
| FLAGS_240 | 0x7c0    |
| FLAGS_241 | 0x7c4    |
| FLAGS_242 | 0x7c8    |
| FLAGS_243 | 0x7cc    |
| FLAGS_244 | 0x7d0    |
| FLAGS_245 | 0x7d4    |
| FLAGS_246 | 0x7d8    |
| FLAGS_247 | 0x7dc    |
| FLAGS_248 | 0x7e0    |
| FLAGS_249 | 0x7e4    |
| FLAGS_250 | 0x7e8    |
| FLAGS_251 | 0x7ec    |
| FLAGS_252 | 0x7f0    |
| FLAGS_253 | 0x7f4    |
| FLAGS_254 | 0x7f8    |
| FLAGS_255 | 0x7fc    |


### Fields

```wavejson
{"reg": [{"name": "FLAGS", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:0  |   ro   |   0x0   | FLAGS  |               |

## ROM
Access window into the debug ROM.

- Word Aligned Offset Range: `0x800`to`0xffc`
- Size (words): `512`
- Access: `ro`
- Byte writes are *not* supported.


<!-- END CMDGEN -->
