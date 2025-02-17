# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/keymgr_dpe/data/keymgr_dpe.hjson -->
## Summary

| Name                                                               | Offset   |   Length | Description                                                                |
|:-------------------------------------------------------------------|:---------|---------:|:---------------------------------------------------------------------------|
| keymgr_dpe.[`INTR_STATE`](#intr_state)                             | 0x0      |        4 | Interrupt State Register                                                   |
| keymgr_dpe.[`INTR_ENABLE`](#intr_enable)                           | 0x4      |        4 | Interrupt Enable Register                                                  |
| keymgr_dpe.[`INTR_TEST`](#intr_test)                               | 0x8      |        4 | Interrupt Test Register                                                    |
| keymgr_dpe.[`ALERT_TEST`](#alert_test)                             | 0xc      |        4 | Alert Test Register                                                        |
| keymgr_dpe.[`CFG_REGWEN`](#cfg_regwen)                             | 0x10     |        4 | Key manager configuration enable                                           |
| keymgr_dpe.[`START`](#start)                                       | 0x14     |        4 | Key manager operation start                                                |
| keymgr_dpe.[`CONTROL_SHADOWED`](#control_shadowed)                 | 0x18     |        4 | Key manager operation controls                                             |
| keymgr_dpe.[`SIDELOAD_CLEAR`](#sideload_clear)                     | 0x1c     |        4 | sideload key slots clear                                                   |
| keymgr_dpe.[`RESEED_INTERVAL_REGWEN`](#reseed_interval_regwen)     | 0x20     |        4 | regwen for reseed interval                                                 |
| keymgr_dpe.[`RESEED_INTERVAL_SHADOWED`](#reseed_interval_shadowed) | 0x24     |        4 | Reseed interval for key manager entropy reseed                             |
| keymgr_dpe.[`SLOT_POLICY_REGWEN`](#slot_policy_regwen)             | 0x28     |        4 | Register write enable for SLOT_POLICY                                      |
| keymgr_dpe.[`SLOT_POLICY`](#slot_policy)                           | 0x2c     |        4 | Policy bits for the child DPE context                                      |
| keymgr_dpe.[`SW_BINDING_REGWEN`](#sw_binding_regwen)               | 0x30     |        4 | Register write enable for SOFTWARE_BINDING                                 |
| keymgr_dpe.[`SW_BINDING_0`](#sw_binding)                           | 0x34     |        4 | Software binding input of the key manager.                                 |
| keymgr_dpe.[`SW_BINDING_1`](#sw_binding)                           | 0x38     |        4 | Software binding input of the key manager.                                 |
| keymgr_dpe.[`SW_BINDING_2`](#sw_binding)                           | 0x3c     |        4 | Software binding input of the key manager.                                 |
| keymgr_dpe.[`SW_BINDING_3`](#sw_binding)                           | 0x40     |        4 | Software binding input of the key manager.                                 |
| keymgr_dpe.[`SW_BINDING_4`](#sw_binding)                           | 0x44     |        4 | Software binding input of the key manager.                                 |
| keymgr_dpe.[`SW_BINDING_5`](#sw_binding)                           | 0x48     |        4 | Software binding input of the key manager.                                 |
| keymgr_dpe.[`SW_BINDING_6`](#sw_binding)                           | 0x4c     |        4 | Software binding input of the key manager.                                 |
| keymgr_dpe.[`SW_BINDING_7`](#sw_binding)                           | 0x50     |        4 | Software binding input of the key manager.                                 |
| keymgr_dpe.[`SALT_0`](#salt)                                       | 0x54     |        4 | Salt value used as part of output generation                               |
| keymgr_dpe.[`SALT_1`](#salt)                                       | 0x58     |        4 | Salt value used as part of output generation                               |
| keymgr_dpe.[`SALT_2`](#salt)                                       | 0x5c     |        4 | Salt value used as part of output generation                               |
| keymgr_dpe.[`SALT_3`](#salt)                                       | 0x60     |        4 | Salt value used as part of output generation                               |
| keymgr_dpe.[`SALT_4`](#salt)                                       | 0x64     |        4 | Salt value used as part of output generation                               |
| keymgr_dpe.[`SALT_5`](#salt)                                       | 0x68     |        4 | Salt value used as part of output generation                               |
| keymgr_dpe.[`SALT_6`](#salt)                                       | 0x6c     |        4 | Salt value used as part of output generation                               |
| keymgr_dpe.[`SALT_7`](#salt)                                       | 0x70     |        4 | Salt value used as part of output generation                               |
| keymgr_dpe.[`KEY_VERSION`](#key_version)                           | 0x74     |        4 | Version used as part of output generation                                  |
| keymgr_dpe.[`MAX_KEY_VER_REGWEN`](#max_key_ver_regwen)             | 0x78     |        4 | Register write enable for MAX_KEY_VERSION                                  |
| keymgr_dpe.[`MAX_KEY_VER_SHADOWED`](#max_key_ver_shadowed)         | 0x7c     |        4 | Max key version                                                            |
| keymgr_dpe.[`SW_SHARE0_OUTPUT_0`](#sw_share0_output)               | 0x80     |        4 | Key manager software output.                                               |
| keymgr_dpe.[`SW_SHARE0_OUTPUT_1`](#sw_share0_output)               | 0x84     |        4 | Key manager software output.                                               |
| keymgr_dpe.[`SW_SHARE0_OUTPUT_2`](#sw_share0_output)               | 0x88     |        4 | Key manager software output.                                               |
| keymgr_dpe.[`SW_SHARE0_OUTPUT_3`](#sw_share0_output)               | 0x8c     |        4 | Key manager software output.                                               |
| keymgr_dpe.[`SW_SHARE0_OUTPUT_4`](#sw_share0_output)               | 0x90     |        4 | Key manager software output.                                               |
| keymgr_dpe.[`SW_SHARE0_OUTPUT_5`](#sw_share0_output)               | 0x94     |        4 | Key manager software output.                                               |
| keymgr_dpe.[`SW_SHARE0_OUTPUT_6`](#sw_share0_output)               | 0x98     |        4 | Key manager software output.                                               |
| keymgr_dpe.[`SW_SHARE0_OUTPUT_7`](#sw_share0_output)               | 0x9c     |        4 | Key manager software output.                                               |
| keymgr_dpe.[`SW_SHARE1_OUTPUT_0`](#sw_share1_output)               | 0xa0     |        4 | Key manager software output.                                               |
| keymgr_dpe.[`SW_SHARE1_OUTPUT_1`](#sw_share1_output)               | 0xa4     |        4 | Key manager software output.                                               |
| keymgr_dpe.[`SW_SHARE1_OUTPUT_2`](#sw_share1_output)               | 0xa8     |        4 | Key manager software output.                                               |
| keymgr_dpe.[`SW_SHARE1_OUTPUT_3`](#sw_share1_output)               | 0xac     |        4 | Key manager software output.                                               |
| keymgr_dpe.[`SW_SHARE1_OUTPUT_4`](#sw_share1_output)               | 0xb0     |        4 | Key manager software output.                                               |
| keymgr_dpe.[`SW_SHARE1_OUTPUT_5`](#sw_share1_output)               | 0xb4     |        4 | Key manager software output.                                               |
| keymgr_dpe.[`SW_SHARE1_OUTPUT_6`](#sw_share1_output)               | 0xb8     |        4 | Key manager software output.                                               |
| keymgr_dpe.[`SW_SHARE1_OUTPUT_7`](#sw_share1_output)               | 0xbc     |        4 | Key manager software output.                                               |
| keymgr_dpe.[`WORKING_STATE`](#working_state)                       | 0xc0     |        4 | Key manager working state.                                                 |
| keymgr_dpe.[`OP_STATUS`](#op_status)                               | 0xc4     |        4 | Key manager status.                                                        |
| keymgr_dpe.[`ERR_CODE`](#err_code)                                 | 0xc8     |        4 | Key manager error code.                                                    |
| keymgr_dpe.[`FAULT_STATUS`](#fault_status)                         | 0xcc     |        4 | This register represents both synchronous and asynchronous fatal faults.   |
| keymgr_dpe.[`DEBUG`](#debug)                                       | 0xd0     |        4 | The register holds some debug information that may be convenient if keymgr |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "op_done", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 90}}
```

|  Bits  |  Type  |  Reset  | Name    | Description        |
|:------:|:------:|:-------:|:--------|:-------------------|
|  31:1  |        |         |         | Reserved           |
|   0    |  rw1c  |   0x0   | op_done | Operation complete |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "op_done", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 90}}
```

|  Bits  |  Type  |  Reset  | Name    | Description                                                       |
|:------:|:------:|:-------:|:--------|:------------------------------------------------------------------|
|  31:1  |        |         |         | Reserved                                                          |
|   0    |   rw   |   0x0   | op_done | Enable interrupt when [`INTR_STATE.op_done`](#intr_state) is set. |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "op_done", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 90}}
```

|  Bits  |  Type  |  Reset  | Name    | Description                                                |
|:------:|:------:|:-------:|:--------|:-----------------------------------------------------------|
|  31:1  |        |         |         | Reserved                                                   |
|   0    |   wo   |   0x0   | op_done | Write 1 to force [`INTR_STATE.op_done`](#intr_state) to 1. |

## ALERT_TEST
Alert Test Register
- Offset: `0xc`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "recov_operation_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_fault_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 210}}
```

|  Bits  |  Type  |  Reset  | Name                | Description                                      |
|:------:|:------:|:-------:|:--------------------|:-------------------------------------------------|
|  31:2  |        |         |                     | Reserved                                         |
|   1    |   wo   |   0x0   | fatal_fault_err     | Write 1 to trigger one alert event of this kind. |
|   0    |   wo   |   0x0   | recov_operation_err | Write 1 to trigger one alert event of this kind. |

## CFG_REGWEN
Key manager configuration enable
- Offset: `0x10`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                   |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                                                                                                      |
|   0    |   ro   |   0x1   | EN     | key manager configuration enable. When key manager operation is started (see CONTROL), registers protected by this EN are no longer modifiable until the operation completes. |

## START
Key manager operation start
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0x1`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name             |
|:------:|:------:|:-------:|:-----------------|
|  31:1  |        |         | Reserved         |
|   0    |   rw   |   0x0   | [EN](#start--en) |

### START . EN
Start key manager operations

| Value   | Name        | Description                                                                                             |
|:--------|:------------|:--------------------------------------------------------------------------------------------------------|
| 0x1     | Valid state | To trigger a start, this value must be programmed.  All other values are considered no operation start. |

Other values are reserved.

## CONTROL_SHADOWED
Key manager operation controls
- Offset: `0x18`
- Reset default: `0x10`
- Reset mask: `0xcf070`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"bits": 4}, {"name": "OPERATION", "bits": 3, "attr": ["rw"], "rotate": -90}, {"bits": 5}, {"name": "DEST_SEL", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "SLOT_SRC_SEL", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 2}, {"name": "SLOT_DST_SEL", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 12}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name                                            |
|:------:|:------:|:-------:|:------------------------------------------------|
| 31:20  |        |         | Reserved                                        |
| 19:18  |   rw   |   0x0   | [SLOT_DST_SEL](#control_shadowed--slot_dst_sel) |
| 17:16  |        |         | Reserved                                        |
| 15:14  |   rw   |   0x0   | [SLOT_SRC_SEL](#control_shadowed--slot_src_sel) |
| 13:12  |   rw   |   0x0   | [DEST_SEL](#control_shadowed--dest_sel)         |
|  11:7  |        |         | Reserved                                        |
|  6:4   |   rw   |   0x1   | [OPERATION](#control_shadowed--operation)       |
|  3:0   |        |         | Reserved                                        |

### CONTROL_SHADOWED . SLOT_DST_SEL
The destination key slot to be used for the advance and erase operations.

### CONTROL_SHADOWED . SLOT_SRC_SEL
The source key slot to be used for the invoked operation.

### CONTROL_SHADOWED . DEST_SEL
When the OPERATION field is programmed to generate output, this field selects
the target cryptograhic use of the key.

This field should be programmed for both HW / SW generation, as this helps diverisify the output.

| Value   | Name   | Description                                                                                                                                                                                                                                                                                                                                   |
|:--------|:-------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0x0     | None   | No target selected                                                                                                                                                                                                                                                                                                                            |
| 0x1     | AES    | AES selected                                                                                                                                                                                                                                                                                                                                  |
| 0x2     | KMAC   | KMAC selected                                                                                                                                                                                                                                                                                                                                 |
| 0x3     | OTBN   | OTBN selected.  Note for OTBN hardware operations, the generated output is 384-bits, while for all other operations (including OTBN software), it is 256-bits. Generating a hardware 384-bit seed directly for OTBN sideload reduces some of the OTBN code burden for entropy expansion. When generating for software, this is not a concern. |


### CONTROL_SHADOWED . OPERATION
Key manager DPE operation selection

| Value   | Name               | Description                                                                        |
|:--------|:-------------------|:-----------------------------------------------------------------------------------|
| 0x0     | Advance            | Advances a key manager DPE slot.                                                   |
| 0x1     | Erase Slot         | Erases the secrets and resets the valid bit of the destination slot.               |
| 0x2     | Generate SW Output | Generates a key manager output that is visible to software from the current state. |
| 0x3     | Generate HW Output | Generates a cryptographic key that is visible only to hardware crypto blocks.      |
| 0x4     | Disable            | Moves key manager DPE to disabled state.                                           |

Other values are reserved.

## SIDELOAD_CLEAR
sideload key slots clear
- Offset: `0x1c`
- Reset default: `0x0`
- Reset mask: `0x7`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 3, "attr": ["rw"], "rotate": 0}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                        |
|:------:|:------:|:-------:|:----------------------------|
|  31:3  |        |         | Reserved                    |
|  2:0   |   rw   |   0x0   | [VAL](#sideload_clear--val) |

### SIDELOAD_CLEAR . VAL
Depending on the value programmed, a different sideload key slot is cleared.
If the value programmed is not one of the enumerated values below, ALL sideload
key slots are continuously cleared. In order to stop continuous clearing, SW should
toggle the clear bit again (i.e. disable continuous clearing).

| Value   | Name   | Description                                                 |
|:--------|:-------|:------------------------------------------------------------|
| 0x0     | None   | No sideload keys cleared.                                   |
| 0x1     | AES    | The AES sideload key is continuously cleared with entropy.  |
| 0x2     | KMAC   | The KMAC sideload key is continuously cleared with entropy. |
| 0x3     | OTBN   | The OTBN sideload key is continuously cleared with entropy. |

Other values are reserved.

## RESEED_INTERVAL_REGWEN
regwen for reseed interval
- Offset: `0x20`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                              |
|:------:|:------:|:-------:|:-------|:-----------------------------------------|
|  31:1  |        |         |        | Reserved                                 |
|   0    |  rw0c  |   0x1   | EN     | Configuration enable for reseed interval |

## RESEED_INTERVAL_SHADOWED
Reseed interval for key manager entropy reseed
- Offset: `0x24`
- Reset default: `0x100`
- Reset mask: `0xffff`
- Register enable: [`RESEED_INTERVAL_REGWEN`](#reseed_interval_regwen)

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 16, "attr": ["rw"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                   |
|:------:|:------:|:-------:|:-------|:--------------------------------------------------------------|
| 31:16  |        |         |        | Reserved                                                      |
|  15:0  |   rw   |  0x100  | VAL    | Number of internal PRNG updates before a reseed is requested. |

## SLOT_POLICY_REGWEN
Register write enable for SLOT_POLICY
- Offset: `0x28`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                        |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                           |
|   0    |  rw0c  |   0x1   | EN     | Locks SLOT_POLICY register. After a successful advance operation, this register is unlocked again. |

## SLOT_POLICY
Policy bits for the child DPE context
- Offset: `0x2c`
- Reset default: `0x0`
- Reset mask: `0x7`
- Register enable: [`SLOT_POLICY_REGWEN`](#slot_policy_regwen)

### Fields

```wavejson
{"reg": [{"name": "ALLOW_CHILD", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EXPORTABLE", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "RETAIN_PARENT", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                       |
|:------:|:------:|:-------:|:--------------|:------------------------------------------------------------------|
|  31:3  |        |         |               | Reserved                                                          |
|   2    |   rw   |   0x0   | RETAIN_PARENT | Set whether further advance operations force erasure of the slot. |
|   1    |   rw   |   0x0   | EXPORTABLE    | Set whether the key for the target slot is exportable.            |
|   0    |   rw   |   0x0   | ALLOW_CHILD   | Set whether this context allows derivation of further children.   |

## SW_BINDING_REGWEN
Register write enable for SOFTWARE_BINDING
- Offset: `0x30`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                                                            |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                                                                                                                                                               |
|   0    |  rw0c  |   0x1   | EN     | Software binding register write enable. This is locked by software and unlocked by hardware upon a successful advance call. Software binding resets to 1, and its value cannot be altered by software until advancement to Init state. |

## SW_BINDING
Software binding input of the key manager.
This register is lockable and shared between key manager stages.
This binding value is not considered secret, however its integrity is very important.

The software binding is locked by software and unlocked by hardware upon a successful advance operation.
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`SW_BINDING_REGWEN`](#sw_binding_regwen)

### Instances

| Name         | Offset   |
|:-------------|:---------|
| SW_BINDING_0 | 0x34     |
| SW_BINDING_1 | 0x38     |
| SW_BINDING_2 | 0x3c     |
| SW_BINDING_3 | 0x40     |
| SW_BINDING_4 | 0x44     |
| SW_BINDING_5 | 0x48     |
| SW_BINDING_6 | 0x4c     |
| SW_BINDING_7 | 0x50     |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description            |
|:------:|:------:|:-------:|:-------|:-----------------------|
|  31:0  |   rw   |   0x0   | VAL    | Software binding value |

## SALT
Salt value used as part of output generation
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Instances

| Name   | Offset   |
|:-------|:---------|
| SALT_0 | 0x54     |
| SALT_1 | 0x58     |
| SALT_2 | 0x5c     |
| SALT_3 | 0x60     |
| SALT_4 | 0x64     |
| SALT_5 | 0x68     |
| SALT_6 | 0x6c     |
| SALT_7 | 0x70     |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:0  |   rw   |   0x0   | VAL    | Salt value    |

## KEY_VERSION
Version used as part of output generation
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Instances

| Name        | Offset   |
|:------------|:---------|
| KEY_VERSION | 0x74     |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:0  |   rw   |   0x0   | VAL    | Key version   |

## MAX_KEY_VER_REGWEN
Register write enable for MAX_KEY_VERSION
- Offset: `0x78`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                       |
|:------:|:------:|:-------:|:-------|:----------------------------------|
|  31:1  |        |         |        | Reserved                          |
|   0    |  rw0c  |   0x1   | EN     | MAX_KEY_VERSION configure enable. |

## MAX_KEY_VER_SHADOWED
Max key version
- Offset: `0x7c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`MAX_KEY_VER_REGWEN`](#max_key_ver_regwen)

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                            |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | VAL    | Max key version. Any key version up to the value specificed in this register is valid. |

## SW_SHARE0_OUTPUT
Key manager software output.

When a software output operation is selected, the results of the operation are placed
here.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name               | Offset   |
|:-------------------|:---------|
| SW_SHARE0_OUTPUT_0 | 0x80     |
| SW_SHARE0_OUTPUT_1 | 0x84     |
| SW_SHARE0_OUTPUT_2 | 0x88     |
| SW_SHARE0_OUTPUT_3 | 0x8c     |
| SW_SHARE0_OUTPUT_4 | 0x90     |
| SW_SHARE0_OUTPUT_5 | 0x94     |
| SW_SHARE0_OUTPUT_6 | 0x98     |
| SW_SHARE0_OUTPUT_7 | 0x9c     |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rc"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description           |
|:------:|:------:|:-------:|:-------|:----------------------|
|  31:0  |   rc   |   0x0   | VAL    | Software output value |

## SW_SHARE1_OUTPUT
Key manager software output.

When a software output operation is selected, the results of the operation are placed
here.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name               | Offset   |
|:-------------------|:---------|
| SW_SHARE1_OUTPUT_0 | 0xa0     |
| SW_SHARE1_OUTPUT_1 | 0xa4     |
| SW_SHARE1_OUTPUT_2 | 0xa8     |
| SW_SHARE1_OUTPUT_3 | 0xac     |
| SW_SHARE1_OUTPUT_4 | 0xb0     |
| SW_SHARE1_OUTPUT_5 | 0xb4     |
| SW_SHARE1_OUTPUT_6 | 0xb8     |
| SW_SHARE1_OUTPUT_7 | 0xbc     |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rc"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description           |
|:------:|:------:|:-------:|:-------|:----------------------|
|  31:0  |   rc   |   0x0   | VAL    | Software output value |

## WORKING_STATE
Key manager working state.

This is a readout of the current key manager working state
- Offset: `0xc0`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "STATE", "bits": 2, "attr": ["ro"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                           |
|:------:|:------:|:-------:|:-------------------------------|
|  31:2  |        |         | Reserved                       |
|  1:0   |   ro   |   0x0   | [STATE](#working_state--state) |

### WORKING_STATE . STATE
Key manager control state

| Value   | Name      | Description                                                                                               |
|:--------|:----------|:----------------------------------------------------------------------------------------------------------|
| 0x0     | Reset     | Key manager control is still in reset.  Please wait for initialization complete before issuing operations |
| 0x1     | Available | Key manager control has finished latching OTP root key and will now accept software commands.             |
| 0x2     | Disabled  | Key manager currently disabled. Please reset the key manager. Sideload keys are still valid.              |
| 0x3     | Invalid   | Key manager currently invalid. Please reset the key manager. Sideload keys are no longer valid.           |


## OP_STATUS
Key manager status.

Hardware sets the status based on software initiated operations.
This register must be explicitly cleared by software.
Software clears by writing back whatever it reads.
- Offset: `0xc4`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "STATUS", "bits": 2, "attr": ["rw1c"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                         |
|:------:|:------:|:-------:|:-----------------------------|
|  31:2  |        |         | Reserved                     |
|  1:0   |  rw1c  |   0x0   | [STATUS](#op_status--status) |

### OP_STATUS . STATUS
Operation status.

| Value   | Name         | Description                                                               |
|:--------|:-------------|:--------------------------------------------------------------------------|
| 0x0     | Idle         | Key manager is idle                                                       |
| 0x1     | WIP          | Work in progress. A key manager operation has been started and is ongoing |
| 0x2     | DONE_SUCCESS | Operation finished without errors                                         |
| 0x3     | DONE_ERROR   | Operation finished with errors, please see ERR_CODE register.             |


## ERR_CODE
Key manager error code.
This register must be explicitly cleared by software.

This register represents both synchronous and asynchronous recoverable
errors.

Synchronous errors refer to those that only happen when a keymgr operation is
invoked, while asynchronous refers to errors that can happen at any time.
- Offset: `0xc8`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "INVALID_OP", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "INVALID_KMAC_INPUT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "INVALID_SHADOW_UPDATE", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                                          |
|:------:|:------:|:-------:|:----------------------|:---------------------------------------------------------------------|
|  31:3  |        |         |                       | Reserved                                                             |
|   2    |  rw1c  |   0x0   | INVALID_SHADOW_UPDATE | An error observed during shadow register updates, asynchronous error |
|   1    |  rw1c  |   0x0   | INVALID_KMAC_INPUT    | Invalid data issued to kmac interface, synchronous error             |
|   0    |  rw1c  |   0x0   | INVALID_OP            | Invalid operation issued to key manager, synchronous error           |

## FAULT_STATUS
This register represents both synchronous and asynchronous fatal faults.

Synchronous faults refer to those that only happen when a keymgr operation is
invoked, while asynchronous refers to faults that can happen at any time.

- Offset: `0xcc`
- Reset default: `0x0`
- Reset mask: `0x3fff`

### Fields

```wavejson
{"reg": [{"name": "CMD", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "KMAC_FSM", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "KMAC_DONE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "KMAC_OP", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "KMAC_OUT", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "REGFILE_INTG", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SHADOW", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CTRL_FSM_INTG", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CTRL_FSM_CHK", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CTRL_FSM_CNT", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "RESEED_CNT", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SIDE_CTRL_FSM", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SIDE_CTRL_SEL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "KEY_ECC", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 18}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                                               |
|:------:|:------:|:-------:|:--------------|:------------------------------------------------------------------------------------------|
| 31:14  |        |         |               | Reserved                                                                                  |
|   13   |   ro   |   0x0   | KEY_ECC       | Secret key ecc error, asynchronous fault                                                  |
|   12   |   ro   |   0x0   | SIDE_CTRL_SEL | Sideload control key select error, synchronous fault                                      |
|   11   |   ro   |   0x0   | SIDE_CTRL_FSM | Sideload control FSM integrity error, asynchronous fault                                  |
|   10   |   ro   |   0x0   | RESEED_CNT    | Reseed counter integrity error, asynchronous fault                                        |
|   9    |   ro   |   0x0   | CTRL_FSM_CNT  | Control FSM counter integrity error, asynchronous fault                                   |
|   8    |   ro   |   0x0   | CTRL_FSM_CHK  | Control FSM cross check error, asynchronous fault                                         |
|   7    |   ro   |   0x0   | CTRL_FSM_INTG | Control FSM integrity error, asynchronous fault                                           |
|   6    |   ro   |   0x0   | SHADOW        | Shadow copy storage error, asynchronous fault                                             |
|   5    |   ro   |   0x0   | REGFILE_INTG  | Register file integrity error, asynchronous fault                                         |
|   4    |   ro   |   0x0   | KMAC_OUT      | KMAC data returned as all 0's or all 1's - synchronous fault                              |
|   3    |   ro   |   0x0   | KMAC_OP       | KMAC reported an error during keymgr usage, this should never happen - synchronous fault. |
|   2    |   ro   |   0x0   | KMAC_DONE     | The kmac transfer interface encountered an unexpected done, asynchronous fault.           |
|   1    |   ro   |   0x0   | KMAC_FSM      | The kmac transfer interface FSM is in an invalid state, asynchronous fault.               |
|   0    |   ro   |   0x0   | CMD           | A non-onehot command was seen in kmac, asynchronous fault.                                |

## DEBUG
The register holds some debug information that may be convenient if keymgr
misbehaves.
- Offset: `0xd0`
- Reset default: `0x0`
- Reset mask: `0x1ff`

### Fields

```wavejson
{"reg": [{"name": "INVALID_CREATOR_SEED", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "INVALID_OWNER_SEED", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "INVALID_DEV_ID", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "INVALID_HEALTH_STATE", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "INVALID_KEY_VERSION", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "INVALID_KEY", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "INVALID_DIGEST", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "INVALID_ROOT_KEY", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "INACTIVE_LC_EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 23}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                          |
|:------:|:------:|:-------:|:---------------------|:-----------------------------------------------------|
|  31:9  |        |         |                      | Reserved                                             |
|   8    |  rw0c  |   0x0   | INACTIVE_LC_EN       | Enable signal from LC ctrl is deactivated            |
|   7    |  rw0c  |   0x0   | INVALID_ROOT_KEY     | OTP root key was invalid during the first advance    |
|   6    |  rw0c  |   0x0   | INVALID_DIGEST       | ROM digest failed input checks during operation      |
|   5    |  rw0c  |   0x0   | INVALID_KEY          | Key fed to kmac failed input checks during operation |
|   4    |  rw0c  |   0x0   | INVALID_KEY_VERSION  | Key version failed input checks during operation     |
|   3    |  rw0c  |   0x0   | INVALID_HEALTH_STATE | Health state failed input checks during operation    |
|   2    |  rw0c  |   0x0   | INVALID_DEV_ID       | Device ID failed input checks during operation       |
|   1    |  rw0c  |   0x0   | INVALID_OWNER_SEED   | Owner seed failed input checks during operation      |
|   0    |  rw0c  |   0x0   | INVALID_CREATOR_SEED | Creator seed failed input checks during operation    |


<!-- END CMDGEN -->
