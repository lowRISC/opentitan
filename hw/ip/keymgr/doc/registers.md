# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/keymgr/data/keymgr.hjson -->
## Summary

| Name                                                                       | Offset   |   Length | Description                                                                |
|:---------------------------------------------------------------------------|:---------|---------:|:---------------------------------------------------------------------------|
| keymgr.[`INTR_STATE`](#intr_state)                                         | 0x0      |        4 | Interrupt State Register                                                   |
| keymgr.[`INTR_ENABLE`](#intr_enable)                                       | 0x4      |        4 | Interrupt Enable Register                                                  |
| keymgr.[`INTR_TEST`](#intr_test)                                           | 0x8      |        4 | Interrupt Test Register                                                    |
| keymgr.[`ALERT_TEST`](#alert_test)                                         | 0xc      |        4 | Alert Test Register                                                        |
| keymgr.[`CFG_REGWEN`](#cfg_regwen)                                         | 0x10     |        4 | Key manager configuration enable                                           |
| keymgr.[`START`](#start)                                                   | 0x14     |        4 | Key manager operation start                                                |
| keymgr.[`CONTROL_SHADOWED`](#control_shadowed)                             | 0x18     |        4 | Key manager operation controls                                             |
| keymgr.[`SIDELOAD_CLEAR`](#sideload_clear)                                 | 0x1c     |        4 | sideload key slots clear                                                   |
| keymgr.[`RESEED_INTERVAL_REGWEN`](#reseed_interval_regwen)                 | 0x20     |        4 | regwen for reseed interval                                                 |
| keymgr.[`RESEED_INTERVAL_SHADOWED`](#reseed_interval_shadowed)             | 0x24     |        4 | Reseed interval for key manager entropy reseed                             |
| keymgr.[`SW_BINDING_REGWEN`](#sw_binding_regwen)                           | 0x28     |        4 | Register write enable for SOFTWARE_BINDING                                 |
| keymgr.[`SEALING_SW_BINDING_0`](#sealing_sw_binding)                       | 0x2c     |        4 | Software binding input to sealing portion of the key manager.              |
| keymgr.[`SEALING_SW_BINDING_1`](#sealing_sw_binding)                       | 0x30     |        4 | Software binding input to sealing portion of the key manager.              |
| keymgr.[`SEALING_SW_BINDING_2`](#sealing_sw_binding)                       | 0x34     |        4 | Software binding input to sealing portion of the key manager.              |
| keymgr.[`SEALING_SW_BINDING_3`](#sealing_sw_binding)                       | 0x38     |        4 | Software binding input to sealing portion of the key manager.              |
| keymgr.[`SEALING_SW_BINDING_4`](#sealing_sw_binding)                       | 0x3c     |        4 | Software binding input to sealing portion of the key manager.              |
| keymgr.[`SEALING_SW_BINDING_5`](#sealing_sw_binding)                       | 0x40     |        4 | Software binding input to sealing portion of the key manager.              |
| keymgr.[`SEALING_SW_BINDING_6`](#sealing_sw_binding)                       | 0x44     |        4 | Software binding input to sealing portion of the key manager.              |
| keymgr.[`SEALING_SW_BINDING_7`](#sealing_sw_binding)                       | 0x48     |        4 | Software binding input to sealing portion of the key manager.              |
| keymgr.[`ATTEST_SW_BINDING_0`](#attest_sw_binding)                         | 0x4c     |        4 | Software binding input to the attestation portion of the key manager.      |
| keymgr.[`ATTEST_SW_BINDING_1`](#attest_sw_binding)                         | 0x50     |        4 | Software binding input to the attestation portion of the key manager.      |
| keymgr.[`ATTEST_SW_BINDING_2`](#attest_sw_binding)                         | 0x54     |        4 | Software binding input to the attestation portion of the key manager.      |
| keymgr.[`ATTEST_SW_BINDING_3`](#attest_sw_binding)                         | 0x58     |        4 | Software binding input to the attestation portion of the key manager.      |
| keymgr.[`ATTEST_SW_BINDING_4`](#attest_sw_binding)                         | 0x5c     |        4 | Software binding input to the attestation portion of the key manager.      |
| keymgr.[`ATTEST_SW_BINDING_5`](#attest_sw_binding)                         | 0x60     |        4 | Software binding input to the attestation portion of the key manager.      |
| keymgr.[`ATTEST_SW_BINDING_6`](#attest_sw_binding)                         | 0x64     |        4 | Software binding input to the attestation portion of the key manager.      |
| keymgr.[`ATTEST_SW_BINDING_7`](#attest_sw_binding)                         | 0x68     |        4 | Software binding input to the attestation portion of the key manager.      |
| keymgr.[`Salt_0`](#salt)                                                   | 0x6c     |        4 | Salt value used as part of output generation                               |
| keymgr.[`Salt_1`](#salt)                                                   | 0x70     |        4 | Salt value used as part of output generation                               |
| keymgr.[`Salt_2`](#salt)                                                   | 0x74     |        4 | Salt value used as part of output generation                               |
| keymgr.[`Salt_3`](#salt)                                                   | 0x78     |        4 | Salt value used as part of output generation                               |
| keymgr.[`Salt_4`](#salt)                                                   | 0x7c     |        4 | Salt value used as part of output generation                               |
| keymgr.[`Salt_5`](#salt)                                                   | 0x80     |        4 | Salt value used as part of output generation                               |
| keymgr.[`Salt_6`](#salt)                                                   | 0x84     |        4 | Salt value used as part of output generation                               |
| keymgr.[`Salt_7`](#salt)                                                   | 0x88     |        4 | Salt value used as part of output generation                               |
| keymgr.[`KEY_VERSION`](#key_version)                                       | 0x8c     |        4 | Version used as part of output generation                                  |
| keymgr.[`MAX_CREATOR_KEY_VER_REGWEN`](#max_creator_key_ver_regwen)         | 0x90     |        4 | Register write enable for MAX_CREATOR_KEY_VERSION                          |
| keymgr.[`MAX_CREATOR_KEY_VER_SHADOWED`](#max_creator_key_ver_shadowed)     | 0x94     |        4 | Max creator key version                                                    |
| keymgr.[`MAX_OWNER_INT_KEY_VER_REGWEN`](#max_owner_int_key_ver_regwen)     | 0x98     |        4 | Register write enable for MAX_OWNER_INT_KEY_VERSION                        |
| keymgr.[`MAX_OWNER_INT_KEY_VER_SHADOWED`](#max_owner_int_key_ver_shadowed) | 0x9c     |        4 | Max owner intermediate key version                                         |
| keymgr.[`MAX_OWNER_KEY_VER_REGWEN`](#max_owner_key_ver_regwen)             | 0xa0     |        4 | Register write enable for MAX_OWNER_KEY_VERSION                            |
| keymgr.[`MAX_OWNER_KEY_VER_SHADOWED`](#max_owner_key_ver_shadowed)         | 0xa4     |        4 | Max owner key version                                                      |
| keymgr.[`SW_SHARE0_OUTPUT_0`](#sw_share0_output)                           | 0xa8     |        4 | Key manager software output.                                               |
| keymgr.[`SW_SHARE0_OUTPUT_1`](#sw_share0_output)                           | 0xac     |        4 | Key manager software output.                                               |
| keymgr.[`SW_SHARE0_OUTPUT_2`](#sw_share0_output)                           | 0xb0     |        4 | Key manager software output.                                               |
| keymgr.[`SW_SHARE0_OUTPUT_3`](#sw_share0_output)                           | 0xb4     |        4 | Key manager software output.                                               |
| keymgr.[`SW_SHARE0_OUTPUT_4`](#sw_share0_output)                           | 0xb8     |        4 | Key manager software output.                                               |
| keymgr.[`SW_SHARE0_OUTPUT_5`](#sw_share0_output)                           | 0xbc     |        4 | Key manager software output.                                               |
| keymgr.[`SW_SHARE0_OUTPUT_6`](#sw_share0_output)                           | 0xc0     |        4 | Key manager software output.                                               |
| keymgr.[`SW_SHARE0_OUTPUT_7`](#sw_share0_output)                           | 0xc4     |        4 | Key manager software output.                                               |
| keymgr.[`SW_SHARE1_OUTPUT_0`](#sw_share1_output)                           | 0xc8     |        4 | Key manager software output.                                               |
| keymgr.[`SW_SHARE1_OUTPUT_1`](#sw_share1_output)                           | 0xcc     |        4 | Key manager software output.                                               |
| keymgr.[`SW_SHARE1_OUTPUT_2`](#sw_share1_output)                           | 0xd0     |        4 | Key manager software output.                                               |
| keymgr.[`SW_SHARE1_OUTPUT_3`](#sw_share1_output)                           | 0xd4     |        4 | Key manager software output.                                               |
| keymgr.[`SW_SHARE1_OUTPUT_4`](#sw_share1_output)                           | 0xd8     |        4 | Key manager software output.                                               |
| keymgr.[`SW_SHARE1_OUTPUT_5`](#sw_share1_output)                           | 0xdc     |        4 | Key manager software output.                                               |
| keymgr.[`SW_SHARE1_OUTPUT_6`](#sw_share1_output)                           | 0xe0     |        4 | Key manager software output.                                               |
| keymgr.[`SW_SHARE1_OUTPUT_7`](#sw_share1_output)                           | 0xe4     |        4 | Key manager software output.                                               |
| keymgr.[`WORKING_STATE`](#working_state)                                   | 0xe8     |        4 | Key manager working state.                                                 |
| keymgr.[`OP_STATUS`](#op_status)                                           | 0xec     |        4 | Key manager status.                                                        |
| keymgr.[`ERR_CODE`](#err_code)                                             | 0xf0     |        4 | Key manager error code.                                                    |
| keymgr.[`FAULT_STATUS`](#fault_status)                                     | 0xf4     |        4 | This register represents both synchronous and asynchronous fatal faults.   |
| keymgr.[`DEBUG`](#debug)                                                   | 0xf8     |        4 | The register holds some debug information that may be convenient if keymgr |

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
- Reset mask: `0x30f0`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"bits": 4}, {"name": "OPERATION", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "CDI_SEL", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 4}, {"name": "DEST_SEL", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 18}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name                                      |
|:------:|:------:|:-------:|:------------------------------------------|
| 31:14  |        |         | Reserved                                  |
| 13:12  |   rw   |   0x0   | [DEST_SEL](#control_shadowed--dest_sel)   |
|  11:8  |        |         | Reserved                                  |
|   7    |   rw   |   0x0   | [CDI_SEL](#control_shadowed--cdi_sel)     |
|  6:4   |   rw   |   0x1   | [OPERATION](#control_shadowed--operation) |
|  3:0   |        |         | Reserved                                  |

### CONTROL_SHADOWED . DEST_SEL
When the OPERATION field is programmed to generate output, this field selects
the appropriate crypto cipher target.

This field should be programmed for both hw / sw generation, as this helps diverisifies the output.

| Value   | Name   | Description                                                                                                                                                                                                                                                                                                                                    |
|:--------|:-------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0x0     | None   | No target selected                                                                                                                                                                                                                                                                                                                             |
| 0x1     | AES    | AES selected                                                                                                                                                                                                                                                                                                                                   |
| 0x2     | KMAC   | KMAC selected                                                                                                                                                                                                                                                                                                                                  |
| 0x3     | OTBN   | OTBN selected.  Note for OTBN hardware operations, the generated output is 384-bits, while for all other operations (including OTBN software), it is 256-bits.  Generating a hardware 384-bit seed directly for OTBN sideload reduces some of the OTBN code burden for entropy expansion. When generating for software, this is not a concern. |


### CONTROL_SHADOWED . CDI_SEL
When the OPERATION field is programmed to generate output, this field selects
the appropriate CDI to use.

This field should be programmed for both hw / sw generation.

| Value   | Name            | Description                 |
|:--------|:----------------|:----------------------------|
| 0x0     | Sealing CDI     | Sealing CDI is selected     |
| 0x1     | Attestation CDI | Attestation CDI is selected |


### CONTROL_SHADOWED . OPERATION
Key manager operation selection. All values not enumerated below behave the same as disable

| Value   | Name               | Description                                                                                                                                                                           |
|:--------|:-------------------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0x0     | Advance            | Advance key manager state.  Advances key manager to the next stage. If key manager is already at last functional state, the advance operation is equivalent to the disable operation. |
| 0x1     | Generate ID        | Generates an identity seed from the current state.                                                                                                                                    |
| 0x2     | Generate SW Output | Generates a key manager output that is visible to software from the current state.                                                                                                    |
| 0x3     | Generate HW Output | Generates a key manager output that is visible only to hardware crypto blocks.                                                                                                        |
| 0x4     | Disable            | Disables key manager operation and moves it to the disabled state.  Note the disabled state is terminal and cannot be recovered without a reset.                                      |

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

|  Bits  |  Type  |  Reset  | Name   | Description                                                 |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------|
| 31:16  |        |         |        | Reserved                                                    |
|  15:0  |   rw   |  0x100  | VAL    | Number of key manager cycles before the entropy is reseeded |

## SW_BINDING_REGWEN
Register write enable for SOFTWARE_BINDING
- Offset: `0x28`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                                                             |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                                                                                                                                                                |
|   0    |  rw0c  |   0x1   | EN     | Software binding register write enable. This is locked by software and unlocked by hardware upon a successful advance call.  Software binding resets to 1, and its value cannot be altered by software until advancement to Init state. |

## SEALING_SW_BINDING
Software binding input to sealing portion of the key manager.
This register is lockable and shared between key manager stages.
This binding value is not considered secret, however its integrity is very important.

The software binding is locked by software and unlocked by hardware upon a successful advance operation.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                 | Offset   |
|:---------------------|:---------|
| SEALING_SW_BINDING_0 | 0x2c     |
| SEALING_SW_BINDING_1 | 0x30     |
| SEALING_SW_BINDING_2 | 0x34     |
| SEALING_SW_BINDING_3 | 0x38     |
| SEALING_SW_BINDING_4 | 0x3c     |
| SEALING_SW_BINDING_5 | 0x40     |
| SEALING_SW_BINDING_6 | 0x44     |
| SEALING_SW_BINDING_7 | 0x48     |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description            |
|:------:|:------:|:-------:|:-------|:-----------------------|
|  31:0  |   rw   |   0x0   | VAL    | Software binding value |

## ATTEST_SW_BINDING
Software binding input to the attestation portion of the key manager.
This register is lockable and shared between key manager stages.
This binding value is not considered secret, however its integrity is very important.

The software binding is locked by software and unlocked by hardware upon a successful advance operation.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                | Offset   |
|:--------------------|:---------|
| ATTEST_SW_BINDING_0 | 0x4c     |
| ATTEST_SW_BINDING_1 | 0x50     |
| ATTEST_SW_BINDING_2 | 0x54     |
| ATTEST_SW_BINDING_3 | 0x58     |
| ATTEST_SW_BINDING_4 | 0x5c     |
| ATTEST_SW_BINDING_5 | 0x60     |
| ATTEST_SW_BINDING_6 | 0x64     |
| ATTEST_SW_BINDING_7 | 0x68     |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description            |
|:------:|:------:|:-------:|:-------|:-----------------------|
|  31:0  |   rw   |   0x0   | VAL    | Software binding value |

## Salt
Salt value used as part of output generation
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name   | Offset   |
|:-------|:---------|
| Salt_0 | 0x6c     |
| Salt_1 | 0x70     |
| Salt_2 | 0x74     |
| Salt_3 | 0x78     |
| Salt_4 | 0x7c     |
| Salt_5 | 0x80     |
| Salt_6 | 0x84     |
| Salt_7 | 0x88     |


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

### Instances

| Name        | Offset   |
|:------------|:---------|
| KEY_VERSION | 0x8c     |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:0  |   rw   |   0x0   | VAL    | Key version   |

## MAX_CREATOR_KEY_VER_REGWEN
Register write enable for MAX_CREATOR_KEY_VERSION
- Offset: `0x90`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                               |
|:------:|:------:|:-------:|:-------|:------------------------------------------|
|  31:1  |        |         |        | Reserved                                  |
|   0    |  rw0c  |   0x1   | EN     | MAX_CREATOR_KEY_VERSION configure enable. |

## MAX_CREATOR_KEY_VER_SHADOWED
Max creator key version
- Offset: `0x94`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`MAX_CREATOR_KEY_VER_REGWEN`](#max_creator_key_ver_regwen)

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                             |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | VAL    | Max key version.  Any key version up to the value specificed in this register is valid. |

## MAX_OWNER_INT_KEY_VER_REGWEN
Register write enable for MAX_OWNER_INT_KEY_VERSION
- Offset: `0x98`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                  |
|:------:|:------:|:-------:|:-------|:---------------------------------------------|
|  31:1  |        |         |        | Reserved                                     |
|   0    |  rw0c  |   0x1   | EN     | MAX_OWNER_INTERMEDIATE_KEY configure enable. |

## MAX_OWNER_INT_KEY_VER_SHADOWED
Max owner intermediate key version
- Offset: `0x9c`
- Reset default: `0x1`
- Reset mask: `0xffffffff`
- Register enable: [`MAX_OWNER_INT_KEY_VER_REGWEN`](#max_owner_int_key_ver_regwen)

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                             |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x1   | VAL    | Max key version.  Any key version up to the value specificed in this register is valid. |

## MAX_OWNER_KEY_VER_REGWEN
Register write enable for MAX_OWNER_KEY_VERSION
- Offset: `0xa0`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                     |
|:------:|:------:|:-------:|:-------|:--------------------------------|
|  31:1  |        |         |        | Reserved                        |
|   0    |  rw0c  |   0x1   | EN     | MAX_OWNER_KEY configure enable. |

## MAX_OWNER_KEY_VER_SHADOWED
Max owner key version
- Offset: `0xa4`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`MAX_OWNER_KEY_VER_REGWEN`](#max_owner_key_ver_regwen)

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                             |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | VAL    | Max key version.  Any key version up to the value specificed in this register is valid. |

## SW_SHARE0_OUTPUT
Key manager software output.

When a software output operation is selected, the results of the operation are placed
here.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name               | Offset   |
|:-------------------|:---------|
| SW_SHARE0_OUTPUT_0 | 0xa8     |
| SW_SHARE0_OUTPUT_1 | 0xac     |
| SW_SHARE0_OUTPUT_2 | 0xb0     |
| SW_SHARE0_OUTPUT_3 | 0xb4     |
| SW_SHARE0_OUTPUT_4 | 0xb8     |
| SW_SHARE0_OUTPUT_5 | 0xbc     |
| SW_SHARE0_OUTPUT_6 | 0xc0     |
| SW_SHARE0_OUTPUT_7 | 0xc4     |


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
| SW_SHARE1_OUTPUT_0 | 0xc8     |
| SW_SHARE1_OUTPUT_1 | 0xcc     |
| SW_SHARE1_OUTPUT_2 | 0xd0     |
| SW_SHARE1_OUTPUT_3 | 0xd4     |
| SW_SHARE1_OUTPUT_4 | 0xd8     |
| SW_SHARE1_OUTPUT_5 | 0xdc     |
| SW_SHARE1_OUTPUT_6 | 0xe0     |
| SW_SHARE1_OUTPUT_7 | 0xe4     |


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
- Offset: `0xe8`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "STATE", "bits": 3, "attr": ["ro"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                           |
|:------:|:------:|:-------:|:-------------------------------|
|  31:3  |        |         | Reserved                       |
|  2:0   |   ro   |   0x0   | [STATE](#working_state--state) |

### WORKING_STATE . STATE
Key manager control state

| Value   | Name                   | Description                                                                                               |
|:--------|:-----------------------|:----------------------------------------------------------------------------------------------------------|
| 0x0     | Reset                  | Key manager control is still in reset.  Please wait for initialization complete before issuing operations |
| 0x1     | Init                   | Key manager control has finished initialization and will now accept software commands.                    |
| 0x2     | Creator Root Key       | Key manager control currently contains the creator root key.                                              |
| 0x3     | Owner Intermediate Key | Key manager control currently contains the owner intermediate key.                                        |
| 0x4     | Owner Key              | Key manager control currently contains the owner key.                                                     |
| 0x5     | Disabled               | Key manager currently disabled. Please reset the key manager. Sideload keys are still valid.              |
| 0x6     | Invalid                | Key manager currently invalid. Please reset the key manager. Sideload keys are no longer valid.           |

Other values are reserved.

## OP_STATUS
Key manager status.

Hardware sets the status based on software initiated operations.
This register must be explicitly cleared by software.
Software clears by writing back whatever it reads.
- Offset: `0xec`
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
- Offset: `0xf0`
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

- Offset: `0xf4`
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
- Offset: `0xf8`
- Reset default: `0x0`
- Reset mask: `0x7f`

### Fields

```wavejson
{"reg": [{"name": "INVALID_CREATOR_SEED", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "INVALID_OWNER_SEED", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "INVALID_DEV_ID", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "INVALID_HEALTH_STATE", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "INVALID_KEY_VERSION", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "INVALID_KEY", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "INVALID_DIGEST", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 25}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                          |
|:------:|:------:|:-------:|:---------------------|:-----------------------------------------------------|
|  31:7  |        |         |                      | Reserved                                             |
|   6    |  rw0c  |   0x0   | INVALID_DIGEST       | ROM digest failed input checks during operation      |
|   5    |  rw0c  |   0x0   | INVALID_KEY          | Key fed to kmac failed input checks during operation |
|   4    |  rw0c  |   0x0   | INVALID_KEY_VERSION  | Key version failed input checks during operation     |
|   3    |  rw0c  |   0x0   | INVALID_HEALTH_STATE | Health state failed input checks during operation    |
|   2    |  rw0c  |   0x0   | INVALID_DEV_ID       | Device ID failed input checks during operation       |
|   1    |  rw0c  |   0x0   | INVALID_OWNER_SEED   | Owner seed failed input checks during operation      |
|   0    |  rw0c  |   0x0   | INVALID_CREATOR_SEED | Creator seed failed input checks during operation    |


<!-- END CMDGEN -->
