## Summary

| Name                                                | Offset   |   Length | Description                              |
|:----------------------------------------------------|:---------|---------:|:-----------------------------------------|
| ascon.[`ALERT_TEST`](#alert_test)                   | 0x0      |        4 | Alert Test Register                      |
| ascon.[`KEY_SHARE0_0`](#key_share0)                 | 0x4      |        4 | Initial Key Registers Share 0.           |
| ascon.[`KEY_SHARE0_1`](#key_share0)                 | 0x8      |        4 | Initial Key Registers Share 0.           |
| ascon.[`KEY_SHARE0_2`](#key_share0)                 | 0xc      |        4 | Initial Key Registers Share 0.           |
| ascon.[`KEY_SHARE0_3`](#key_share0)                 | 0x10     |        4 | Initial Key Registers Share 0.           |
| ascon.[`KEY_SHARE1_0`](#key_share1)                 | 0x14     |        4 | Initial Key Registers Share 1.           |
| ascon.[`KEY_SHARE1_1`](#key_share1)                 | 0x18     |        4 | Initial Key Registers Share 1.           |
| ascon.[`KEY_SHARE1_2`](#key_share1)                 | 0x1c     |        4 | Initial Key Registers Share 1.           |
| ascon.[`KEY_SHARE1_3`](#key_share1)                 | 0x20     |        4 | Initial Key Registers Share 1.           |
| ascon.[`NONCE_SHARE0_0`](#nonce_share0)             | 0x24     |        4 | Input Nonce Register Share 0.            |
| ascon.[`NONCE_SHARE0_1`](#nonce_share0)             | 0x28     |        4 | Input Nonce Register Share 0.            |
| ascon.[`NONCE_SHARE0_2`](#nonce_share0)             | 0x2c     |        4 | Input Nonce Register Share 0.            |
| ascon.[`NONCE_SHARE0_3`](#nonce_share0)             | 0x30     |        4 | Input Nonce Register Share 0.            |
| ascon.[`NONCE_SHARE1_0`](#nonce_share1)             | 0x34     |        4 | Input Nonce Register Share 1.            |
| ascon.[`NONCE_SHARE1_1`](#nonce_share1)             | 0x38     |        4 | Input Nonce Register Share 1.            |
| ascon.[`NONCE_SHARE1_2`](#nonce_share1)             | 0x3c     |        4 | Input Nonce Register Share 1.            |
| ascon.[`NONCE_SHARE1_3`](#nonce_share1)             | 0x40     |        4 | Input Nonce Register Share 1.            |
| ascon.[`DATA_IN_SHARE0_0`](#data_in_share0)         | 0x44     |        4 | Input Data Register 0.                   |
| ascon.[`DATA_IN_SHARE0_1`](#data_in_share0)         | 0x48     |        4 | Input Data Register 0.                   |
| ascon.[`DATA_IN_SHARE0_2`](#data_in_share0)         | 0x4c     |        4 | Input Data Register 0.                   |
| ascon.[`DATA_IN_SHARE0_3`](#data_in_share0)         | 0x50     |        4 | Input Data Register 0.                   |
| ascon.[`DATA_IN_SHARE1_0`](#data_in_share1)         | 0x54     |        4 | Data Input Register Share 1              |
| ascon.[`DATA_IN_SHARE1_1`](#data_in_share1)         | 0x58     |        4 | Data Input Register Share 1              |
| ascon.[`DATA_IN_SHARE1_2`](#data_in_share1)         | 0x5c     |        4 | Data Input Register Share 1              |
| ascon.[`DATA_IN_SHARE1_3`](#data_in_share1)         | 0x60     |        4 | Data Input Register Share 1              |
| ascon.[`TAG_IN_0`](#tag_in)                         | 0x64     |        4 | Input TAG Register.                      |
| ascon.[`TAG_IN_1`](#tag_in)                         | 0x68     |        4 | Input TAG Register.                      |
| ascon.[`TAG_IN_2`](#tag_in)                         | 0x6c     |        4 | Input TAG Register.                      |
| ascon.[`TAG_IN_3`](#tag_in)                         | 0x70     |        4 | Input TAG Register.                      |
| ascon.[`MSG_OUT_0`](#msg_out)                       | 0x74     |        4 | Output Data Register.                    |
| ascon.[`MSG_OUT_1`](#msg_out)                       | 0x78     |        4 | Output Data Register.                    |
| ascon.[`MSG_OUT_2`](#msg_out)                       | 0x7c     |        4 | Output Data Register.                    |
| ascon.[`MSG_OUT_3`](#msg_out)                       | 0x80     |        4 | Output Data Register.                    |
| ascon.[`TAG_OUT_0`](#tag_out)                       | 0x84     |        4 | Output Tag Register.                     |
| ascon.[`TAG_OUT_1`](#tag_out)                       | 0x88     |        4 | Output Tag Register.                     |
| ascon.[`TAG_OUT_2`](#tag_out)                       | 0x8c     |        4 | Output Tag Register.                     |
| ascon.[`TAG_OUT_3`](#tag_out)                       | 0x90     |        4 | Output Tag Register.                     |
| ascon.[`CTRL_SHADOWED`](#ctrl_shadowed)             | 0x94     |        4 | Control Register.                        |
| ascon.[`CTRL_AUX_SHADOWED`](#ctrl_aux_shadowed)     | 0x98     |        4 | Auxiliary Control Register.              |
| ascon.[`CTRL_AUX_REGWEN`](#ctrl_aux_regwen)         | 0x9c     |        4 | Lock bit for Auxiliary Control Register. |
| ascon.[`BLOCK_CTRL_SHADOWED`](#block_ctrl_shadowed) | 0xa0     |        4 | Block Control Register.                  |
| ascon.[`TRIGGER`](#trigger)                         | 0xa4     |        4 | Trigger Register.                        |
| ascon.[`STATUS`](#status)                           | 0xa8     |        4 | Status Register                          |
| ascon.[`OUTPUT_VALID`](#output_valid)               | 0xac     |        4 | Output Valid Register                    |
| ascon.[`FSM_STATE`](#fsm_state)                     | 0xb0     |        4 | Main FSM State register.                 |
| ascon.[`FSM_STATE_REGREN`](#fsm_state_regren)       | 0xb4     |        4 | Lock bit for Auxiliary Control Register. |
| ascon.[`ERROR`](#error)                             | 0xb8     |        4 | Error Register.                          |

## ALERT_TEST
Alert Test Register
- Offset: `0x0`
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

## KEY_SHARE0
Initial Key Registers Share 0.

The actual initial key corresponds to Initial Key Registers Share 0 XORed with Initial Key Registers Share 1.
Loaded into the internal Full Key register upon starting encryption/decryption.
All key registers (Share 0 and Share 1) must be written at least once when the key is changed.
The order in which the registers are updated does not matter.
Can only be updated when the Ascon unit is idle.
If the Ascon unit is non-idle, writes to these registers are ignored.
Upon reset, these registers are cleared with pseudo-random data.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name         | Offset   |
|:-------------|:---------|
| KEY_SHARE0_0 | 0x4      |
| KEY_SHARE0_1 | 0x8      |
| KEY_SHARE0_2 | 0xc      |
| KEY_SHARE0_3 | 0x10     |


### Fields

```wavejson
{"reg": [{"name": "key_share0", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description         |
|:------:|:------:|:-------:|:-----------|:--------------------|
|  31:0  |   wo   |   0x0   | key_share0 | Initial Key Share 0 |

## KEY_SHARE1
Initial Key Registers Share 1.

The actual initial key corresponds to Initial Key Registers Share 0 XORed with Initial Key Registers Share 1.
Loaded into the internal Full Key register upon starting encryption/decryption.
All key registers (Share 0 and Share 1) must be written at least once when the key is changed.
The order in which the registers are updated does not matter.
Can only be updated when the Ascon unit is idle.
If the Ascon unit is non-idle, writes to these registers are ignored.
Upon reset, these registers are cleared with pseudo-random data.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name         | Offset   |
|:-------------|:---------|
| KEY_SHARE1_0 | 0x14     |
| KEY_SHARE1_1 | 0x18     |
| KEY_SHARE1_2 | 0x1c     |
| KEY_SHARE1_3 | 0x20     |


### Fields

```wavejson
{"reg": [{"name": "key_share1", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description         |
|:------:|:------:|:-------:|:-----------|:--------------------|
|  31:0  |   wo   |   0x0   | key_share1 | Initial Key Share 1 |

## NONCE_SHARE0
Input Nonce Register Share 0.
The actual data corresponds to Nonce Input Registers Share 0 XORed with Nonce Input Registers Share 1.
If SW does not want to provide the Nonce masked, it can simply set one share to all zeros and provide the unmasked nonce in the other share.
All nonce registers (Share 0 and Share 1) must be written each time a new message is processed.
Ascon requires the nonce to be unique for each message.
However there are no hardware checks to enforce this.
The order in which the registers are updated does not matter.
If the user fails to update the register the [`ERROR.NO_NONCE`](#error) Register is set.
Can only be updated when the Ascon unit is idle.
If the Ascon unit is non-idle, writes to these registers are ignored.
Upon reset, these registers are cleared with pseudo-random data.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name           | Offset   |
|:---------------|:---------|
| NONCE_SHARE0_0 | 0x24     |
| NONCE_SHARE0_1 | 0x28     |
| NONCE_SHARE0_2 | 0x2c     |
| NONCE_SHARE0_3 | 0x30     |


### Fields

```wavejson
{"reg": [{"name": "nonce", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description         |
|:------:|:------:|:-------:|:-------|:--------------------|
|  31:0  |   wo   |    x    | nonce  | Input Nonce Share 0 |

## NONCE_SHARE1
Input Nonce Register Share 1.
The actual data corresponds to Nonce Input Registers Share 0 XORed with Nonce Input Registers Share 1.
If SW does not want to provide the Nonce masked, it can simply set one share to all zeros and provide the unmasked nonce in the other share.
All nonce registers (Share 0 and Share 1) must be written each time a new message is processed.
Ascon requires the nonce to be unique for each message
However there are no hardware checks to enforce this.
The order in which the registers are updated does not matter.
If the user fails to update the register the [`ERROR.NO_NONCE`](#error) Register is set.
Can only be updated when the Ascon unit is idle.
If the Ascon unit is non-idle, writes to these registers are ignored.
Upon reset, these registers are cleared with pseudo-random data.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name           | Offset   |
|:---------------|:---------|
| NONCE_SHARE1_0 | 0x34     |
| NONCE_SHARE1_1 | 0x38     |
| NONCE_SHARE1_2 | 0x3c     |
| NONCE_SHARE1_3 | 0x40     |


### Fields

```wavejson
{"reg": [{"name": "nonce", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description         |
|:------:|:------:|:-------:|:-------|:--------------------|
|  31:0  |   wo   |    x    | nonce  | Input Nonce Share 1 |

## DATA_IN_SHARE0
Input Data Register 0.
The actual data corresponds to Data Input Registers Share 0 XORed with Data Input Registers Share 1.
This register holds Share 0 of one input block.
This is either the associated data, plaintext or the ciphertext, depending on the mode.
All registers must be written each time a new block is processed.
Otherwise the engine stalls until all registers have been written.
For Ascon 128 the upper 64 bit can be set to any value
For partial blocks the unused bytes can be set to any value.
The order in which the registers are updated does not matter.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name             | Offset   |
|:-----------------|:---------|
| DATA_IN_SHARE0_0 | 0x44     |
| DATA_IN_SHARE0_1 | 0x48     |
| DATA_IN_SHARE0_2 | 0x4c     |
| DATA_IN_SHARE0_3 | 0x50     |


### Fields

```wavejson
{"reg": [{"name": "msg_in", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description        |
|:------:|:------:|:-------:|:-------|:-------------------|
|  31:0  |   wo   |    x    | msg_in | Input Data Share 0 |

## DATA_IN_SHARE1
Data Input Register Share 1
The actual message corresponds to Data Input Registers Share 0 XORed with Data Input Registers Share 1.
This register holds Share 1 of one data input block.
This is either the associated data, plaintext or the ciphertext, depending on the mode.
If CTRL_SHADOWED.masked_{ad,msg}_input = 1, all registers must be written each time a block of associated data
or message is processed
If CTRL_SHADOWED.masked_{ad,msg}_input = 0, the write operation tracking for these registers is disabled.
Software should set Share 1 to all zeros before the first block of associated data / message is written to
Share 0.
This basically disables input masking.
For Ascon 128 the upper 64 bit can be set to any value.
For partial blocks the unused bytes can be set to any value.
The order in which the registers are updated does not matter.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name             | Offset   |
|:-----------------|:---------|
| DATA_IN_SHARE1_0 | 0x54     |
| DATA_IN_SHARE1_1 | 0x58     |
| DATA_IN_SHARE1_2 | 0x5c     |
| DATA_IN_SHARE1_3 | 0x60     |


### Fields

```wavejson
{"reg": [{"name": "msg_in", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description        |
|:------:|:------:|:-------:|:-------|:-------------------|
|  31:0  |   wo   |    x    | msg_in | Input Data Share 1 |

## TAG_IN
Input TAG Register.
This register holds the expected tag for authenticated decryption.
All registers must be written each time a new decryption is started.
The order in which the registers are updated does not matter.
Upon reset, these registers are cleared with pseudo-random data.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name     | Offset   |
|:---------|:---------|
| TAG_IN_0 | 0x64     |
| TAG_IN_1 | 0x68     |
| TAG_IN_2 | 0x6c     |
| TAG_IN_3 | 0x70     |


### Fields

```wavejson
{"reg": [{"name": "tag_in", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:0  |   wo   |   0x0   | tag_in | Input TAG     |

## MSG_OUT
Output Data Register.
Holds the output data produced by the Ascon unit during the last encryption/decryption operation.
If CTRL_AUX_SHADOWED.force_data_overwrite = 0 (see Control Register),
the Ascon unit is stalled when the previous output data has not yet been read and is about to be overwritten.
Each register has to be read at least once.
The order in which the registers are read does not matter.
Upon reset, these registers are cleared with pseudo-random data.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name      | Offset   |
|:----------|:---------|
| MSG_OUT_0 | 0x74     |
| MSG_OUT_1 | 0x78     |
| MSG_OUT_2 | 0x7c     |
| MSG_OUT_3 | 0x80     |


### Fields

```wavejson
{"reg": [{"name": "msg_out", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name    | Description   |
|:------:|:------:|:-------:|:--------|:--------------|
|  31:0  |   ro   |    x    | msg_out | Output Data   |

## TAG_OUT
Output Tag Register.
Holds the computed tag that is produced by the Ascon unit during an authenticated encryption/decryption.
Each register has to be read at least once for encryption.
For decryption the read is optional, but allows software to double check the result.
The order in which the registers are read does not matter.
Upon reset, these registers are cleared with pseudo-random data.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name      | Offset   |
|:----------|:---------|
| TAG_OUT_0 | 0x84     |
| TAG_OUT_1 | 0x88     |
| TAG_OUT_2 | 0x8c     |
| TAG_OUT_3 | 0x90     |


### Fields

```wavejson
{"reg": [{"name": "tag_out", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name    | Description   |
|:------:|:------:|:-------:|:--------|:--------------|
|  31:0  |   ro   |    x    | tag_out | Output Tag    |

## CTRL_SHADOWED
Control Register.
Can only be updated when the Ascon unit is idle.
If the Ascon unit is non-idle, writes to this register are ignored.
This register is shadowed, meaning two subsequent write operations are required to change its content.
If the two write operations try to set a different value, a recoverable alert is triggered (See Status Register).
A read operation clears the internal phase tracking:
The next write operation is always considered a first write operation of an update sequence.
Any write operation to this register will clear the status tracking required for automatic mode (See [`CTRL_AUX_SHADOWED.manual_start_trigger`](#ctrl_aux_shadowed)).
A write to the Control Register is considered the start of a new message.
Hence, software needs to provide a new Nonce and input data afterwards.
- Offset: `0x94`
- Reset default: `0x0`
- Reset mask: `0x3ff`

### Fields

```wavejson
{"reg": [{"name": "OPERATION", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "ASCON_VARIANT", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "SIDELOAD_KEY", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "MASKED_AD_INPUT", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "MASKED_MSG_INPUT", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "NO_MSG", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "NO_AD", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 22}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name                                                 |
|:------:|:------:|:-------:|:-----------------------------------------------------|
| 31:10  |        |         | Reserved                                             |
|   9    |   rw   |   0x0   | [NO_AD](#ctrl_shadowed--no_ad)                       |
|   8    |   rw   |   0x0   | [NO_MSG](#ctrl_shadowed--no_msg)                     |
|   7    |   rw   |   0x0   | [MASKED_MSG_INPUT](#ctrl_shadowed--masked_msg_input) |
|   6    |   rw   |   0x0   | [MASKED_AD_INPUT](#ctrl_shadowed--masked_ad_input)   |
|   5    |   rw   |   0x0   | [SIDELOAD_KEY](#ctrl_shadowed--sideload_key)         |
|  4:3   |   rw   |   0x0   | [ASCON_VARIANT](#ctrl_shadowed--ascon_variant)       |
|  2:0   |   rw   |   0x0   | [OPERATION](#ctrl_shadowed--operation)               |

### CTRL_SHADOWED . NO_AD
There is no (1) associated data to be processed.
There is (0) associated data.

### CTRL_SHADOWED . NO_MSG
There is no (1) message (plaintext/ciphertext) to be processed.
There is (0) a message.

### CTRL_SHADOWED . MASKED_MSG_INPUT
Controls whether the message input is provided in shares (1) or not (0).
If the input is provided in shares all registers of both shares must be written for each input block.
If set to 0, the write operation tracking of Share 1 is disabled.
Software should set Share 1 to all zeros before the first block of the message is written to Share 0.
It does not need to be rewritten for each block.
Once all registers of Share 0 have been written, Ascon starts to process the data depending on the [`CTRL_AUX_SHADOWED.manual_start_trigger.`](#ctrl_aux_shadowed)

### CTRL_SHADOWED . MASKED_AD_INPUT
Controls whether the associated data input is provided in shares (1) or not (0).
If the input is provided in shares all registers of both shares must be written for each input block.
If set to 0, the write operation tracking of Share 1 is disabled.
Software should set Share 1 to all zeros before the first block of associated data is written to Share 0.
It does not need to be rewritten for each block.
Once all registers of Share 0 have been written, Ascon starts to process the data depending on the [`CTRL_AUX_SHADOWED.manual_start_trigger.`](#ctrl_aux_shadowed)

### CTRL_SHADOWED . SIDELOAD_KEY
Controls whether the Ascon unit uses the key provided by the key manager via key sideload interface (1)
or the key provided by software via Initial Key Registers KEY_SHARE1 and KEY_SHARE_0 (0).

### CTRL_SHADOWED . ASCON_VARIANT
Specifies which variant of Ascon is used.
It can be either Ascon-128 (2'b01) or Ascon-128a (2'b10).
They only differ in the input block size and the number of permutations per round.
The size of the key, nonce, tag is 128 bits for both variants.
This field is only relevant for encryption or decryption.
It is ignored for Ascon-XOF.

| Value   | Name       | Description                                                                                                                                                      |
|:--------|:-----------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0x1     | ASCON_128  | Ascon-128 is the primary choice. In this mode, the rate and thus the input block size is 64 bit. There are 6 rounds of permutation between different inputs.     |
| 0x2     | ASCON_128a | Ascon-128a is the secondary choice. In this mode, the rate and thus the input block size is 128 bit. There are 8 rounds of permutation between different inputs. |

Other values are reserved.

### CTRL_SHADOWED . OPERATION
Specifies which operation ascon should perform.
There are:
Enc, Dec, XOF (not implemented yet)
They are one-hot encoded

| Value   | Name      | Description                                                                                                     |
|:--------|:----------|:----------------------------------------------------------------------------------------------------------------|
| 0x1     | ASCON_ENC | 3'b001: Encryption. Invalid input values are mapped to this.                                                    |
| 0x2     | ASCON_DEC | 3'b010: Decryption.                                                                                             |
| 0x4     | ASCON_XOF | 3'b100: XOF. This mode is currently not supported and treated as an invalid input, that is mapped to ASCON_ENC. |

Other values are reserved.

## CTRL_AUX_SHADOWED
Auxiliary Control Register.
This register is shadowed, meaning two subsequent write operations are required to change its content.
If the two write operations try to set a different value, a recoverable alert is triggered (See Status Register).
A read operation clears the internal phase tracking: The next write operation is always considered a first write operation of an update sequence.
These configuration options are only used for special cases during development and can therefore be locked to the default values.
For normal operation these options should all be set to zero.
- Offset: `0x98`
- Reset default: `0x0`
- Reset mask: `0x3`
- Register enable: [`CTRL_AUX_REGWEN`](#ctrl_aux_regwen)

### Fields

```wavejson
{"reg": [{"name": "MANUAL_START_TRIGGER", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "FORCE_DATA_OVERWRITE", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                                                                                                                                                   |
|:------:|:------:|:-------:|:---------------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:2  |        |         |                      | Reserved                                                                                                                                                                                                                      |
|   1    |   rw   |   0x0   | FORCE_DATA_OVERWRITE | Control whether the Ascon unit is stalled during the last encryption/decryption cycle if the previous output data has not yet been read (0) or finishes the operation and overwrites the previous output data (1). Default: 0 |
|   0    |   rw   |   0x0   | MANUAL_START_TRIGGER | Control whether the Ascon unit should automatically start to encrypt/decrypt when it receives new input data (0) or wait for a separate trigger signal before starting (1) (see Trigger Register). Default: 0                 |

## CTRL_AUX_REGWEN
Lock bit for Auxiliary Control Register.
- Offset: `0x9c`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "CTRL_AUX_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name            | Description                                                                                                                                          |
|:------:|:------:|:-------:|:----------------|:-----------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                 | Reserved                                                                                                                                             |
|   0    |  rw0c  |   0x1   | CTRL_AUX_REGWEN | Auxiliary Control Register configuration enable bit. If this is cleared to 0, the Auxiliary Control Register cannot be written until the next reset. |

## BLOCK_CTRL_SHADOWED
Block Control Register.
This register is shadowed, meaning two subsequent write operations are required to change its content.
If the two write operations try to set a different value, a recoverable alert is triggered (See Status Register).
A read operation clears the internal phase tracking:
The next write operation is always considered a first write operation of an update sequence.
This register has to be written at least for each first and last block of message, associated data.
Intermediate blocks are expected to be of full block size.
If there's only one block of data, all three fields: valid_bytes, data_type_last and data_type_start must be set.
- Offset: `0xa0`
- Reset default: `0x1f000000`
- Reset mask: `0x1fffffff`

### Fields

```wavejson
{"reg": [{"name": "DATA_TYPE_START", "bits": 12, "attr": ["rw"], "rotate": 0}, {"name": "DATA_TYPE_LAST", "bits": 12, "attr": ["rw"], "rotate": 0}, {"name": "VALID_BYTES", "bits": 5, "attr": ["rw"], "rotate": -90}, {"bits": 3}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name            | Description                                                                                                                                                                                                                       |
|:------:|:------:|:-------:|:----------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:29  |        |         |                 | Reserved                                                                                                                                                                                                                          |
| 28:24  |   rw   |  0x1f   | VALID_BYTES     | Indicates the number of valid bytes [0 to 16] bytes. Default: 16 bytes for ASCON 128a Default:   8 bytes for ASCON 128                                                                                                            |
| 23:12  |   rw   |   0x0   | DATA_TYPE_LAST  | Specifies that the next read from an input is the last of its kind. There are: PT_IN, CT_IN, AD_IN. They are internally mubi4 encoded. Only one type is allowed to be true at the same time. NONE sets all mubi4 values to false. |
|  11:0  |   rw   |   0x0   | DATA_TYPE_START | Specifies which input the Ascon unit shall process next. There are: PT_IN, CT_IN, AD_IN. They are internally mubi4 encoded. Only one type is allowed to be true at the same time. NONE sets all mubi4 encoded values to False.    |

## TRIGGER
Trigger Register.
Each bit is individually cleared to zero when executing the corresponding trigger.
While executing any of the triggered operations, the Ascon unit will set the IDLE bit in the Status Register to zero.
The processor must check the Status Register before triggering further actions.
For example, writes to Initial Key and nonce Registers are ignored while the Ascon unit is busy.
Writes to the Message and associated data Registers are not ignored but the data will be cleared if a WIPE operation is pending.
- Offset: `0xa4`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "START", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "WIPE", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                                                        |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:2  |        |         |        | Reserved                                                                                                                                                                                                                           |
|   1    |   rw   |   0x0   | WIPE   | Performs a secure wipe of sensitive data.                                                                                                                                                                                          |
|   0    |   rw   |   0x0   | START  | If CTRL_SHADOWED_AUX.manual_start_trigger = 1: Keep Ascon unit paused (0) or trigger the authenticated encryption/decryption of one data block (1). If CTRL_SHADOWED_AUX.manual_start_trigger = 0: writes to this bit are ignored. |

## STATUS
Status Register
- Offset: `0xa8`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "IDLE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "STALL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "WAIT_EDN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ASCON_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ALERT_RECOV_CTRL_UPDATE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ALERT_RECOV_CTRL_AUX_UPDATE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ALERT_RECOV_BLOCK_CTRL_UPDATE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ALERT_FATAL_FAULT", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 350}}
```

|  Bits  |  Type  |  Reset  | Name                                                                            |
|:------:|:------:|:-------:|:--------------------------------------------------------------------------------|
|  31:8  |        |         | Reserved                                                                        |
|   7    |   ro   |   0x0   | [ALERT_FATAL_FAULT](#status--alert_fatal_fault)                                 |
|   6    |   ro   |   0x0   | [ALERT_RECOV_BLOCK_CTRL_UPDATE_ERR](#status--alert_recov_block_ctrl_update_err) |
|   5    |   ro   |   0x0   | [ALERT_RECOV_CTRL_AUX_UPDATE_ERR](#status--alert_recov_ctrl_aux_update_err)     |
|   4    |   ro   |   0x0   | [ALERT_RECOV_CTRL_UPDATE_ERR](#status--alert_recov_ctrl_update_err)             |
|   3    |   ro   |   0x0   | [ASCON_ERROR](#status--ascon_error)                                             |
|   2    |   ro   |   0x0   | [WAIT_EDN](#status--wait_edn)                                                   |
|   1    |   ro   |   0x0   | [STALL](#status--stall)                                                         |
|   0    |   ro   |   0x0   | [IDLE](#status--idle)                                                           |

### STATUS . ALERT_FATAL_FAULT
No fatal fault has occurred inside the Asconunit (0).
A fatal fault has occurred and the Ascon unit needs to be reset (1).
Examples for fatal faults include
i) storage errors in the Control Register,
ii) if any internal FSM enters an invalid state,
iii) if any sparsely encoded signal takes on an invalid value,
iv) errors in the internal round counter,
v) escalations triggered by the life cycle controller, and
vi) fatal integrity failures on the TL-UL bus.

### STATUS . ALERT_RECOV_BLOCK_CTRL_UPDATE_ERR
An update error has not occurred (0) or has occurred (1) in the shadowed block Control Register.
The register has to be rewritten.

### STATUS . ALERT_RECOV_CTRL_AUX_UPDATE_ERR
An update error has not occurred (0) or has occurred (1) in the shadowed Auxiliary Control Register.
The register has to be rewritten.

### STATUS . ALERT_RECOV_CTRL_UPDATE_ERR
An update error has not occurred (0) or has occurred (1) in the shadowed Control Register.
Ascon operation needs to be restarted by re-writing the Control Register.

### STATUS . ASCON_ERROR
An error due to a misconfiguration has happened.
The user should read out the error register for more information

### STATUS . WAIT_EDN
The Ascon unit is waiting for new entropy.

### STATUS . STALL
The Ascon unit is not stalled (0) or stalled (1) because there is previous
output data that must be read by the processor before the Ascon unit can
overwrite this data.

### STATUS . IDLE
The Ascon unit is idle (0) or busy (1).

## OUTPUT_VALID
Output Valid Register
This register specifies which output register contains valid data and should be read next.
It also contains the status information whether the TAG comparison was valid or not.
- Offset: `0xac`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "DATA_TYPE", "bits": 3, "attr": ["ro"], "rotate": -90}, {"name": "TAG_COMPARISON_VALID", "bits": 2, "attr": ["ro"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                                                                        |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                                                           |
|  4:3   |   ro   |   0x0   | TAG_COMPARISON_VALID | Indicates if the tag could be successfully compared 2'b01, or not 2'b10 2'b00 indicates that the tag hasn't been calculated, yet 2'b11 is invalid. |
|  2:0   |   ro   |   0x0   | DATA_TYPE            | Specifies which output type/register is valid. There are: PT_OUT, CT_OUT, TAG_OUT, NONE                                                            |

## FSM_STATE
Main FSM State register.
These registers can be used for debugging the internal state of ASCON's FSM.
The read can be blocked with the FSM_STATE_REGREN register
- Offset: `0xb0`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "MAIN_FSM", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                           |
|:------:|:------:|:-------:|:---------|:----------------------------------------------------------------------|
|  31:0  |   ro   |    x    | MAIN_FSM | These fields are directly mapped to the ASCON's main state registers. |

## FSM_STATE_REGREN
Lock bit for Auxiliary Control Register.
- Offset: `0xb4`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "FSM_STATE_REGREN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                                                                                                      |
|:------:|:------:|:-------:|:-----------------|:-------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                  | Reserved                                                                                                                                         |
|   0    |  rw0c  |   0x1   | FSM_STATE_REGREN | FSM_STATE register configuration enable bit. If this is cleared to 0, the FSM_STATE register returns all zeros on any read until the next reset. |

## ERROR
Error Register.
Error register for errors caused by user's misconfiguration.
To clear the error, a wipe must be triggered.
- Offset: `0xb8`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "NO_KEY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "NO_NONCE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "WRONG_ORDER", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FLAG_INPUT_MISSMATCH", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                            |
|:------:|:------:|:-------:|:---------------------|:-----------------------------------------------------------------------|
|  31:4  |        |         |                      | Reserved                                                               |
|   3    |   ro   |   0x0   | FLAG_INPUT_MISSMATCH | A flag for an empty input was set, but a non empty input was provided. |
|   2    |   ro   |   0x0   | WRONG_ORDER          | The ordering of associated data and message was wrong.                 |
|   1    |   ro   |   0x0   | NO_NONCE             | No Nonce was provided                                                  |
|   0    |   ro   |   0x0   | NO_KEY               | No Key was provided                                                    |
