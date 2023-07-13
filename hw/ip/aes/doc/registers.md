# Registers

The AES unit uses 8 and 2x4 separate write-only registers for the initial key, initialization vector, and input data, as well as 4 separate read-only registers for the output data.
All registers are little-endian.
Compared to first-in, first-out (FIFO) interfaces, having separate registers has a couple of advantages:

- Supported out-of-the-box by the register tool (the FIFO would have to be implemented separately).
- Usability: critical corner cases where software updates input data or the key partially only are easier to avoid using separate registers and the `hwqe`-signals provided by the Register Tool.
- Easier interaction with DMA engines

Also, using a FIFO interface for something that is not actually FIFO (internally, 16B of input/output data are consumed/produced at once) is less natural.

For a detailed overview of the register tool, please refer to the [Register Tool documentation.](../../../../util/reggen/README.md)

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/aes/data/aes.hjson -->
## Summary

| Name                                                    | Offset   |   Length | Description                              |
|:--------------------------------------------------------|:---------|---------:|:-----------------------------------------|
| aes.[`CIP_ID`](#cip_id)                                 | 0x0      |        4 | Comportable IP ID.                       |
| aes.[`REVISION`](#revision)                             | 0x4      |        4 | Comportable IP semantic version.         |
| aes.[`PARAMETER_BLOCK_TYPE`](#parameter_block_type)     | 0x8      |        4 | Parameter block type.                    |
| aes.[`PARAMETER_BLOCK_LENGTH`](#parameter_block_length) | 0xc      |        4 | Parameter block length.                  |
| aes.[`NEXT_PARAMETER_BLOCK`](#next_parameter_block)     | 0x10     |        4 | Next parameter block offset.             |
| aes.[`ALERT_TEST`](#alert_test)                         | 0x40     |        4 | Alert Test Register                      |
| aes.[`KEY_SHARE0_0`](#key_share0)                       | 0x44     |        4 | Initial Key Registers Share 0.           |
| aes.[`KEY_SHARE0_1`](#key_share0)                       | 0x48     |        4 | Initial Key Registers Share 0.           |
| aes.[`KEY_SHARE0_2`](#key_share0)                       | 0x4c     |        4 | Initial Key Registers Share 0.           |
| aes.[`KEY_SHARE0_3`](#key_share0)                       | 0x50     |        4 | Initial Key Registers Share 0.           |
| aes.[`KEY_SHARE0_4`](#key_share0)                       | 0x54     |        4 | Initial Key Registers Share 0.           |
| aes.[`KEY_SHARE0_5`](#key_share0)                       | 0x58     |        4 | Initial Key Registers Share 0.           |
| aes.[`KEY_SHARE0_6`](#key_share0)                       | 0x5c     |        4 | Initial Key Registers Share 0.           |
| aes.[`KEY_SHARE0_7`](#key_share0)                       | 0x60     |        4 | Initial Key Registers Share 0.           |
| aes.[`KEY_SHARE1_0`](#key_share1)                       | 0x64     |        4 | Initial Key Registers Share 1.           |
| aes.[`KEY_SHARE1_1`](#key_share1)                       | 0x68     |        4 | Initial Key Registers Share 1.           |
| aes.[`KEY_SHARE1_2`](#key_share1)                       | 0x6c     |        4 | Initial Key Registers Share 1.           |
| aes.[`KEY_SHARE1_3`](#key_share1)                       | 0x70     |        4 | Initial Key Registers Share 1.           |
| aes.[`KEY_SHARE1_4`](#key_share1)                       | 0x74     |        4 | Initial Key Registers Share 1.           |
| aes.[`KEY_SHARE1_5`](#key_share1)                       | 0x78     |        4 | Initial Key Registers Share 1.           |
| aes.[`KEY_SHARE1_6`](#key_share1)                       | 0x7c     |        4 | Initial Key Registers Share 1.           |
| aes.[`KEY_SHARE1_7`](#key_share1)                       | 0x80     |        4 | Initial Key Registers Share 1.           |
| aes.[`IV_0`](#iv)                                       | 0x84     |        4 | Initialization Vector Registers.         |
| aes.[`IV_1`](#iv)                                       | 0x88     |        4 | Initialization Vector Registers.         |
| aes.[`IV_2`](#iv)                                       | 0x8c     |        4 | Initialization Vector Registers.         |
| aes.[`IV_3`](#iv)                                       | 0x90     |        4 | Initialization Vector Registers.         |
| aes.[`DATA_IN_0`](#data_in)                             | 0x94     |        4 | Input Data Registers.                    |
| aes.[`DATA_IN_1`](#data_in)                             | 0x98     |        4 | Input Data Registers.                    |
| aes.[`DATA_IN_2`](#data_in)                             | 0x9c     |        4 | Input Data Registers.                    |
| aes.[`DATA_IN_3`](#data_in)                             | 0xa0     |        4 | Input Data Registers.                    |
| aes.[`DATA_OUT_0`](#data_out)                           | 0xa4     |        4 | Output Data Register.                    |
| aes.[`DATA_OUT_1`](#data_out)                           | 0xa8     |        4 | Output Data Register.                    |
| aes.[`DATA_OUT_2`](#data_out)                           | 0xac     |        4 | Output Data Register.                    |
| aes.[`DATA_OUT_3`](#data_out)                           | 0xb0     |        4 | Output Data Register.                    |
| aes.[`CTRL_SHADOWED`](#ctrl_shadowed)                   | 0xb4     |        4 | Control Register.                        |
| aes.[`CTRL_AUX_SHADOWED`](#ctrl_aux_shadowed)           | 0xb8     |        4 | Auxiliary Control Register.              |
| aes.[`CTRL_AUX_REGWEN`](#ctrl_aux_regwen)               | 0xbc     |        4 | Lock bit for Auxiliary Control Register. |
| aes.[`TRIGGER`](#trigger)                               | 0xc0     |        4 | Trigger Register.                        |
| aes.[`STATUS`](#status)                                 | 0xc4     |        4 | Status Register                          |

## CIP_ID
Comportable IP ID.
- Offset: `0x0`
- Reset default: `0x2`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "CIP_ID", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                       |
|:------:|:------:|:-------:|:-------|:--------------------------------------------------|
|  31:0  |   ro   |   0x2   | CIP_ID | This value is a unique comportable IP identifier. |

## REVISION
Comportable IP semantic version.
- Offset: `0x4`
- Reset default: `0x2000000`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "RESERVED", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "SUBMINOR", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "MINOR", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "MAJOR", "bits": 8, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                      |
|:------:|:------:|:-------:|:---------|:---------------------------------|
| 31:24  |   ro   |   0x2   | MAJOR    | Major version number.            |
| 23:16  |   ro   |   0x0   | MINOR    | Minor version number.            |
|  15:8  |   ro   |   0x0   | SUBMINOR | Subminor (patch) version number. |
|  7:0   |   ro   |   0x0   | RESERVED | Reserved version number.         |

## PARAMETER_BLOCK_TYPE
Parameter block type.
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "BLOCK_TYPE", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description           |
|:------:|:------:|:-------:|:-----------|:----------------------|
|  31:0  |   ro   |   0x0   | BLOCK_TYPE | Parameter block type. |

## PARAMETER_BLOCK_LENGTH
Parameter block length.
- Offset: `0xc`
- Reset default: `0xc`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "BLOCK_LENGTH", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                      |
|:------:|:------:|:-------:|:-------------|:---------------------------------|
|  31:0  |   ro   |   0xc   | BLOCK_LENGTH | Parameter block length in bytes. |

## NEXT_PARAMETER_BLOCK
Next parameter block offset.
- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "BLOCK_OFFSET", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                                                             |
|:------:|:------:|:-------:|:-------------|:----------------------------------------------------------------------------------------|
|  31:0  |   ro   |   0x0   | BLOCK_OFFSET | This offset value is zero if there is no other                         parameter block. |

## ALERT_TEST
Alert Test Register
- Offset: `0x40`
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
Loaded into the internal Full Key register upon starting encryption/decryption of the next block.
All key registers (Share 0 and Share 1) must be written at least once when the key is changed, regardless of key length (write random data for unused bits).
The order in which the registers are updated does not matter.
Can only be updated when the AES unit is idle.
If the AES unit is non-idle, writes to these registers are ignored.
Upon reset, these registers are cleared with pseudo-random data.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name         | Offset   |
|:-------------|:---------|
| KEY_SHARE0_0 | 0x44     |
| KEY_SHARE0_1 | 0x48     |
| KEY_SHARE0_2 | 0x4c     |
| KEY_SHARE0_3 | 0x50     |
| KEY_SHARE0_4 | 0x54     |
| KEY_SHARE0_5 | 0x58     |
| KEY_SHARE0_6 | 0x5c     |
| KEY_SHARE0_7 | 0x60     |


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
Loaded into the internal Full Key register upon starting encryption/decryption of the next block.
All key registers (Share 0 and Share 1) must be written at least once when the key is changed, regardless of key length (write random data for unused bits).
The order in which the registers are updated does not matter.
Can only be updated when the AES unit is idle.
If the AES unit is non-idle, writes to these registers are ignored.
Upon reset, these registers are cleared with pseudo-random data.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name         | Offset   |
|:-------------|:---------|
| KEY_SHARE1_0 | 0x64     |
| KEY_SHARE1_1 | 0x68     |
| KEY_SHARE1_2 | 0x6c     |
| KEY_SHARE1_3 | 0x70     |
| KEY_SHARE1_4 | 0x74     |
| KEY_SHARE1_5 | 0x78     |
| KEY_SHARE1_6 | 0x7c     |
| KEY_SHARE1_7 | 0x80     |


### Fields

```wavejson
{"reg": [{"name": "key_share1", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description         |
|:------:|:------:|:-------:|:-----------|:--------------------|
|  31:0  |   wo   |   0x0   | key_share1 | Initial Key Share 1 |

## IV
Initialization Vector Registers.

The initialization vector (IV) or initial counter value must be written to these registers when starting a new message in CBC or CTR mode (see Control Register), respectively.
In CBC and CTR modes, the AES unit does not start encryption/decryption with a partially updated IV.
Each register has to be written at least once.
The order in which the registers are written does not matter.
If the AES unit is non-idle, writes to these registers are ignored.
Whenever starting a new message, the corresponding IV value must be provided by the processor.
Once started, the AES unit automatically updates the contents of these registers.
In ECB mode, the IV registers are not used and do not need to be configured.
Upon reset, these registers are cleared with pseudo-random data.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name   | Offset   |
|:-------|:---------|
| IV_0   | 0x84     |
| IV_1   | 0x88     |
| IV_2   | 0x8c     |
| IV_3   | 0x90     |


### Fields

```wavejson
{"reg": [{"name": "iv", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description           |
|:------:|:------:|:-------:|:-------|:----------------------|
|  31:0  |   rw   |   0x0   | iv     | Initialization Vector |

## DATA_IN
Input Data Registers.

If MANUAL_OPERATION=0 (see Control Register), the AES unit automatically starts encryption/decryption after all Input Data registers have been written.
Each register has to be written at least once.
The order in which the registers are written does not matter.
Loaded into the internal State register upon starting encryption/decryption of the next block.
After that, the processor can update the Input Data registers (See INPUT_READY field of Status Register).
Upon reset, these registers are cleared with pseudo-random data.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name      | Offset   |
|:----------|:---------|
| DATA_IN_0 | 0x94     |
| DATA_IN_1 | 0x98     |
| DATA_IN_2 | 0x9c     |
| DATA_IN_3 | 0xa0     |


### Fields

```wavejson
{"reg": [{"name": "data_in", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name    | Description   |
|:------:|:------:|:-------:|:--------|:--------------|
|  31:0  |   wo   |   0x0   | data_in | Input Data    |

## DATA_OUT
Output Data Register.

Holds the output data produced by the AES unit during the last encryption/decryption operation.
If MANUAL_OPERATION=0 (see Control Register), the AES unit is stalled when the previous output data has not yet been read and is about to be overwritten.
Each register has to be read at least once.
The order in which the registers are read does not matter.
Upon reset, these registers are cleared with pseudo-random data.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name       | Offset   |
|:-----------|:---------|
| DATA_OUT_0 | 0xa4     |
| DATA_OUT_1 | 0xa8     |
| DATA_OUT_2 | 0xac     |
| DATA_OUT_3 | 0xb0     |


### Fields

```wavejson
{"reg": [{"name": "data_out", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description   |
|:------:|:------:|:-------:|:---------|:--------------|
|  31:0  |   ro   |   0x0   | data_out | Output Data   |

## CTRL_SHADOWED
Control Register.

Can only be updated when the AES unit is idle.
If the AES unit is non-idle, writes to this register are ignored.
This register is shadowed, meaning two subsequent write operations are required to change its content.
If the two write operations try to set a different value, a recoverable alert is triggered (See Status Register).
A read operation clears the internal phase tracking: The next write operation is always considered a first write operation of an update sequence.
Any write operation to this register will clear the status tracking required for automatic mode (See MANUAL_OPERATION field).
A write to the Control Register is considered the start of a new message.
Hence, software needs to provide new key, IV and input data afterwards.
- Offset: `0xb4`
- Reset default: `0x1181`
- Reset mask: `0xffff`

### Fields

```wavejson
{"reg": [{"name": "OPERATION", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "MODE", "bits": 6, "attr": ["rw"], "rotate": 0}, {"name": "KEY_LEN", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "SIDELOAD", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "PRNG_RESEED_RATE", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "MANUAL_OPERATION", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name                                                 |
|:------:|:------:|:-------:|:-----------------------------------------------------|
| 31:16  |        |         | Reserved                                             |
|   15   |   rw   |   0x0   | [MANUAL_OPERATION](#ctrl_shadowed--manual_operation) |
| 14:12  |   rw   |   0x1   | [PRNG_RESEED_RATE](#ctrl_shadowed--prng_reseed_rate) |
|   11   |   rw   |   0x0   | [SIDELOAD](#ctrl_shadowed--sideload)                 |
|  10:8  |   rw   |   0x1   | [KEY_LEN](#ctrl_shadowed--key_len)                   |
|  7:2   |   rw   |  0x20   | [MODE](#ctrl_shadowed--mode)                         |
|  1:0   |   rw   |   0x1   | [OPERATION](#ctrl_shadowed--operation)               |

### CTRL_SHADOWED . MANUAL_OPERATION
Controls whether the AES unit is operated in normal/automatic mode (0) or fully manual mode (1).
In automatic mode (0), the AES unit automatically i) starts to encrypt/decrypt when it receives new input data, and ii) stalls during the last encryption/decryption cycle if the previous output data has not yet been read.
This is the most efficient mode to operate in.
Note that the corresponding status tracking is automatically cleared upon a write to the Control Register.
In manual mode (1), the AES unit i) only starts to encrypt/decrypt after receiving a start trigger (see Trigger Register), and ii) overwrites previous output data irrespective of whether it has been read out or not.
This mode is useful if software needs full control over the AES unit.

### CTRL_SHADOWED . PRNG_RESEED_RATE
3-bit one-hot field to control the reseeding rate of the internal pseudo-random number generator (PRNG) used for masking.
Invalid input values, i.e., values with multiple bits set and value 3'b000 are mapped to the highest reseeding rate PER_1 (3'b001).

| Value   | Name   | Description                                                                                                                                                                                                             |
|:--------|:-------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0x1     | PER_1  | 3'b001: Reseed the masking PRNG once per block. Invalid input values, i.e., values with multiple bits set and value 3'b000 are mapped to PER_1 (3'b001). This results in a max entropy consumption rate of ~286 Mbit/s. |
| 0x2     | PER_64 | 3'b010: Reseed the masking PRNG approximately once per every 64 blocks. This results in a max entropy consumption rate of ~4.5 Mbit/s.                                                                                  |
| 0x4     | PER_8K | 3'b100: Reseed the masking PRNG approximately once per every 8192 blocks. This results in an max entropy consumption rate of ~0.035 Mbit/s.                                                                             |

Other values are reserved.

### CTRL_SHADOWED . SIDELOAD
Controls whether the AES unit uses the key provided by the key manager via key sideload interface (1) or the key provided by software via Initial Key Registers KEY_SHARE1_0 - KEY_SHARE1_7 (0).

### CTRL_SHADOWED . KEY_LEN
3-bit one-hot field to select AES key length.
Invalid input values, i.e., values with multiple bits set, value 3'b000, and value 3'b010 in case 192-bit keys are not supported (because disabled at compile time) are mapped to AES_256 (3'b100).

| Value   | Name    | Description                                                                                                                                                                                                            |
|:--------|:--------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0x1     | AES_128 | 3'b001: 128-bit key length.                                                                                                                                                                                            |
| 0x2     | AES_192 | 3'b010: 192-bit key length. In case support for 192-bit keys has been disabled at compile time, setting this value results in configuring AES_256 (3'b100).                                                            |
| 0x4     | AES_256 | 3'b100: 256-bit key length. Invalid input values, i.e., values with multiple bits set, value 3'b000, and value 3'b010 in case 192-bit keys are not supported (because disabled at compile time) are mapped to AES_256. |

Other values are reserved.

### CTRL_SHADOWED . MODE
6-bit one-hot field to select AES block cipher mode.
Invalid input values, i.e., values with multiple bits set and value 6'b00_0000, are mapped to AES_NONE (6'b10_0000).

| Value   | Name     | Description                                                                                                        |
|:--------|:---------|:-------------------------------------------------------------------------------------------------------------------|
| 0x01    | AES_ECB  | 6'b00_0001: Electronic Codebook (ECB) mode.                                                                        |
| 0x02    | AES_CBC  | 6'b00_0010: Cipher Block Chaining (CBC) mode.                                                                      |
| 0x04    | AES_CFB  | 6'b00_0100: Cipher Feedback (CFB) mode.                                                                            |
| 0x08    | AES_OFB  | 6'b00_1000: Output Feedback (OFB) mode.                                                                            |
| 0x10    | AES_CTR  | 6'b01_0000: Counter (CTR) mode.                                                                                    |
| 0x20    | AES_NONE | 6'b10_0000: Invalid input values, i.e., value with multiple bits set and value 6'b00_0000, are mapped to AES_NONE. |

Other values are reserved.

### CTRL_SHADOWED . OPERATION
2-bit one-hot field to select the operation of AES unit.
Invalid input values, i.e., values with multiple bits set and value 2'b00, are mapped to AES_ENC (2'b01).

| Value   | Name    | Description                                                                            |
|:--------|:--------|:---------------------------------------------------------------------------------------|
| 0x1     | AES_ENC | 2'b01: Encryption. Invalid input values, i.e., 2'b00 and 2'b11, are mapped to AES_ENC. |
| 0x2     | AES_DEC | 2'b10: Decryption.                                                                     |

Other values are reserved.

## CTRL_AUX_SHADOWED
Auxiliary Control Register.

This register is shadowed, meaning two subsequent write operations are required to change its content.
If the two write operations try to set a different value, a recoverable alert is triggered (See Status Register).
A read operation clears the internal phase tracking: The next write operation is always considered a first write operation of an update sequence.
- Offset: `0xb8`
- Reset default: `0x1`
- Reset mask: `0x3`
- Register enable: [`CTRL_AUX_REGWEN`](#ctrl_aux_regwen)

### Fields

```wavejson
{"reg": [{"name": "KEY_TOUCH_FORCES_RESEED", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "FORCE_MASKS", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 250}}
```

|  Bits  |  Type  |  Reset  | Name                                                                   |
|:------:|:------:|:-------:|:-----------------------------------------------------------------------|
|  31:2  |        |         | Reserved                                                               |
|   1    |   rw   |   0x0   | [FORCE_MASKS](#ctrl_aux_shadowed--force_masks)                         |
|   0    |   rw   |   0x1   | [KEY_TOUCH_FORCES_RESEED](#ctrl_aux_shadowed--key_touch_forces_reseed) |

### CTRL_AUX_SHADOWED . FORCE_MASKS
Allow the internal masking PRNG to advance (0) or force its internal state (1) leading to constant masks.
Setting all masks to constant value can be useful when performing SCA.
To completely disable the masking, the second key share (KEY_SHARE1_0 - KEY_SHARE1_7) must be zero as well.
In addition, a special seed needs to be loaded into the masking PRNG using the EDN interface.
Only applicable if both the Masking parameter and the SecAllowForcingMasks parameter are set to one.

### CTRL_AUX_SHADOWED . KEY_TOUCH_FORCES_RESEED
Controls whether providing a new key triggers the reseeding of internal pseudo-random number generators used for clearing and masking (1) or not (0).

## CTRL_AUX_REGWEN
Lock bit for Auxiliary Control Register.
- Offset: `0xbc`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "CTRL_AUX_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name            | Description                                                                                                                             |
|:------:|:------:|:-------:|:----------------|:----------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                 | Reserved                                                                                                                                |
|   0    |  rw0c  |   0x1   | CTRL_AUX_REGWEN | Auxiliary Control Register configuration enable bit. If this is cleared to 0, the Auxiliary Control Register cannot be written anymore. |

## TRIGGER
Trigger Register.

Each bit is individually cleared to zero when executing the corresponding trigger.
While executing any of the triggered operations, the AES unit will set the IDLE bit in the Status Register to zero.
The processor must check the Status Register before triggering further actions.
For example, writes to Initial Key and IV Registers are ignored while the AES unit is busy.
Writes to the Input Data Registers are not ignored but the data will be cleared if a KEY_IV_DATA_IN_CLEAR operation is pending.
- Offset: `0xc0`
- Reset default: `0xe`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "START", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "KEY_IV_DATA_IN_CLEAR", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "DATA_OUT_CLEAR", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "PRNG_RESEED", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                                                   |
|:------:|:------:|:-------:|:-------------------------------------------------------|
|  31:4  |        |         | Reserved                                               |
|   3    |   wo   |   0x1   | [PRNG_RESEED](#trigger--prng_reseed)                   |
|   2    |   wo   |   0x1   | [DATA_OUT_CLEAR](#trigger--data_out_clear)             |
|   1    |   wo   |   0x1   | [KEY_IV_DATA_IN_CLEAR](#trigger--key_iv_data_in_clear) |
|   0    |   wo   |   0x0   | [START](#trigger--start)                               |

### TRIGGER . PRNG_RESEED
Keep continuing with the current states of the internal pseudo-random number generators used for register clearing and masking (0) or perform a reseed of the internal states from the connected entropy source (1).
If the KEY_TOUCH_FORCES_RESEED bit in the Auxiliary Control Register is set to one, this trigger will automatically get set after providing a new initial key.

### TRIGGER . DATA_OUT_CLEAR
Keep current values in Output Data registers (0) or clear those registers with pseudo-random data (1).

### TRIGGER . KEY_IV_DATA_IN_CLEAR
Keep current values in Initial Key, internal Full Key and Decryption Key registers, IV registers and Input Data registers (0) or clear all those registers with pseudo-random data (1).

### TRIGGER . START
Keep AES unit paused (0) or trigger the encryption/decryption of one data block (1).
This trigger is cleared to `0` if MANUAL_OPERATION=0 or if MODE=AES_NONE (see Control Register).

## STATUS
Status Register
- Offset: `0xc4`
- Reset default: `0x0`
- Reset mask: `0x7f`

### Fields

```wavejson
{"reg": [{"name": "IDLE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "STALL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "OUTPUT_LOST", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "OUTPUT_VALID", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "INPUT_READY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ALERT_RECOV_CTRL_UPDATE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ALERT_FATAL_FAULT", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 25}], "config": {"lanes": 1, "fontsize": 10, "vspace": 290}}
```

|  Bits  |  Type  |  Reset  | Name                                                                |
|:------:|:------:|:-------:|:--------------------------------------------------------------------|
|  31:7  |        |         | Reserved                                                            |
|   6    |   ro   |   0x0   | [ALERT_FATAL_FAULT](#status--alert_fatal_fault)                     |
|   5    |   ro   |   0x0   | [ALERT_RECOV_CTRL_UPDATE_ERR](#status--alert_recov_ctrl_update_err) |
|   4    |   ro   |   0x0   | [INPUT_READY](#status--input_ready)                                 |
|   3    |   ro   |   0x0   | [OUTPUT_VALID](#status--output_valid)                               |
|   2    |   ro   |   0x0   | [OUTPUT_LOST](#status--output_lost)                                 |
|   1    |   ro   |   0x0   | [STALL](#status--stall)                                             |
|   0    |   ro   |   0x0   | [IDLE](#status--idle)                                               |

### STATUS . ALERT_FATAL_FAULT
No fatal fault has occurred inside the AES unit (0).
A fatal fault has occurred and the AES unit needs to be reset (1).
Examples for fatal faults include
i) storage errors in the Control Register,
ii) if any internal FSM enters an invalid state,
iii) if any sparsely encoded signal takes on an invalid value,
iv) errors in the internal round counter,
v) escalations triggered by the life cycle controller, and
vi) fatal integrity failures on the TL-UL bus.

### STATUS . ALERT_RECOV_CTRL_UPDATE_ERR
An update error has not occurred (0) or has occurred (1) in the shadowed Control Register.
AES operation needs to be restarted by re-writing the Control Register.

### STATUS . INPUT_READY
The AES unit is ready (1) or not ready (0) to receive new data input via the DATA_IN registers.
If the present values in the DATA_IN registers have not yet been loaded into the
module this flag is `0` (not ready).

### STATUS . OUTPUT_VALID
The AES unit has no valid output (0) or has valid output data (1).

### STATUS . OUTPUT_LOST
All previous output data has been fully read by the processor (0) or at least one previous output data block has been lost (1).
It has been overwritten by the AES unit before the processor could fully read it.
Once set to `1`, this flag remains set until AES operation is restarted by re-writing the Control Register.
The primary use of this flag is for design verification.
This flag is not meaningful if MANUAL_OPERATION=0 (see Control Register).

### STATUS . STALL
The AES unit is not stalled (0) or stalled (1) because there is previous
output data that must be read by the processor before the AES unit can
overwrite this data.
This flag is not meaningful if MANUAL_OPERATION=1 (see Control Register).

### STATUS . IDLE
The AES unit is idle (1) or busy (0).
This flag is `0` if one of the following operations is currently running: i) encryption/decryption, ii) register clearing or iii) PRNG reseeding.
This flag is also `0` if an encryption/decryption is running but the AES unit is stalled.


<!-- END CMDGEN -->
