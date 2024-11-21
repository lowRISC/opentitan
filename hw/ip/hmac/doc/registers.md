# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/hmac/data/hmac.hjson -->
## Summary

| Name                                         | Offset   |   Length | Description                                                    |
|:---------------------------------------------|:---------|---------:|:---------------------------------------------------------------|
| hmac.[`INTR_STATE`](#intr_state)             | 0x0      |        4 | Interrupt State Register                                       |
| hmac.[`INTR_ENABLE`](#intr_enable)           | 0x4      |        4 | Interrupt Enable Register                                      |
| hmac.[`INTR_TEST`](#intr_test)               | 0x8      |        4 | Interrupt Test Register                                        |
| hmac.[`ALERT_TEST`](#alert_test)             | 0xc      |        4 | Alert Test Register                                            |
| hmac.[`CFG`](#cfg)                           | 0x10     |        4 | HMAC Configuration register.                                   |
| hmac.[`CMD`](#cmd)                           | 0x14     |        4 | HMAC command register                                          |
| hmac.[`STATUS`](#status)                     | 0x18     |        4 | HMAC Status register                                           |
| hmac.[`ERR_CODE`](#err_code)                 | 0x1c     |        4 | HMAC Error Code                                                |
| hmac.[`WIPE_SECRET`](#wipe_secret)           | 0x20     |        4 | Clear internal secret registers.                               |
| hmac.[`KEY_0`](#key)                         | 0x24     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_1`](#key)                         | 0x28     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_2`](#key)                         | 0x2c     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_3`](#key)                         | 0x30     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_4`](#key)                         | 0x34     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_5`](#key)                         | 0x38     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_6`](#key)                         | 0x3c     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_7`](#key)                         | 0x40     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_8`](#key)                         | 0x44     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_9`](#key)                         | 0x48     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_10`](#key)                        | 0x4c     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_11`](#key)                        | 0x50     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_12`](#key)                        | 0x54     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_13`](#key)                        | 0x58     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_14`](#key)                        | 0x5c     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_15`](#key)                        | 0x60     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_16`](#key)                        | 0x64     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_17`](#key)                        | 0x68     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_18`](#key)                        | 0x6c     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_19`](#key)                        | 0x70     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_20`](#key)                        | 0x74     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_21`](#key)                        | 0x78     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_22`](#key)                        | 0x7c     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_23`](#key)                        | 0x80     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_24`](#key)                        | 0x84     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_25`](#key)                        | 0x88     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_26`](#key)                        | 0x8c     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_27`](#key)                        | 0x90     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_28`](#key)                        | 0x94     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_29`](#key)                        | 0x98     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_30`](#key)                        | 0x9c     |        4 | HMAC Secret Key                                                |
| hmac.[`KEY_31`](#key)                        | 0xa0     |        4 | HMAC Secret Key                                                |
| hmac.[`DIGEST_0`](#digest)                   | 0xa4     |        4 | Digest output.                                                 |
| hmac.[`DIGEST_1`](#digest)                   | 0xa8     |        4 | Digest output.                                                 |
| hmac.[`DIGEST_2`](#digest)                   | 0xac     |        4 | Digest output.                                                 |
| hmac.[`DIGEST_3`](#digest)                   | 0xb0     |        4 | Digest output.                                                 |
| hmac.[`DIGEST_4`](#digest)                   | 0xb4     |        4 | Digest output.                                                 |
| hmac.[`DIGEST_5`](#digest)                   | 0xb8     |        4 | Digest output.                                                 |
| hmac.[`DIGEST_6`](#digest)                   | 0xbc     |        4 | Digest output.                                                 |
| hmac.[`DIGEST_7`](#digest)                   | 0xc0     |        4 | Digest output.                                                 |
| hmac.[`DIGEST_8`](#digest)                   | 0xc4     |        4 | Digest output.                                                 |
| hmac.[`DIGEST_9`](#digest)                   | 0xc8     |        4 | Digest output.                                                 |
| hmac.[`DIGEST_10`](#digest)                  | 0xcc     |        4 | Digest output.                                                 |
| hmac.[`DIGEST_11`](#digest)                  | 0xd0     |        4 | Digest output.                                                 |
| hmac.[`DIGEST_12`](#digest)                  | 0xd4     |        4 | Digest output.                                                 |
| hmac.[`DIGEST_13`](#digest)                  | 0xd8     |        4 | Digest output.                                                 |
| hmac.[`DIGEST_14`](#digest)                  | 0xdc     |        4 | Digest output.                                                 |
| hmac.[`DIGEST_15`](#digest)                  | 0xe0     |        4 | Digest output.                                                 |
| hmac.[`MSG_LENGTH_LOWER`](#msg_length_lower) | 0xe4     |        4 | Received Message Length calculated by the HMAC in bits [31:0]  |
| hmac.[`MSG_LENGTH_UPPER`](#msg_length_upper) | 0xe8     |        4 | Received Message Length calculated by the HMAC in bits [63:32] |
| hmac.[`MSG_FIFO`](#msg_fifo)                 | 0x1000   |     4096 | <!-- imp_hmac_0015 begin -->                                   |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "hmac_done", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "fifo_empty", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "hmac_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name                                  |
|:------:|:------:|:-------:|:--------------------------------------|
|  31:3  |        |         | Reserved                              |
|   2    |  rw1c  |   0x0   | [hmac_err](#intr_state--hmac_err)     |
|   1    |   ro   |   0x0   | [fifo_empty](#intr_state--fifo_empty) |
|   0    |  rw1c  |   0x0   | [hmac_done](#intr_state--hmac_done)   |

### INTR_STATE . hmac_err
<!-- req_hmac_0019 begin -->
HMAC error has occurred. ERR_CODE register shows which error occurred.
<!-- req_hmac_0019 end -->

### INTR_STATE . fifo_empty
The message FIFO is empty.
<!-- req_hmac_001A begin -->
This interrupt is raised only if the message FIFO is actually writable by software, i.e., if all of the following conditions are met:
i) The HMAC block is not running in HMAC mode and performing the second round of computing the final hash of the outer key as well as the result of the first round using the inner key.
ii) Software has not yet written the Process or Stop command to finish the hashing operation.
For the interrupt to be raised, the message FIFO must also have been full previously.
<!-- req_hmac_001A end -->
Otherwise, the hardware empties the FIFO faster than software can fill it and there is no point in interrupting the software to inform it about the message FIFO being empty.

### INTR_STATE . hmac_done
<!-- req_hmac_0008 begin -->
HMAC/SHA-2 has completed.
<!-- req_hmac_0008 end -->

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "hmac_done", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "fifo_empty", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "hmac_err", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                          |
|:------:|:------:|:-------:|:-----------|:---------------------------------------------------------------------|
|  31:3  |        |         |            | Reserved                                                             |
|   2    |   rw   |   0x0   | hmac_err   | Enable interrupt when [`INTR_STATE.hmac_err`](#intr_state) is set.   |
|   1    |   rw   |   0x0   | fifo_empty | Enable interrupt when [`INTR_STATE.fifo_empty`](#intr_state) is set. |
|   0    |   rw   |   0x0   | hmac_done  | Enable interrupt when [`INTR_STATE.hmac_done`](#intr_state) is set.  |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "hmac_done", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fifo_empty", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "hmac_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                   |
|:------:|:------:|:-------:|:-----------|:--------------------------------------------------------------|
|  31:3  |        |         |            | Reserved                                                      |
|   2    |   wo   |   0x0   | hmac_err   | Write 1 to force [`INTR_STATE.hmac_err`](#intr_state) to 1.   |
|   1    |   wo   |   0x0   | fifo_empty | Write 1 to force [`INTR_STATE.fifo_empty`](#intr_state) to 1. |
|   0    |   wo   |   0x0   | hmac_done  | Write 1 to force [`INTR_STATE.hmac_done`](#intr_state) to 1.  |

## ALERT_TEST
Alert Test Register
- Offset: `0xc`
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

## CFG
HMAC Configuration register.

<!-- req_hmac_0038 begin -->
The register is updated when the engine is in Idle.
If the software updates the register while the engine computes the hash, the updated value is discarded.
<!-- req_hmac_0038 end -->
- Offset: `0x10`
- Reset default: `0x4100`
- Reset mask: `0x7fff`

### Fields

```wavejson
{"reg": [{"name": "hmac_en", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "sha_en", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endian_swap", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "digest_swap", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key_swap", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "digest_size", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "key_length", "bits": 6, "attr": ["rw"], "rotate": 0}, {"bits": 17}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name                             |
|:------:|:------:|:-------:|:---------------------------------|
| 31:15  |        |         | Reserved                         |
|  14:9  |   rw   |  0x20   | [key_length](#cfg--key_length)   |
|  8:5   |   rw   |   0x8   | [digest_size](#cfg--digest_size) |
|   4    |   rw   |   0x0   | [key_swap](#cfg--key_swap)       |
|   3    |   rw   |   0x0   | [digest_swap](#cfg--digest_swap) |
|   2    |   rw   |   0x0   | [endian_swap](#cfg--endian_swap) |
|   1    |   rw   |    x    | [sha_en](#cfg--sha_en)           |
|   0    |   rw   |    x    | [hmac_en](#cfg--hmac_en)         |

### CFG . key_length
Key length configuration.

<!-- req_hmac_0027 begin -->
This is a 6-bit one-hot encoded field to configure the key length for HMAC.
<!-- req_hmac_0027 end -->

<!-- req_hmac_0016 begin -->
The HMAC can be programmed with the following key lengths: 128-bit, 256-bit, 384-bit, 512-bit and 1024-bit.
But the HMAC supports any arbitrary key length: the software should configure the HMAC with the next largest supported key length and concatenate zeros to reach the programmed key length.
<!-- req_hmac_0016 end -->
The position of these zeros depends on the endianness, thus on the programmed [`CFG.key_swap`](registers.md#cfg--key_swap).
For example, for an 80-bit key, HMAC should be configured with an 128-bit key length, fed with the 80-bit key and with 48 zero-bits.

Note that the key length cannot be greater than the block size: up to 1024-bit for SHA-2 384/512 and up to 512-bit for SHA-2 256.
<!-- imp_hmac_0008 begin -->
The value of this register is irrelevant when only SHA-2 (not keyed HMAC) is configured.
<!-- imp_hmac_0008 end -->
<!-- req_hmac_0020 begin -->
However, for HMAC mode (`hmac_en == 1`), when HMAC is triggered to start while [`KEY_LENGTH`](#key_length) holds `Key_None` or [`KEY_LENGTH`](#key_length) holds `Key_1024` for [`DIGEST_SIZE`](#digest_size) = `SHA2_256`, starting is blocked and an error is signalled to SW.
<!-- req_hmac_0020 end -->

| Value   | Name     | Description                                                                                                                                                                                                                                                                                                                                                                                                                          |
|:--------|:---------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0x01    | Key_128  | 6'b00_0001: 128-bit secret key.                                                                                                                                                                                                                                                                                                                                                                                                      |
| 0x02    | Key_256  | 6'b00_0010: 256-bit secret key.                                                                                                                                                                                                                                                                                                                                                                                                      |
| 0x04    | Key_384  | 6'b00_0100: 384-bit secret key.                                                                                                                                                                                                                                                                                                                                                                                                      |
| 0x08    | Key_512  | 6'b00_1000: 512-bit secret key.                                                                                                                                                                                                                                                                                                                                                                                                      |
| 0x10    | Key_1024 | 6'b01_0000: 1024-bit secret key.                                                                                                                                                                                                                                                                                                                                                                                                     |
| 0x20    | Key_None | <!-- req_hmac_0021 begin --> 6'b10_0000: Unsupported/invalid values and all-zero values are mapped to Key_None. <!-- req_hmac_0021 end --> With this value, when HMAC is triggered to start operation (via `hash_start` or `hash_continue`), it will be blocked from starting and an error is signalled to the SW. If only unkeyed SHA-2 is configured (`hmac_en == 0`), starting is not blocked, since this does not require a key. |

Other values are reserved.

### CFG . digest_size
Digest size configuration.
<!-- req_hmac_0028 begin -->
This is a 4-bit one-hot encoded field to select digest size.
<!-- req_hmac_0028 end -->
<!-- imp_hmac_0007 begin -->
This field is either used in HMAC mode and in SHA-2 standalone mode.
<!-- imp_hmac_0007 end -->
Invalid/unsupported values, i.e., values that don't correspond to SHA2_256, SHA2_384, or SHA2_512, are mapped to SHA2_None.

| Value   | Name      | Description                                                                                                                                                                                                                                                                                                            |
|:--------|:----------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0x1     | SHA2_256  | 4'b0001: SHA-2 256 digest.                                                                                                                                                                                                                                                                                             |
| 0x2     | SHA2_384  | 4'b0010: SHA-2 384 digest.                                                                                                                                                                                                                                                                                             |
| 0x4     | SHA2_512  | 4'b0100: SHA-2 512 digest.                                                                                                                                                                                                                                                                                             |
| 0x8     | SHA2_None | <!-- req_hmac_002A begin --> 4'b1000: Unsupported/invalid values and all-zero values are mapped to SHA2_None. <!-- req_hmac_002A end --> With this value, when HMAC/SHA-2 is triggered to start operation (via `hash_start` or `hash_continue`), it will be blocked from starting and an error is signalled to the SW. |

Other values are reserved.

### CFG . key_swap
Key register byte swap.

<!-- req_hmac_002B begin -->
If 1 the endianness of each KEY_* register is swapped. Default value (value 0) is big endian representation of the KEY_* CSRs.
<!-- req_hmac_002B end -->

### CFG . digest_swap
Digest register byte swap.

<!-- req_hmac_002C begin -->
If 1 the value in each digest output register is converted to big-endian byte order.
<!-- req_hmac_002C end -->
This setting does not affect the order of the digest output registers, [`DIGEST_0`](#digest_0) still contains the first 4 bytes of the digest.

### CFG . endian_swap
Endian swap.

<!-- req_hmac_002D begin -->
If 0, each value will be added to the message in little-endian byte order.
The value is written to MSG_FIFO same to the SW writes.
If 1, then each individual multi-byte value, regardless of its alignment, written to [`MSG_FIFO`](#msg_fifo) will be added to the message in big-endian byte order.
<!-- req_hmac_002D end -->
<!-- req_hmac_002F begin -->
A message written to [`MSG_FIFO`](#msg_fifo) one byte at a time will not be affected by this setting.
<!-- req_hmac_002F end -->
From a hardware perspective byte swaps are performed on a TL-UL word granularity.

### CFG . sha_en
SHA-2 enable.

 <!-- req_hmac_0030 begin -->
 If 0, the SHA engine will not initiate compression, this is used to stop operation of the SHA-2 engine until configuration has been done.
 <!-- req_hmac_0030 end -->
 <!-- req_hmac_0031 begin -->
 When the SHA-2 engine is disabled the digest is cleared, and the digest can be written to from SW which enables restoring context (to support context switching).
 <!-- req_hmac_0031 end -->
 

### CFG . hmac_en
<!-- req_hmac_0002 begin -->
HMAC datapath enable.
<!-- req_hmac_0002 end -->

<!-- imp_hmac_000F begin -->
If this bit is 1, HMAC operates when `hash_start` toggles.
<!-- imp_hmac_000F end -->

## CMD
HMAC command register
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "hash_start", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"name": "hash_process", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"name": "hash_stop", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"name": "hash_continue", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name                                 |
|:------:|:------:|:-------:|:-------------------------------------|
|  31:4  |        |         | Reserved                             |
|   3    | r0w1c  |    x    | [hash_continue](#cmd--hash_continue) |
|   2    | r0w1c  |    x    | [hash_stop](#cmd--hash_stop)         |
|   1    | r0w1c  |    x    | [hash_process](#cmd--hash_process)   |
|   0    | r0w1c  |    x    | [hash_start](#cmd--hash_start)       |

### CMD . hash_continue
<!-- imp_hmac_0010 begin -->
When 1 is written to this field, SHA-2 or HMAC will continue hashing based on the current hash in the digest registers and the message length, which both have to be restored to switch context.
<!-- imp_hmac_0010 end -->

### CMD . hash_stop
<!-- req_hmac_0008 begin -->
When 1 is written to this field, SHA-2 or HMAC will afterwards set the `hmac_done` interrupt as soon as the current block has been hashed.
<!-- req_hmac_0008 end -->
<!-- imp_hmac_0011 begin -->
The hash can then be read from the registers [`DIGEST_0`](#digest_0) to [`DIGEST_15.`](#digest_15)
<!-- imp_hmac_0011 end -->
Together with the message length in [`MSG_LENGTH_LOWER`](#msg_length_lower) and [`MSG_LENGTH_UPPER`](#msg_length_upper), this forms the information that has to be saved before switching context.

### CMD . hash_process
<!-- imp_hmac_0012 begin -->
If 1 is written to this field, SHA-2 or HMAC calculates the digest or signing based on currently received message.
<!-- imp_hmac_0012 end -->

### CMD . hash_start
If 1 is written into this field, SHA-2 or HMAC begins its operation.
CPU must configure relative information first, such as the digest size, secret key and the key length.

## STATUS
HMAC Status register
- Offset: `0x18`
- Reset default: `0x3`
- Reset mask: `0x3f7`

### Fields

```wavejson
{"reg": [{"name": "hmac_idle", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "fifo_empty", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "fifo_full", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 1}, {"name": "fifo_depth", "bits": 6, "attr": ["ro"], "rotate": 0}, {"bits": 22}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                                                                                                                                                                                        |
|:------:|:------:|:-------:|:-----------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:10  |        |         |            | Reserved                                                                                                                                                                                                                           |
|  9:4   |   ro   |    x    | fifo_depth | <!-- req_hmac_0036 begin --> FIFO entry count. <!-- req_hmac_0036 end --> <!-- req_hmac_0006 begin --> <!-- FIFO depth register field should be 6 bits width as the message FIFO has a depth of 32. --> <!-- req_hmac_0006 end --> |
|   3    |        |         |            | Reserved                                                                                                                                                                                                                           |
|   2    |   ro   |    x    | fifo_full  | <!-- req_hmac_0035 begin --> FIFO full. <!-- req_hmac_0035 end --> Data written to the FIFO whilst it is full will cause back-pressure on the interconnect                                                                         |
|   1    |   ro   |   0x1   | fifo_empty | <!-- req_hmac_0034 begin --> FIFO empty <!-- req_hmac_0034 end -->                                                                                                                                                                 |
|   0    |   ro   |   0x1   | hmac_idle  | <!-- req_hmac_0033 begin --> HMAC idle status. <!-- req_hmac_0033 end -->                                                                                                                                                          |

## ERR_CODE
HMAC Error Code
- Offset: `0x1c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "err_code", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                                                                                                                                                                      |
|:------:|:------:|:-------:|:---------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   ro   |   0x0   | err_code | <!-- req_hmac_0037 begin --> If an error interrupt occurs, this register has information of error cause. <!-- req_hmac_0037 end --> Please take a look at `hw/ip/prim/rtl/prim_sha2_pkg.sv:err_code_e enum type. |

## WIPE_SECRET
Clear internal secret registers.

<!-- req_hmac_000A begin -->
If CPU writes a value into the register, the value is used to clear the internal variables such as the secret key, internal state machine, or hash value.
The clear secret operation overwrites the internal variables with the provided 32-bit value.
For SHA-2 384/512 that work with 64-bit words, the 32-bit value is duplicated and concatenated to generate the 64-bit value.
<!-- req_hmac_000A end -->
It is recommended to use a value extracted from an entropy source.
- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "secret", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:0  |   wo   |    x    | secret | Secret value  |

## KEY
HMAC Secret Key

HMAC using SHA-2 256/384/512 assumes any hashed secret key length up to the block size, thus capped at 1024-bit.
[`key_length`](#key_length) determines how many of these registers are relevant for the HMAC operation.
<!-- imp_hmac_0013 begin -->
Order of the secret key is:
key[1023:0] = {KEY0, KEY1, KEY2, ... , KEY31};
<!-- imp_hmac_0013 end -->

<!-- req_hmac_0039 begin -->
The registers are allowed to be updated only when the engine is in Idle state.
If the engine computes the hash, it discards any attempts to update the secret keys and report an error.
<!-- req_hmac_0039 end -->
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name   | Offset   |
|:-------|:---------|
| KEY_0  | 0x24     |
| KEY_1  | 0x28     |
| KEY_2  | 0x2c     |
| KEY_3  | 0x30     |
| KEY_4  | 0x34     |
| KEY_5  | 0x38     |
| KEY_6  | 0x3c     |
| KEY_7  | 0x40     |
| KEY_8  | 0x44     |
| KEY_9  | 0x48     |
| KEY_10 | 0x4c     |
| KEY_11 | 0x50     |
| KEY_12 | 0x54     |
| KEY_13 | 0x58     |
| KEY_14 | 0x5c     |
| KEY_15 | 0x60     |
| KEY_16 | 0x64     |
| KEY_17 | 0x68     |
| KEY_18 | 0x6c     |
| KEY_19 | 0x70     |
| KEY_20 | 0x74     |
| KEY_21 | 0x78     |
| KEY_22 | 0x7c     |
| KEY_23 | 0x80     |
| KEY_24 | 0x84     |
| KEY_25 | 0x88     |
| KEY_26 | 0x8c     |
| KEY_27 | 0x90     |
| KEY_28 | 0x94     |
| KEY_29 | 0x98     |
| KEY_30 | 0x9c     |
| KEY_31 | 0xa0     |


### Fields

```wavejson
{"reg": [{"name": "key", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                         |
|:------:|:------:|:-------:|:-------|:------------------------------------|
|  31:0  |   wo   |    x    | key    | 32-bit chunk of 1024-bit secret key |

## DIGEST
Digest output.

If HMAC is disabled, the register shows result of SHA-2 256/384/512.
<!-- imp_hmac_000A begin -->
Order of the 512-bit digest[511:0] = {DIGEST0, DIGEST1, DIGEST2, ... , DIGEST15}.
For SHA-2 256 order of the 256-bit digest[255:0] = {DIGEST0, DIGEST1, DIGEST2, DIGEST3, DIGEST4, DIGEST5, DIGEST6, DIGEST7} and {DIGEST8 - DIGEST15} are irrelevant and should not be read out.
For SHA-2 384, {DIGEST12-DIGEST15} are truncated; they are irrelevant and should not be read out.
<!-- imp_hmac_000A end -->

<!-- req_hmac_0031 begin -->
The digest gets cleared when `CFG.sha_en` transitions from 1 to 0.
When `CFG.sha_en` is 0, these registers can be written to by software.
<!-- req_hmac_0031 end -->
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name      | Offset   |
|:----------|:---------|
| DIGEST_0  | 0xa4     |
| DIGEST_1  | 0xa8     |
| DIGEST_2  | 0xac     |
| DIGEST_3  | 0xb0     |
| DIGEST_4  | 0xb4     |
| DIGEST_5  | 0xb8     |
| DIGEST_6  | 0xbc     |
| DIGEST_7  | 0xc0     |
| DIGEST_8  | 0xc4     |
| DIGEST_9  | 0xc8     |
| DIGEST_10 | 0xcc     |
| DIGEST_11 | 0xd0     |
| DIGEST_12 | 0xd4     |
| DIGEST_13 | 0xd8     |
| DIGEST_14 | 0xdc     |
| DIGEST_15 | 0xe0     |


### Fields

```wavejson
{"reg": [{"name": "digest", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                    |
|:------:|:------:|:-------:|:-------|:-------------------------------|
|  31:0  |   rw   |    x    | digest | 32-bit chunk of 512-bit digest |

## MSG_LENGTH_LOWER
Received Message Length calculated by the HMAC in bits [31:0]

Message is byte granularity.
Lower 3 bits [2:0] are ignored.

<!-- req_hmac_0031 begin -->
When `CFG.sha_en` is 0, this register can be written by software.
<!-- req_hmac_0031 end -->
- Offset: `0xe4`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "v", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description           |
|:------:|:------:|:-------:|:-------|:----------------------|
|  31:0  |   rw   |    x    | v      | Message Length [31:0] |

## MSG_LENGTH_UPPER
Received Message Length calculated by the HMAC in bits [63:32]

<!-- req_hmac_0031 begin -->
When `CFG.sha_en` is 0, this register can be written by software.
<!-- req_hmac_0031 end -->
<!-- imp_hmac_0014 begin -->
For SHA-2-2 256 computations, message length is 64-bit {MSG_LENGTH_UPPER, MSG_LENGTH_LOWER}.
For SHA-2 384/512 message length is extended to 128-bit in line with [nist-fips-180-4] where the upper 64 bits get zero-padded: {32'b0, 32'b0, MSG_LENGTH_UPPER, MSG_LENGTH_LOWER}.
<!-- imp_hmac_0014 end -->
- Offset: `0xe8`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "v", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description            |
|:------:|:------:|:-------:|:-------|:-----------------------|
|  31:0  |   rw   |    x    | v      | Message Length [63:32] |

## MSG_FIFO
<!-- imp_hmac_0015 begin -->
Message FIFO. Any write to this window will be appended to the FIFO.
Only the lower [1:0] bits of the address matter to writes within the window
(for correctly dealing with non 32-bit writes)
<!-- imp_hmac_0015 end -->

- Word Aligned Offset Range: `0x1000`to`0x1ffc`
- Size (words): `1024`
- Access: `wo`
- Byte writes are  supported.


<!-- END CMDGEN -->
