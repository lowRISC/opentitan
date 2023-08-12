# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/hmac/data/hmac.hjson -->
## Summary

| Name                                         | Offset   |   Length | Description                                                                                                                                                                                     |
|:---------------------------------------------|:---------|---------:|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| hmac.[`INTR_STATE`](#intr_state)             | 0x0      |        4 | Interrupt State Register                                                                                                                                                                        |
| hmac.[`INTR_ENABLE`](#intr_enable)           | 0x4      |        4 | Interrupt Enable Register                                                                                                                                                                       |
| hmac.[`INTR_TEST`](#intr_test)               | 0x8      |        4 | Interrupt Test Register                                                                                                                                                                         |
| hmac.[`ALERT_TEST`](#alert_test)             | 0xc      |        4 | Alert Test Register                                                                                                                                                                             |
| hmac.[`CFG`](#cfg)                           | 0x10     |        4 | HMAC Configuration register.                                                                                                                                                                    |
| hmac.[`CMD`](#cmd)                           | 0x14     |        4 | HMAC command register                                                                                                                                                                           |
| hmac.[`STATUS`](#status)                     | 0x18     |        4 | HMAC Status register                                                                                                                                                                            |
| hmac.[`ERR_CODE`](#err_code)                 | 0x1c     |        4 | HMAC Error Code                                                                                                                                                                                 |
| hmac.[`WIPE_SECRET`](#wipe_secret)           | 0x20     |        4 | Randomize internal secret registers.                                                                                                                                                            |
| hmac.[`KEY_0`](#key)                         | 0x24     |        4 | HMAC Secret Key                                                                                                                                                                                 |
| hmac.[`KEY_1`](#key)                         | 0x28     |        4 | HMAC Secret Key                                                                                                                                                                                 |
| hmac.[`KEY_2`](#key)                         | 0x2c     |        4 | HMAC Secret Key                                                                                                                                                                                 |
| hmac.[`KEY_3`](#key)                         | 0x30     |        4 | HMAC Secret Key                                                                                                                                                                                 |
| hmac.[`KEY_4`](#key)                         | 0x34     |        4 | HMAC Secret Key                                                                                                                                                                                 |
| hmac.[`KEY_5`](#key)                         | 0x38     |        4 | HMAC Secret Key                                                                                                                                                                                 |
| hmac.[`KEY_6`](#key)                         | 0x3c     |        4 | HMAC Secret Key                                                                                                                                                                                 |
| hmac.[`KEY_7`](#key)                         | 0x40     |        4 | HMAC Secret Key                                                                                                                                                                                 |
| hmac.[`DIGEST_0`](#digest)                   | 0x44     |        4 | Digest output. If HMAC is disabled, the register shows result of SHA256                                                                                                                         |
| hmac.[`DIGEST_1`](#digest)                   | 0x48     |        4 | Digest output. If HMAC is disabled, the register shows result of SHA256                                                                                                                         |
| hmac.[`DIGEST_2`](#digest)                   | 0x4c     |        4 | Digest output. If HMAC is disabled, the register shows result of SHA256                                                                                                                         |
| hmac.[`DIGEST_3`](#digest)                   | 0x50     |        4 | Digest output. If HMAC is disabled, the register shows result of SHA256                                                                                                                         |
| hmac.[`DIGEST_4`](#digest)                   | 0x54     |        4 | Digest output. If HMAC is disabled, the register shows result of SHA256                                                                                                                         |
| hmac.[`DIGEST_5`](#digest)                   | 0x58     |        4 | Digest output. If HMAC is disabled, the register shows result of SHA256                                                                                                                         |
| hmac.[`DIGEST_6`](#digest)                   | 0x5c     |        4 | Digest output. If HMAC is disabled, the register shows result of SHA256                                                                                                                         |
| hmac.[`DIGEST_7`](#digest)                   | 0x60     |        4 | Digest output. If HMAC is disabled, the register shows result of SHA256                                                                                                                         |
| hmac.[`MSG_LENGTH_LOWER`](#msg_length_lower) | 0x64     |        4 | Received Message Length calculated by the HMAC in bits [31:0]                                                                                                                                   |
| hmac.[`MSG_LENGTH_UPPER`](#msg_length_upper) | 0x68     |        4 | Received Message Length calculated by the HMAC in bits [63:32]                                                                                                                                  |
| hmac.[`MSG_FIFO`](#msg_fifo)                 | 0x800    |     2048 | Message FIFO. Any write to this window will be appended to the FIFO. Only the lower [1:0] bits of the address matter to writes within the window (for correctly dealing with non 32-bit writes) |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "hmac_done", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "fifo_empty", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "hmac_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                       |
|:------:|:------:|:-------:|:-----------|:------------------------------------------------------------------|
|  31:3  |        |         |            | Reserved                                                          |
|   2    |  rw1c  |   0x0   | hmac_err   | HMAC error occurred. ERR_CODE register shows which error occurred |
|   1    |  rw1c  |   0x0   | fifo_empty | Message FIFO empty condition                                      |
|   0    |  rw1c  |   0x0   | hmac_done  | HMAC-256 completes a message with key                             |

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

The register is updated when the engine is in Idle.
If the software updates the register while the engine computes the hash,
the updated value is discarded.
- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "hmac_en", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "sha_en", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endian_swap", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "digest_swap", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name                             |
|:------:|:------:|:-------:|:---------------------------------|
|  31:4  |        |         | Reserved                         |
|   3    |   rw   |   0x0   | [digest_swap](#cfg--digest_swap) |
|   2    |   rw   |   0x0   | [endian_swap](#cfg--endian_swap) |
|   1    |   rw   |    x    | [sha_en](#cfg--sha_en)           |
|   0    |   rw   |    x    | [hmac_en](#cfg--hmac_en)         |

### CFG . digest_swap
Digest register byte swap.

If 1 the value contained in each digest output register is
converted to big-endian byte order.
This setting does not affect the order of the digest output
registers, [`DIGEST_0`](#digest_0) still contains the first 4 bytes of
the digest.

### CFG . endian_swap
Endian swap.

If 0, each value will be added to the message in little-endian
byte order. The value is written to MSG_FIFO same to the SW writes.

If 1, then each individual multi-byte value, regardless of its
alignment, written to [`MSG_FIFO`](#msg_fifo) will be added to the message
in big-endian byte order.

A message written to [`MSG_FIFO`](#msg_fifo) one byte at a time will not be
affected by this setting.

From a hardware perspective byte swaps are performed on a TL-UL
word granularity.

### CFG . sha_en
SHA256 enable. If 0, SHA engine won't initiate compression,
this is used to stop operation of the SHA engine until configuration
has been done. When the SHA engine is disabled the digest is cleared.

### CFG . hmac_en
HMAC datapath enable.

If this bit is 1, HMAC operates when `hash_start` toggles.

## CMD
HMAC command register
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "hash_start", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"name": "hash_process", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                                                                                                                             |
|:------:|:------:|:-------:|:-------------|:--------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:2  |        |         |              | Reserved                                                                                                                                                |
|   1    | r0w1c  |    x    | hash_process | If writes 1 into this field, SHA256 or HMAC calculates the digest or signing based on currently received message.                                       |
|   0    | r0w1c  |    x    | hash_start   | If writes 1 into this field, SHA256 or HMAC begins its operation.  CPU should configure relative information first, such as message_length, secret_key. |

## STATUS
HMAC Status register
- Offset: `0x18`
- Reset default: `0x1`
- Reset mask: `0x1f3`

### Fields

```wavejson
{"reg": [{"name": "fifo_empty", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "fifo_full", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 2}, {"name": "fifo_depth", "bits": 5, "attr": ["ro"], "rotate": -90}, {"bits": 23}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                                                        |
|:------:|:------:|:-------:|:-----------|:---------------------------------------------------------------------------------------------------|
|  31:9  |        |         |            | Reserved                                                                                           |
|  8:4   |   ro   |    x    | fifo_depth | FIFO entry count.                                                                                  |
|  3:2   |        |         |            | Reserved                                                                                           |
|   1    |   ro   |    x    | fifo_full  | FIFO full. Data written to the FIFO whilst it is full will cause back-pressure on the interconnect |
|   0    |   ro   |   0x1   | fifo_empty | FIFO empty                                                                                         |

## ERR_CODE
HMAC Error Code
- Offset: `0x1c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "err_code", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                                                                                                      |
|:------:|:------:|:-------:|:---------|:-------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   ro   |   0x0   | err_code | If error interrupt occurs, this register has information of error cause. Please take a look at `hw/ip/hmac/rtl/hmac_pkg.sv:err_code_e enum type. |

## WIPE_SECRET
Randomize internal secret registers.

If CPU writes value into the register, the value is used to randomize internal
variables such as secret key, internal state machine, or hash value.
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

SHA256 assumes secret key is hashed 256bit key.
Order of the secret key is:
key[255:0] = {KEY0, KEY1, KEY2, ... , KEY7};

The registers are allowed to be updated when the engine is in Idle state.
If the engine computes the hash, it discards any attempts to update the secret keys
and report an error.
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


### Fields

```wavejson
{"reg": [{"name": "key", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                        |
|:------:|:------:|:-------:|:-------|:-----------------------------------|
|  31:0  |   wo   |    x    | key    | 32-bit chunk of 256-bit Secret Key |

## DIGEST
Digest output. If HMAC is disabled, the register shows result of SHA256

Order of the digest is:
digest[255:0] = {DIGEST0, DIGEST1, DIGEST2, ... , DIGEST7};
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name     | Offset   |
|:---------|:---------|
| DIGEST_0 | 0x44     |
| DIGEST_1 | 0x48     |
| DIGEST_2 | 0x4c     |
| DIGEST_3 | 0x50     |
| DIGEST_4 | 0x54     |
| DIGEST_5 | 0x58     |
| DIGEST_6 | 0x5c     |
| DIGEST_7 | 0x60     |


### Fields

```wavejson
{"reg": [{"name": "digest", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                    |
|:------:|:------:|:-------:|:-------|:-------------------------------|
|  31:0  |   ro   |    x    | digest | 32-bit chunk of 256-bit Digest |

## MSG_LENGTH_LOWER
Received Message Length calculated by the HMAC in bits [31:0]

Message is byte granularity.
lower 3bits [2:0] are ignored.
- Offset: `0x64`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "v", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description           |
|:------:|:------:|:-------:|:-------|:----------------------|
|  31:0  |   ro   |   0x0   | v      | Message Length [31:0] |

## MSG_LENGTH_UPPER
Received Message Length calculated by the HMAC in bits [63:32]
- Offset: `0x68`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "v", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description            |
|:------:|:------:|:-------:|:-------|:-----------------------|
|  31:0  |   ro   |   0x0   | v      | Message Length [63:32] |

## MSG_FIFO
Message FIFO. Any write to this window will be appended to the FIFO. Only the lower [1:0] bits of the address matter to writes within the window (for correctly dealing with non 32-bit writes)

- Word Aligned Offset Range: `0x800`to`0xffc`
- Size (words): `512`
- Access: `wo`
- Byte writes are  supported.


<!-- END CMDGEN -->
