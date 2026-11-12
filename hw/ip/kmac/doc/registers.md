# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/kmac/data/kmac.hjson -->
## Summary

| Name                                                         | Offset   |   Length | Description                                                                         |
|:-------------------------------------------------------------|:---------|---------:|:------------------------------------------------------------------------------------|
| kmac.[`INTR_STATE`](#intr_state)                             | 0x0      |        4 | Interrupt State Register                                                            |
| kmac.[`INTR_ENABLE`](#intr_enable)                           | 0x4      |        4 | Interrupt Enable Register                                                           |
| kmac.[`INTR_TEST`](#intr_test)                               | 0x8      |        4 | Interrupt Test Register                                                             |
| kmac.[`ALERT_TEST`](#alert_test)                             | 0xc      |        4 | Alert Test Register                                                                 |
| kmac.[`CFG_REGWEN`](#cfg_regwen)                             | 0x10     |        4 | Register write enable for [`CFG_SHADOWED`](#cfg_shadowed) register.                 |
| kmac.[`CFG_SHADOWED`](#cfg_shadowed)                         | 0x14     |        4 | KMAC Configuration register.                                                        |
| kmac.[`CMD`](#cmd)                                           | 0x18     |        4 | KMAC/ SHA3 command register.                                                        |
| kmac.[`STATUS`](#status)                                     | 0x1c     |        4 | KMAC/SHA3 Status register.                                                          |
| kmac.[`ENTROPY_CFG_LOCK`](#entropy_cfg_lock)                 | 0x20     |        4 | Software lock for the [`ENTROPY_CFG_SHADOWED`](#entropy_cfg_shadowed) register.     |
| kmac.[`ENTROPY_CFG_REGWEN`](#entropy_cfg_regwen)             | 0x24     |        4 | Register write enable for [`ENTROPY_CFG_SHADOWED`](#entropy_cfg_shadowed) register. |
| kmac.[`ENTROPY_CFG_SHADOWED`](#entropy_cfg_shadowed)         | 0x28     |        4 | Entropy Configuration register.                                                     |
| kmac.[`ENTROPY_SEED`](#entropy_seed)                         | 0x2c     |        4 | Entropy Seed                                                                        |
| kmac.[`ENTROPY_REFRESH_HASH_CNT`](#entropy_refresh_hash_cnt) | 0x30     |        4 | Entropy Refresh Counter                                                             |
| kmac.[`KEY_SHARE0_0`](#key_share0)                           | 0x34     |        4 | KMAC Secret Key                                                                     |
| kmac.[`KEY_SHARE0_1`](#key_share0)                           | 0x38     |        4 | KMAC Secret Key                                                                     |
| kmac.[`KEY_SHARE0_2`](#key_share0)                           | 0x3c     |        4 | KMAC Secret Key                                                                     |
| kmac.[`KEY_SHARE0_3`](#key_share0)                           | 0x40     |        4 | KMAC Secret Key                                                                     |
| kmac.[`KEY_SHARE0_4`](#key_share0)                           | 0x44     |        4 | KMAC Secret Key                                                                     |
| kmac.[`KEY_SHARE0_5`](#key_share0)                           | 0x48     |        4 | KMAC Secret Key                                                                     |
| kmac.[`KEY_SHARE0_6`](#key_share0)                           | 0x4c     |        4 | KMAC Secret Key                                                                     |
| kmac.[`KEY_SHARE0_7`](#key_share0)                           | 0x50     |        4 | KMAC Secret Key                                                                     |
| kmac.[`KEY_SHARE0_8`](#key_share0)                           | 0x54     |        4 | KMAC Secret Key                                                                     |
| kmac.[`KEY_SHARE0_9`](#key_share0)                           | 0x58     |        4 | KMAC Secret Key                                                                     |
| kmac.[`KEY_SHARE0_10`](#key_share0)                          | 0x5c     |        4 | KMAC Secret Key                                                                     |
| kmac.[`KEY_SHARE0_11`](#key_share0)                          | 0x60     |        4 | KMAC Secret Key                                                                     |
| kmac.[`KEY_SHARE0_12`](#key_share0)                          | 0x64     |        4 | KMAC Secret Key                                                                     |
| kmac.[`KEY_SHARE0_13`](#key_share0)                          | 0x68     |        4 | KMAC Secret Key                                                                     |
| kmac.[`KEY_SHARE0_14`](#key_share0)                          | 0x6c     |        4 | KMAC Secret Key                                                                     |
| kmac.[`KEY_SHARE0_15`](#key_share0)                          | 0x70     |        4 | KMAC Secret Key                                                                     |
| kmac.[`KEY_SHARE1_0`](#key_share1)                           | 0x74     |        4 | KMAC Secret Key, 2nd share.                                                         |
| kmac.[`KEY_SHARE1_1`](#key_share1)                           | 0x78     |        4 | KMAC Secret Key, 2nd share.                                                         |
| kmac.[`KEY_SHARE1_2`](#key_share1)                           | 0x7c     |        4 | KMAC Secret Key, 2nd share.                                                         |
| kmac.[`KEY_SHARE1_3`](#key_share1)                           | 0x80     |        4 | KMAC Secret Key, 2nd share.                                                         |
| kmac.[`KEY_SHARE1_4`](#key_share1)                           | 0x84     |        4 | KMAC Secret Key, 2nd share.                                                         |
| kmac.[`KEY_SHARE1_5`](#key_share1)                           | 0x88     |        4 | KMAC Secret Key, 2nd share.                                                         |
| kmac.[`KEY_SHARE1_6`](#key_share1)                           | 0x8c     |        4 | KMAC Secret Key, 2nd share.                                                         |
| kmac.[`KEY_SHARE1_7`](#key_share1)                           | 0x90     |        4 | KMAC Secret Key, 2nd share.                                                         |
| kmac.[`KEY_SHARE1_8`](#key_share1)                           | 0x94     |        4 | KMAC Secret Key, 2nd share.                                                         |
| kmac.[`KEY_SHARE1_9`](#key_share1)                           | 0x98     |        4 | KMAC Secret Key, 2nd share.                                                         |
| kmac.[`KEY_SHARE1_10`](#key_share1)                          | 0x9c     |        4 | KMAC Secret Key, 2nd share.                                                         |
| kmac.[`KEY_SHARE1_11`](#key_share1)                          | 0xa0     |        4 | KMAC Secret Key, 2nd share.                                                         |
| kmac.[`KEY_SHARE1_12`](#key_share1)                          | 0xa4     |        4 | KMAC Secret Key, 2nd share.                                                         |
| kmac.[`KEY_SHARE1_13`](#key_share1)                          | 0xa8     |        4 | KMAC Secret Key, 2nd share.                                                         |
| kmac.[`KEY_SHARE1_14`](#key_share1)                          | 0xac     |        4 | KMAC Secret Key, 2nd share.                                                         |
| kmac.[`KEY_SHARE1_15`](#key_share1)                          | 0xb0     |        4 | KMAC Secret Key, 2nd share.                                                         |
| kmac.[`KEY_LEN`](#key_len)                                   | 0xb4     |        4 | Secret Key length in bit.                                                           |
| kmac.[`PREFIX_0`](#prefix)                                   | 0xb8     |        4 | cSHAKE Prefix register.                                                             |
| kmac.[`PREFIX_1`](#prefix)                                   | 0xbc     |        4 | cSHAKE Prefix register.                                                             |
| kmac.[`PREFIX_2`](#prefix)                                   | 0xc0     |        4 | cSHAKE Prefix register.                                                             |
| kmac.[`PREFIX_3`](#prefix)                                   | 0xc4     |        4 | cSHAKE Prefix register.                                                             |
| kmac.[`PREFIX_4`](#prefix)                                   | 0xc8     |        4 | cSHAKE Prefix register.                                                             |
| kmac.[`PREFIX_5`](#prefix)                                   | 0xcc     |        4 | cSHAKE Prefix register.                                                             |
| kmac.[`PREFIX_6`](#prefix)                                   | 0xd0     |        4 | cSHAKE Prefix register.                                                             |
| kmac.[`PREFIX_7`](#prefix)                                   | 0xd4     |        4 | cSHAKE Prefix register.                                                             |
| kmac.[`PREFIX_8`](#prefix)                                   | 0xd8     |        4 | cSHAKE Prefix register.                                                             |
| kmac.[`PREFIX_9`](#prefix)                                   | 0xdc     |        4 | cSHAKE Prefix register.                                                             |
| kmac.[`PREFIX_10`](#prefix)                                  | 0xe0     |        4 | cSHAKE Prefix register.                                                             |
| kmac.[`ERR_CODE`](#err_code)                                 | 0xe4     |        4 | KMAC/SHA3 Error Code                                                                |
| kmac.[`STATE`](#state)                                       | 0x400    |      512 | Keccak State (1600 bit) memory.                                                     |
| kmac.[`MSG_FIFO`](#msg_fifo)                                 | 0x800    |     2048 | Message FIFO.                                                                       |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "kmac_done", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "fifo_empty", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "kmac_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name                                  |
|:------:|:------:|:-------:|:--------------------------------------|
|  31:3  |        |         | Reserved                              |
|   2    |  rw1c  |   0x0   | [kmac_err](#intr_state--kmac_err)     |
|   1    |   ro   |   0x0   | [fifo_empty](#intr_state--fifo_empty) |
|   0    |  rw1c  |   0x0   | [kmac_done](#intr_state--kmac_done)   |

### INTR_STATE . kmac_err
KMAC/SHA3 error occurred. ERR_CODE register shows the details

### INTR_STATE . fifo_empty
The message FIFO is empty.
This interrupt is raised only if the message FIFO is actually writable by software, i.e., if all of the following conditions are met:
i) The KMAC block is not exercised by a hardware application interface.
ii) The SHA3 block is in the Absorb state.
iii) Software has not yet written the Process command to finish the absorption process.
For the interrupt to be raised, the message FIFO must also have been full previously.
Otherwise, the hardware empties the FIFO faster than software can fill it and there is no point in interrupting the software to inform it about the message FIFO being empty.

### INTR_STATE . kmac_done
KMAC/SHA3 absorbing has been completed

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "kmac_done", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "fifo_empty", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "kmac_err", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                          |
|:------:|:------:|:-------:|:-----------|:---------------------------------------------------------------------|
|  31:3  |        |         |            | Reserved                                                             |
|   2    |   rw   |   0x0   | kmac_err   | Enable interrupt when [`INTR_STATE.kmac_err`](#intr_state) is set.   |
|   1    |   rw   |   0x0   | fifo_empty | Enable interrupt when [`INTR_STATE.fifo_empty`](#intr_state) is set. |
|   0    |   rw   |   0x0   | kmac_done  | Enable interrupt when [`INTR_STATE.kmac_done`](#intr_state) is set.  |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "kmac_done", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fifo_empty", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "kmac_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                   |
|:------:|:------:|:-------:|:-----------|:--------------------------------------------------------------|
|  31:3  |        |         |            | Reserved                                                      |
|   2    |   wo   |   0x0   | kmac_err   | Write 1 to force [`INTR_STATE.kmac_err`](#intr_state) to 1.   |
|   1    |   wo   |   0x0   | fifo_empty | Write 1 to force [`INTR_STATE.fifo_empty`](#intr_state) to 1. |
|   0    |   wo   |   0x0   | kmac_done  | Write 1 to force [`INTR_STATE.kmac_done`](#intr_state) to 1.  |

## ALERT_TEST
Alert Test Register
- Offset: `0xc`
- Reset default: `0x80000000`
- Reset mask: `0x80000003`

### Fields

```wavejson
{"reg": [{"name": "recov_operation_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_fault_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 29}, {"name": "regwen", "bits": 1, "attr": ["rw0c"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 210}}
```

|  Bits  |  Type  |  Reset  | Name                | Description                                            |
|:------:|:------:|:-------:|:--------------------|:-------------------------------------------------------|
|   31   |  rw0c  |   0x1   | regwen              | Write 0 to disable alert testing until the next reset. |
|  30:2  |        |         |                     | Reserved                                               |
|   1    |   wo   |   0x0   | fatal_fault_err     | Write 1 to trigger one alert event of this kind.       |
|   0    |   wo   |   0x0   | recov_operation_err | Write 1 to trigger one alert event of this kind.       |

## CFG_REGWEN
Register write enable for [`CFG_SHADOWED`](#cfg_shadowed) register.
- Offset: `0x10`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "CFG_REGWEN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                                                                                                                                                                           |
|:------:|:------:|:-------:|:-----------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |            | Reserved                                                                                                                                                                                                              |
|   0    |   ro   |   0x1   | CFG_REGWEN | This bit indicates whether the [`CFG_SHADOWED`](#cfg_shadowed) register can be updated by software (1) or not (0). This bit reads 0 if the Keccak core is operating as indicated in the [`STATUS`](#status) register. |

## CFG_SHADOWED
KMAC Configuration register.

This register can only be updated when the Keccak core is idle.
This is indicated by [`CFG_REGWEN`](#cfg_regwen) reading as 1.
If [`CFG_REGWEN`](#cfg_regwen) reads as 0 (meaning the Keccak core is busy), writes to this register are ignored.
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0x418133f`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "kmac_en", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "kstrength", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "mode", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 2}, {"name": "msg_endianness", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "state_endianness", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 2}, {"name": "sideload", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 6}, {"name": "entropy_fast_process", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "msg_mask", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 5}, {"name": "en_unsupported_modestrength", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 5}], "config": {"lanes": 1, "fontsize": 10, "vspace": 290}}
```

|  Bits  |  Type  |  Reset  | Name                                                                      |
|:------:|:------:|:-------:|:--------------------------------------------------------------------------|
| 31:27  |        |         | Reserved                                                                  |
|   26   |   rw   |   0x0   | [en_unsupported_modestrength](#cfg_shadowed--en_unsupported_modestrength) |
| 25:21  |        |         | Reserved                                                                  |
|   20   |   rw   |   0x0   | [msg_mask](#cfg_shadowed--msg_mask)                                       |
|   19   |   rw   |   0x0   | [entropy_fast_process](#cfg_shadowed--entropy_fast_process)               |
| 18:13  |        |         | Reserved                                                                  |
|   12   |   rw   |   0x0   | [sideload](#cfg_shadowed--sideload)                                       |
| 11:10  |        |         | Reserved                                                                  |
|   9    |   rw   |   0x0   | [state_endianness](#cfg_shadowed--state_endianness)                       |
|   8    |   rw   |   0x0   | [msg_endianness](#cfg_shadowed--msg_endianness)                           |
|  7:6   |        |         | Reserved                                                                  |
|  5:4   |   rw   |   0x0   | [mode](#cfg_shadowed--mode)                                               |
|  3:1   |   rw   |   0x0   | [kstrength](#cfg_shadowed--kstrength)                                     |
|   0    |   rw   |   0x0   | [kmac_en](#cfg_shadowed--kmac_en)                                         |

### CFG_SHADOWED . en_unsupported_modestrength
Enable Unsupported Mode and Strength configs.

SW may set this field for KMAC to move forward with unsupported
Keccak Mode and Strength configurations, such as cSHAKE512.

If not set, KMAC won't propagate the SW command (CmdStart) to the
rest of the blocks (AppIntf, KMAC Core, SHA3).

### CFG_SHADOWED . msg_mask
Message Masking with PRNG.

If 1, KMAC applies PRNG to the input messages to the Keccak module
when KMAC mode is on.

### CFG_SHADOWED . entropy_fast_process
Entropy Fast process mode.

If 1, entropy logic uses garbage data while not processing the KMAC
key block. It will re-use previous entropy value and will not
expand the entropy when it is consumed. Only it refreshes the
entropy while processing the secret key block. This process should
not be used if SCA resistance is required because it may cause side
channel leakage.

### CFG_SHADOWED . sideload
Sideloaded Key.

If 1, KMAC uses KeyMgr sideloaded key for SW initiated KMAC
operation. KMAC uses the sideloaded key regardless of this
configuration when KeyMgr initiates the KMAC operation for
Key Derivation Function (KDF).

### CFG_SHADOWED . state_endianness
State Endianness.

If 1 then each individual word in the [`STATE`](#state) output register
is converted to big-endian byte order.
The order of the words in relation to one another is not
changed.
This setting does not affect how the state is interpreted
during computation.

### CFG_SHADOWED . msg_endianness
Message Endianness.

If 1 then each individual multi-byte value, regardless of its
alignment, written to [`MSG_FIFO`](#msg_fifo) will be added to the message
in big-endian byte order.
If 0, each value will be added to the message in little-endian
byte order.
A message written to [`MSG_FIFO`](#msg_fifo) one byte at a time will not be
affected by this setting.
From a hardware perspective byte swaps are performed on a TL-UL
word granularity.

### CFG_SHADOWED . mode
Keccak hashing mode.

This module supports SHA3 main hashing algorithm and the part
of its derived functions, SHAKE and cSHAKE with limitations.
This field is to select the mode.

| Value   | Name   | Description                                              |
|:--------|:-------|:---------------------------------------------------------|
| 0x0     | SHA3   | SHA3 hashing mode. It appends `2'b 10` to the end of msg |
| 0x2     | SHAKE  | SHAKE hashing mode. It appends `1111` to the end of msg  |
| 0x3     | cSHAKE | cSHAKE hashing mode. It appends `00` to the end of msg   |

Other values are reserved.

### CFG_SHADOWED . kstrength
Hashing Strength

3 bit field to select the security strength of SHA3 hashing
engine. If mode field is set to SHAKE or cSHAKE, only 128 and
256 strength can be selected. Other value will result error
when hashing starts.

| Value   | Name   | Description                               |
|:--------|:-------|:------------------------------------------|
| 0x0     | L128   | 128 bit strength. Keccak rate is 1344 bit |
| 0x1     | L224   | 224 bit strength. Keccak rate is 1152 bit |
| 0x2     | L256   | 256 bit strength. Keccak rate is 1088 bit |
| 0x3     | L384   | 384 bit strength. Keccak rate is 832 bit  |
| 0x4     | L512   | 512 bit strength. Keccak rate is 576 bit  |

Other values are reserved.

### CFG_SHADOWED . kmac_en
KMAC datapath enable.

If this bit is 1, the KMAC mode is active and the secret key is prepended to the incoming message.

## CMD
KMAC/ SHA3 command register.

This register is to control the KMAC to start accepting message,
to process the message, and to manually run additional keccak
rounds at the end. Only at certain stage, the CMD affects to the
control logic. It follows the sequence of

`start` --> `process` --> {`run` if needed --> } `done`
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0x73f`

### Fields

```wavejson
{"reg": [{"name": "cmd", "bits": 6, "attr": ["r0w1c"], "rotate": 0}, {"bits": 2}, {"name": "entropy_req", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"name": "hash_cnt_clr", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"name": "err_processed", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"bits": 21}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name                                 |
|:------:|:------:|:-------:|:-------------------------------------|
| 31:11  |        |         | Reserved                             |
|   10   | r0w1c  |    x    | [err_processed](#cmd--err_processed) |
|   9    | r0w1c  |    x    | [hash_cnt_clr](#cmd--hash_cnt_clr)   |
|   8    | r0w1c  |    x    | [entropy_req](#cmd--entropy_req)     |
|  7:6   |        |         | Reserved                             |
|  5:0   | r0w1c  |    x    | [cmd](#cmd--cmd)                     |

### CMD . err_processed
When error occurs and one of the state machine stays at
 Error handling state, SW may process the error based on
 ERR_CODE, then let FSM back to the reset state

### CMD . hash_cnt_clr
Software can set this bit to 1 to manually clear [`ENTROPY_REFRESH_HASH_CNT.`](#entropy_refresh_hash_cnt)

### CMD . entropy_req
Software can set this bit to 1 to manually trigger the reseeding of the internal PRNG when running in EDN Mode or in Software Mode.
This will also clear [`ENTROPY_REFRESH_HASH_CNT.`](#entropy_refresh_hash_cnt)

After setting this bit, the [`STATUS.entropy_ready`](#status) bit should read as 0 and the [`STATUS.entropy_reseeding`](#status) bit as 1 indicating that a reseed operation is ongoing.

If [`ENTROPY_CFG_SHADOWED.ignore_cmd_entropy_req`](#entropy_cfg_shadowed) is set, this bit is ignored.
If masking is disabled, this bit is ignored.

### CMD . cmd
Issue a command to the KMAC/SHA3 IP. The command is sparse
encoded. To prevent sw from writing multiple commands at once,
the field is defined as enum.

| Value   | Name        | Description                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
|:--------|:------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0x07    | start       | Writing 6'b000111 or dec 7 into this field when KMAC/SHA3 is in idle, KMAC/SHA3 begins its operation. If the mode is cSHAKE, before receiving the message, the hashing logic processes Function name string N and customization input string S first. If KMAC mode is enabled, additionally it processes secret key block.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| 0x32    | process     | Writing 6'b110010 or dec 50 into this field when KMAC/SHA3 began its operation and received the entire message, it computes the digest or signing.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          |
| 0x2e    | run         | The `run` field is used in the sponge squeezing stage. It triggers the keccak round logic to run full 24 rounds. This is optional and used when software needs more digest bits than the keccak rate. It only affects when the kmac/sha3 operation is completed.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| 0x35    | done        | Writing 6'b110101 or dec 53 into this field completes the operation. The KMAC/SHA3 hashing engine clears the Keccak state and internal variables and goes back to Idle state for the next command. The command also releases the KMAC HWIP when SW has claimed it with the `state_write` command.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| 0x1c    | stop        | Writing 6'b011100 or dec 28 into this field when KMAC/SHA3 is receiving the message stops the sponge absorbing stage without appending any padding. The Keccak state then holds a valid intermediate sponge state, which SW can read from [`STATE`](#state) to save the context. The message received since the last `start` or `continue` command must be a multiple of the Keccak rate. Otherwise the absorbing stage is stopped anyway, but the exposed state is not a valid context and `ErrSwStopNotBlockAligned` is reported. Once [`STATUS.sha3_stopped`](#status) is set, or the `kmac_done` interrupt is raised, SW reads [`STATE`](#state) and completes the operation with the `done` command, which clears the Keccak state. This command is not available when a sideloaded key is used, as saving the context would expose the key. The command is then discarded and `ErrSwSaveRestoreSideload` is reported. |
| 0x1b    | state_write | Writing 6'b011011 or dec 27 into this field when KMAC/SHA3 is idle claims the KMAC HWIP for SW such that it can write a previously saved context to the KMAC HWIP. The command also clears the Keccak state, so a restore always starts from a known state. SW resumes the operation with the `continue` command once the full context is written. If SW decides not to resume after all, the `done` command releases the KMAC HWIP again. This command is not available when a sideloaded key is used. The command is then discarded and `ErrSwSaveRestoreSideload` is reported.                                                                                                                                                                                                                                                                                                                                           |
| 0x29    | continue    | Writing 6'b101001 or dec 41 into this field after the `state_write` command resumes the sponge absorbing stage from the context that SW has written into [`STATE.`](#state) Issuing it without claiming the KMAC HWIP first is discarded and reported as `ErrSwCmdSequence`. In contrast to the `start` command, the prefix and key are not processed again, as both are already part of the restored state. The [`KEY_SHARE0`](#key_share0) and [`KEY_SHARE1`](#key_share1) registers therefore do not need to be restored, but [`CFG_SHADOWED`](#cfg_shadowed) must hold the same configuration as before the context was saved. This command is not available when a sideloaded key is used. The command is then discarded and `ErrSwSaveRestoreSideload` is reported.                                                                                                                                                   |

Other values are reserved.

## STATUS
KMAC/SHA3 Status register.
- Offset: `0x1c`
- Reset default: `0x4001`
- Reset mask: `0x3030df1f`

### Fields

```wavejson
{"reg": [{"name": "sha3_idle", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "sha3_absorb", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "sha3_squeeze", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "sha3_stopped", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "state_write", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 3}, {"name": "fifo_depth", "bits": 5, "attr": ["ro"], "rotate": -90}, {"bits": 1}, {"name": "fifo_empty", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "fifo_full", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 4}, {"name": "entropy_ready", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "entropy_reseeding", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 6}, {"name": "ALERT_FATAL_FAULT", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ALERT_RECOV_CTRL_UPDATE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 2}], "config": {"lanes": 1, "fontsize": 10, "vspace": 290}}
```

|  Bits  |  Type  |  Reset  | Name                                                                |
|:------:|:------:|:-------:|:--------------------------------------------------------------------|
| 31:30  |        |         | Reserved                                                            |
|   29   |   ro   |   0x0   | [ALERT_RECOV_CTRL_UPDATE_ERR](#status--alert_recov_ctrl_update_err) |
|   28   |   ro   |   0x0   | [ALERT_FATAL_FAULT](#status--alert_fatal_fault)                     |
| 27:22  |        |         | Reserved                                                            |
|   21   |   ro   |   0x0   | [entropy_reseeding](#status--entropy_reseeding)                     |
|   20   |   ro   |   0x0   | [entropy_ready](#status--entropy_ready)                             |
| 19:16  |        |         | Reserved                                                            |
|   15   |   ro   |    x    | [fifo_full](#status--fifo_full)                                     |
|   14   |   ro   |   0x1   | [fifo_empty](#status--fifo_empty)                                   |
|   13   |        |         | Reserved                                                            |
|  12:8  |   ro   |    x    | [fifo_depth](#status--fifo_depth)                                   |
|  7:5   |        |         | Reserved                                                            |
|   4    |   ro   |    x    | [state_write](#status--state_write)                                 |
|   3    |   ro   |    x    | [sha3_stopped](#status--sha3_stopped)                               |
|   2    |   ro   |    x    | [sha3_squeeze](#status--sha3_squeeze)                               |
|   1    |   ro   |    x    | [sha3_absorb](#status--sha3_absorb)                                 |
|   0    |   ro   |   0x1   | [sha3_idle](#status--sha3_idle)                                     |

### STATUS . ALERT_RECOV_CTRL_UPDATE_ERR
An update error has not occurred (0) or has occurred (1) in the shadowed Control Register.
KMAC operation needs to be restarted by re-writing the Control Register.

### STATUS . ALERT_FATAL_FAULT
No fatal fault has occurred inside the KMAC unit (0).
A fatal fault has occurred and the KMAC unit needs to be reset (1),
Examples for such faults include
i) TL-UL bus integrity fault
ii) storage errors in the shadow registers
iii) errors in the message, round, or key counter
iv) any internal FSM entering an invalid state
v) an error in the redundant lfsr

### STATUS . entropy_reseeding
If 1, the internal PRNG is currently performing a reseed operation via EDN or waiting for software to provide a new seed.

If masking is disabled, this bit always reads as 0.

### STATUS . entropy_ready
If 1, the internal PRNG is ready.
If 0, the internal PRNG is either not operating in EDN Mode or Software Mode (i.e., Entropy Boot Mode is active), or the PRNG is currently performing a reseed operation via EDN or waiting for software to provide a new seed via [`ENTROPY_SEED.`](#entropy_seed)
While this bit reads 0, the module will reject KMAC mode operation:
- If software tries to trigger a KMAC mode operation, a `ErrSwHashingWithoutEntropyReady` error is returned.
- If an application interface tries to trigger a KMAC mode operation, a `service rejected error` is returned.

If masking is disabled, this bit matches the inverse of the [`ENTROPY_CFG_SHADOWED.entropy_boot_mode`](#entropy_cfg_shadowed) bit.

### STATUS . fifo_full
Message FIFO Full indicator

### STATUS . fifo_empty
Message FIFO Empty indicator.

The FIFO's `Pass` parameter is set to `1'b 1`. So, by default, if
the SHA engine is ready, the write data to FIFO just passes
through.

In this case, `fifo_depth` remains **0**. `fifo_empty`, however,
lowers the value to **0** for a cycle, then goes back to the empty
state, **1**.

See the "Message FIFO" section in the spec for the reason.

### STATUS . fifo_depth
Count of occupied entries in the message FIFO.

### STATUS . state_write
If 1, SW has claimed the KMAC HWIP with the `state_write`
command and writes to [`STATE`](#state) are accepted. SW must poll this
bit after issuing the command and before writing the context.

The bit clears again when SW leaves the state with the
`continue` or the `done` command.

### STATUS . sha3_stopped
If 1, SHA3 has stopped the sponge absorbing stage for a
context switch. In this stage, SW can read the [`STATE`](#state) to save
the context. The absorbing stage is resumed by restoring the
[`STATE`](#state) and issuing the `continue` command.

### STATUS . sha3_squeeze
If 1, SHA3 completes sponge absorbing stage.
In this stage, SW can manually run the hashing engine.

### STATUS . sha3_absorb
If 1, SHA3 is receiving message stream and processing it

### STATUS . sha3_idle
If 1, SHA3 hashing engine is in idle state.

## ENTROPY_CFG_LOCK
Software lock for the [`ENTROPY_CFG_SHADOWED`](#entropy_cfg_shadowed) register.

By setting this register to 1, software can lock the current content of the [`ENTROPY_CFG_SHADOWED`](#entropy_cfg_shadowed) register until the next reset.
- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "ENTROPY_CFG_LOCK", "bits": 1, "attr": ["rw1s"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name                                                    |
|:------:|:------:|:-------:|:--------------------------------------------------------|
|  31:1  |        |         | Reserved                                                |
|   0    |  rw1s  |   0x0   | [ENTROPY_CFG_LOCK](#entropy_cfg_lock--entropy_cfg_lock) |

### ENTROPY_CFG_LOCK . ENTROPY_CFG_LOCK
This bit indicates whether software has locked the current content of the [`ENTROPY_CFG_SHADOWED`](#entropy_cfg_shadowed) register (1) or not (0).
Whether the [`ENTROPY_CFG_SHADOWED`](#entropy_cfg_shadowed) register can be updated, is indicated in [`ENTROPY_CFG_REGWEN.`](#entropy_cfg_regwen)
Once this bit is set to 1, [`ENTROPY_CFG_REGWEN`](#entropy_cfg_regwen) keeps reading as 0 until the next reset.

## ENTROPY_CFG_REGWEN
Register write enable for [`ENTROPY_CFG_SHADOWED`](#entropy_cfg_shadowed) register.
- Offset: `0x24`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "ENTROPY_CFG_REGWEN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name                                                          |
|:------:|:------:|:-------:|:--------------------------------------------------------------|
|  31:1  |        |         | Reserved                                                      |
|   0    |   ro   |   0x1   | [ENTROPY_CFG_REGWEN](#entropy_cfg_regwen--entropy_cfg_regwen) |

### ENTROPY_CFG_REGWEN . ENTROPY_CFG_REGWEN
This bit indicates whether the [`ENTROPY_CFG_SHADOWED`](#entropy_cfg_shadowed) register can be updated by software (1) or not (0).
If [`ENTROPY_CFG_LOCK`](#entropy_cfg_lock) is 1, this bit reads as 0.
This bit also reads 0 if the internal PRNG is currently being reseeded or if the Keccak core is operating as indicated in the [`STATUS`](#status) register.

## ENTROPY_CFG_SHADOWED
Entropy Configuration register.

This register can only be updated when the Keccak core is idle and if write access has not yet been locked down.
This is indicated by [`ENTROPY_CFG_REGWEN`](#entropy_cfg_regwen) reading as 1.
If [`ENTROPY_CFG_REGWEN`](#entropy_cfg_regwen) reads as 0 (meaning the Keccak core is busy and/or write access has been locked down), writes to this register are ignored.

If masking is disabled, only the Entropy Boot Mode field of this register is relevant and the remaining fields are ignored.
- Offset: `0x28`
- Reset default: `0x1`
- Reset mask: `0x3ff0007`
- Register enable: [`ENTROPY_CFG_REGWEN`](#entropy_cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "entropy_boot_mode", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "entropy_mode", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ignore_cmd_entropy_req", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 13}, {"name": "edn_mode_refresh_threshold", "bits": 10, "attr": ["rw"], "rotate": -90}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 280}}
```

|  Bits  |  Type  |  Reset  | Name                                                                            |
|:------:|:------:|:-------:|:--------------------------------------------------------------------------------|
| 31:26  |        |         | Reserved                                                                        |
| 25:16  |   rw   |   0x0   | [edn_mode_refresh_threshold](#entropy_cfg_shadowed--edn_mode_refresh_threshold) |
|  15:3  |        |         | Reserved                                                                        |
|   2    |   rw   |   0x0   | [ignore_cmd_entropy_req](#entropy_cfg_shadowed--ignore_cmd_entropy_req)         |
|   1    |   rw   |   0x0   | [entropy_mode](#entropy_cfg_shadowed--entropy_mode)                             |
|   0    |  rw0c  |   0x1   | [entropy_boot_mode](#entropy_cfg_shadowed--entropy_boot_mode)                   |

### ENTROPY_CFG_SHADOWED . edn_mode_refresh_threshold
EDN Mode Refresh Threshold

The number of KMAC messages after which the module automatically triggers a reseed operation when running in EDN Mode.
Note that the automatic reseed operation is not triggered when ending the message processing, but after processing the KMAC key block.
If an automatic reseed operation is triggered, the Keccak core can continue processing the message in parallel to the reseed operation.

If this field reads as 0, no automatic reseed operations are triggered in EDN Mode.

### ENTROPY_CFG_SHADOWED . ignore_cmd_entropy_req
If this bit is set, writes to [`CMD.entropy_req`](#cmd) are ignored.
This can be useful for locking down the PRNG configuration and prevent further reseed operations, e.g., if later software stages aren't trusted.

### ENTROPY_CFG_SHADOWED . entropy_mode
Entropy Mode

Using this field, software can configure the non-boot mode of operation of the internal pseudo-random number generator (PRNG).

The value of this field is only relevant if [`ENTROPY_CFG.entropy_boot_mode`](#entropy_cfg) reads as 0.

| Value   | Name     | Description                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
|:--------|:---------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0x0     | edn_mode | Receive fresh entropy from EDN for reseeding the internal PRNG. This entropy mode is to be used for regular operation. When this mode is activated first after reset, the [`STATUS.entropy_reseeding`](#status) bit is set to 1 and the module requests fresh entropy from EDN for reseeding the internal PRNG. Once the reseed operation finishes, the [`STATUS.entropy_ready`](#status) bit is set to 1 and the module can start processing commands. Depending on [`CFG_SHADOWED`](#cfg_shadowed), the internal PRNG is then used for (re-)masking inputs (prefix, key, message) and intermediate results of the Keccak core. The module will then automatically reseed the internal PRNG with fresh entropy from EDN every [`ENTROPY_CFG_SHADOWED.edn_mode_refresh_threshold`](#entropy_cfg_shadowed) messages in KMAC mode. More precisely, automatic reseed operations are always triggered directly after the key absorption phase. How close the module is to automatically trigger a reseed operation can be inferred from [`ENTROPY_REFRESH_HASH_CNT.`](#entropy_refresh_hash_cnt) Alternatively, software can manually initiate reseeding operations using [`CMD.entropy_req`](#cmd) while the module is idle. This will also clear [`ENTROPY_REFRESH_HASH_CNT.`](#entropy_refresh_hash_cnt) Depending on the state of the system, it may take a very long or even indefinite time for the entropy to be delivered. For guidance, refer to [EDN Entropy Mode](programmers_guide.md#edn-entropy-mode). To change from this mode to `sw_mode`, software has to first configure the mode and then trigger a reseed operation using [`CMD.entropy_req.`](#cmd) |
| 0x1     | sw_mode  | Receive entropy from software for reseeding the internal PRNG. This entropy mode is a fall-back option to be used if the entropy complex is not available. When this mode is activated first after reset, the [`STATUS.entropy_reseeding`](#status) bit is set to 1 and the module waits for software to write the [`ENTROPY_SEED`](#entropy_seed) register 6 times. Upon each write, the written value is loaded into the corresponding state chunk of the PRNG. After the last write operation, the [`STATUS.entropy_ready`](#status) bit is set to 1 and the module can start processing commands. Depending on [`CFG_SHADOWED`](#cfg_shadowed), the internal PRNG is then used for (re-)masking inputs (prefix, key, message) and intermediate results of the Keccak core. After this point, software can manually initiate reseeding operations using [`CMD.entropy_req`](#cmd) while the module is idle. This will also clear [`ENTROPY_REFRESH_HASH_CNT.`](#entropy_refresh_hash_cnt) To change from this mode to `edn_mode`, software has to first configure the mode and then trigger a reseed operation using [`CMD.entropy_req.`](#cmd)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |


### ENTROPY_CFG_SHADOWED . entropy_boot_mode
Entropy Boot Mode

If this field reads 1, the internal pseudo-random number generator (PRNG) is operating in boot mode irrespective of the value of [`ENTROPY_CFG.entropy_mode.`](#entropy_cfg)
The sole purpose of the Entropy Boot Mode is to enable the initial ROM_CTRL operation right after coming out of reset.

In this mode, the internal PRNG is not reseeded with fresh entropy, nor updated while the Keccak core operates.
It should therefore not be used after this very initial boot phase and software should disable the Entropy Boot Mode and configure the desired [`ENTROPY_CFG.entropy_mode`](#entropy_cfg) value as early as possible.

## ENTROPY_SEED
Entropy Seed

Entropy seed register for the internal PRNG.

If [`ENTROPY_CFG_SHADOWED.entropy_boot_mode`](#entropy_cfg_shadowed) reads 0, if [`ENTROPY_CFG_SHADOWED.entropy_mode`](#entropy_cfg_shadowed) is set to `sw_mode`, and if [`STATUS.entropy_reseeding`](#status) reads 1, software can write this register 6 times.
Upon each write, the written value is loaded into the corresponding state chunk of the internal PRNG.

After writing the register 6 times, the [`STATUS.entropy_reseeding`](#status) bit drops to 0, the PRNG is ready to deliver randomness to the Keccak core which is indicated by the [`STATUS.entropy_ready`](#status) bit being set.
After this point, another reseed operation can be initiated via [`CMD.entropy_req.`](#cmd)
- Offset: `0x2c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "seed", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                |
|:------:|:------:|:-------:|:-------|:-------------------------------------------|
|  31:0  |   wo   |    x    | seed   | 32-bit chunk of the entropy generator seed |

## ENTROPY_REFRESH_HASH_CNT
Entropy Refresh Counter

KMAC entropy can be refreshed after the given threshold KMAC operations
run. If the KMAC hash counter [`ENTROPY_REFRESH_HASH_CNT`](#entropy_refresh_hash_cnt) hits (GTE) the
configured threshold [`ENTROPY_CFG_SHADOWED.edn_mode_refresh_threshold`](#entropy_cfg_shadowed), the entropy
module in the KMAC IP requests new seed to EDN and reset the KMAC
hash counter.

If the threshold is 0, the refresh by the counter does not work. And the
counter is only reset by the CMD.hash_cnt_clr CSR bit.
- Offset: `0x30`
- Reset default: `0x0`
- Reset mask: `0x3ff`

### Fields

```wavejson
{"reg": [{"name": "hash_cnt", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 22}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description         |
|:------:|:------:|:-------:|:---------|:--------------------|
| 31:10  |        |         |          | Reserved            |
|  9:0   |   ro   |   0x0   | hash_cnt | Hash (KMAC) counter |

## KEY_SHARE0
KMAC Secret Key

KMAC secret key can be up to 512 bit.
Order of the secret key is:
key[512:0] = {KEY15, KEY14, ... , KEY0};

The registers are allowed to be updated when the engine is in Idle state.
If the engine computes the hash, it discards any attempts to update the secret keys
and report an error.

Current KMAC supports up to 512 bit secret key. It is the sw
responsibility to keep upper bits of the secret key to 0.
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Instances

| Name          | Offset   |
|:--------------|:---------|
| KEY_SHARE0_0  | 0x34     |
| KEY_SHARE0_1  | 0x38     |
| KEY_SHARE0_2  | 0x3c     |
| KEY_SHARE0_3  | 0x40     |
| KEY_SHARE0_4  | 0x44     |
| KEY_SHARE0_5  | 0x48     |
| KEY_SHARE0_6  | 0x4c     |
| KEY_SHARE0_7  | 0x50     |
| KEY_SHARE0_8  | 0x54     |
| KEY_SHARE0_9  | 0x58     |
| KEY_SHARE0_10 | 0x5c     |
| KEY_SHARE0_11 | 0x60     |
| KEY_SHARE0_12 | 0x64     |
| KEY_SHARE0_13 | 0x68     |
| KEY_SHARE0_14 | 0x6c     |
| KEY_SHARE0_15 | 0x70     |


### Fields

```wavejson
{"reg": [{"name": "key", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                              |
|:------:|:------:|:-------:|:-------|:-----------------------------------------|
|  31:0  |   wo   |    x    | key    | 32-bit chunk of up-to 512-bit Secret Key |

## KEY_SHARE1
KMAC Secret Key, 2nd share.

KMAC secret key can be up to 512 bit.
Order of the secret key is:
key[512:0] = {KEY15, KEY14, ... , KEY0};

The registers are allowed to be updated when the engine is in Idle state.
If the engine computes the hash, it discards any attempts to update the secret keys
and report an error.

Current KMAC supports up to 512 bit secret key. It is the sw
responsibility to keep upper bits of the secret key to 0.
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Instances

| Name          | Offset   |
|:--------------|:---------|
| KEY_SHARE1_0  | 0x74     |
| KEY_SHARE1_1  | 0x78     |
| KEY_SHARE1_2  | 0x7c     |
| KEY_SHARE1_3  | 0x80     |
| KEY_SHARE1_4  | 0x84     |
| KEY_SHARE1_5  | 0x88     |
| KEY_SHARE1_6  | 0x8c     |
| KEY_SHARE1_7  | 0x90     |
| KEY_SHARE1_8  | 0x94     |
| KEY_SHARE1_9  | 0x98     |
| KEY_SHARE1_10 | 0x9c     |
| KEY_SHARE1_11 | 0xa0     |
| KEY_SHARE1_12 | 0xa4     |
| KEY_SHARE1_13 | 0xa8     |
| KEY_SHARE1_14 | 0xac     |
| KEY_SHARE1_15 | 0xb0     |


### Fields

```wavejson
{"reg": [{"name": "key", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                              |
|:------:|:------:|:-------:|:-------|:-----------------------------------------|
|  31:0  |   wo   |    x    | key    | 32-bit chunk of up-to 512-bit Secret Key |

## KEY_LEN
Secret Key length in bit.

This value is used to make encoded secret key in KMAC.
KMAC supports certain lengths of the secret key. Currently it
supports 128b, 192b, 256b, 384b, and 512b secret keys.
- Offset: `0xb4`
- Reset default: `0x0`
- Reset mask: `0x7`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "len", "bits": 3, "attr": ["wo"], "rotate": 0}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                 |
|:------:|:------:|:-------:|:---------------------|
|  31:3  |        |         | Reserved             |
|  2:0   |   wo   |   0x0   | [len](#key_len--len) |

### KEY_LEN . len
Key length choice

| Value   | Name   | Description            |
|:--------|:-------|:-----------------------|
| 0x0     | Key128 | Key length is 128 bit. |
| 0x1     | Key192 | Key length is 192 bit. |
| 0x2     | Key256 | Key length is 256 bit. |
| 0x3     | Key384 | Key length is 384 bit. |
| 0x4     | Key512 | Key length is 512 bit. |

Other values are reserved.

## PREFIX
cSHAKE Prefix register.

Prefix including Function Name N and Customization String S.
The SHA3 assumes this register value is encoded as:
`encode_string(N) || encode_string(S) || 0`. It means that the
software can freely decide the length of N or S based on the
given Prefix register size 320bit. 320bit is determined to have
32-bit of N and up to 256-bit of S + encode of their length.

It is SW responsibility to fill the register with encoded value
that is described at Section 2.3.2 String Encoding in NIST SP
800-185 specification.

Order of Prefix is:
prefix[end:0] := {PREFIX(N-1), ..., PREFIX(1), PREFIX(0) }

The registers are allowed to be updated when the engine is in Idle state.
If the engine computes the hash, it discards any attempts to update the secret keys
and report an error.
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Instances

| Name      | Offset   |
|:----------|:---------|
| PREFIX_0  | 0xb8     |
| PREFIX_1  | 0xbc     |
| PREFIX_2  | 0xc0     |
| PREFIX_3  | 0xc4     |
| PREFIX_4  | 0xc8     |
| PREFIX_5  | 0xcc     |
| PREFIX_6  | 0xd0     |
| PREFIX_7  | 0xd4     |
| PREFIX_8  | 0xd8     |
| PREFIX_9  | 0xdc     |
| PREFIX_10 | 0xe0     |


### Fields

```wavejson
{"reg": [{"name": "prefix", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                       |
|:------:|:------:|:-------:|:-------|:----------------------------------|
|  31:0  |   rw   |   0x0   | prefix | 32-bit chunk of Encoded NS Prefix |

## ERR_CODE
KMAC/SHA3 Error Code
- Offset: `0xe4`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "err_code", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                            |
|:------:|:------:|:-------:|:--------------------------------|
|  31:0  |   ro   |   0x0   | [err_code](#err_code--err_code) |

### ERR_CODE . err_code
If the `kmac_err` interrupt occurs, this register has information on the error cause.
Bits 31:24 contain the error code (please refer to `err_code_e` in `hw/ip/kmac/rtl/kmac_pkg.sv`) for the encoding, and bits 23:0 contain additional debug information.
This register does *not* get cleared when the `kmac_err` interrupt state gets cleared.

## STATE
Keccak State (1600 bit) memory.

The software can get the processed digest by reading this memory
region. Unlike MSG_FIFO, STATE memory space sees the addr[9:0].
If Masking feature is enabled, the software reads two shares from
this memory space.

Software can write to the register to restore a previously saved
context. Writes are only accepted once software claimed the KMAC
HWIP with the `state_write` command and while the hashing engine
is idle, which [`STATUS.state_write`](#status) reports. Writes at any other
time are acknowledged on the bus and ignored.

Writes must be full 32-bit word writes. Sub-word writes are
answered with a bus error, as a partial write cannot be applied
to the Keccak state.

0x400 - 0x4C7: State share
0x500 - 0x5C7: Mask share of the state, 0 if EnMasking = 0

- Word Aligned Offset Range: `0x400`to`0x5fc`
- Size (words): `128`
- Access: `rw`
- Byte writes are *not* supported.

## MSG_FIFO
Message FIFO.

Any write operation to this window will be appended to MSG_FIFO. SW can
simply write bytes/words to any address within this address range.
Ordering and packing of the incoming bytes/words are handled
internally. Therefore, the least significant 12 bits of the address
are ignored.

- Word Aligned Offset Range: `0x800`to`0xffc`
- Size (words): `512`
- Access: `wo`
- Byte writes are  supported.


<!-- END CMDGEN -->
