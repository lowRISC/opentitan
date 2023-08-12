# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/kmac/data/kmac.hjson -->
## Summary

| Name                                                                             | Offset   |   Length | Description                                              |
|:---------------------------------------------------------------------------------|:---------|---------:|:---------------------------------------------------------|
| kmac.[`INTR_STATE`](#intr_state)                                                 | 0x0      |        4 | Interrupt State Register                                 |
| kmac.[`INTR_ENABLE`](#intr_enable)                                               | 0x4      |        4 | Interrupt Enable Register                                |
| kmac.[`INTR_TEST`](#intr_test)                                                   | 0x8      |        4 | Interrupt Test Register                                  |
| kmac.[`ALERT_TEST`](#alert_test)                                                 | 0xc      |        4 | Alert Test Register                                      |
| kmac.[`CFG_REGWEN`](#cfg_regwen)                                                 | 0x10     |        4 | Controls the configurability of !!CFG_SHADOWED register. |
| kmac.[`CFG_SHADOWED`](#cfg_shadowed)                                             | 0x14     |        4 | KMAC Configuration register.                             |
| kmac.[`CMD`](#cmd)                                                               | 0x18     |        4 | KMAC/ SHA3 command register.                             |
| kmac.[`STATUS`](#status)                                                         | 0x1c     |        4 | KMAC/SHA3 Status register.                               |
| kmac.[`ENTROPY_PERIOD`](#entropy_period)                                         | 0x20     |        4 | Entropy Timer Periods.                                   |
| kmac.[`ENTROPY_REFRESH_HASH_CNT`](#entropy_refresh_hash_cnt)                     | 0x24     |        4 | Entropy Refresh Counter                                  |
| kmac.[`ENTROPY_REFRESH_THRESHOLD_SHADOWED`](#entropy_refresh_threshold_shadowed) | 0x28     |        4 | Entropy Refresh Threshold                                |
| kmac.[`ENTROPY_SEED_0`](#entropy_seed)                                           | 0x2c     |        4 | Entropy Seed                                             |
| kmac.[`ENTROPY_SEED_1`](#entropy_seed)                                           | 0x30     |        4 | Entropy Seed                                             |
| kmac.[`ENTROPY_SEED_2`](#entropy_seed)                                           | 0x34     |        4 | Entropy Seed                                             |
| kmac.[`ENTROPY_SEED_3`](#entropy_seed)                                           | 0x38     |        4 | Entropy Seed                                             |
| kmac.[`ENTROPY_SEED_4`](#entropy_seed)                                           | 0x3c     |        4 | Entropy Seed                                             |
| kmac.[`KEY_SHARE0_0`](#key_share0)                                               | 0x40     |        4 | KMAC Secret Key                                          |
| kmac.[`KEY_SHARE0_1`](#key_share0)                                               | 0x44     |        4 | KMAC Secret Key                                          |
| kmac.[`KEY_SHARE0_2`](#key_share0)                                               | 0x48     |        4 | KMAC Secret Key                                          |
| kmac.[`KEY_SHARE0_3`](#key_share0)                                               | 0x4c     |        4 | KMAC Secret Key                                          |
| kmac.[`KEY_SHARE0_4`](#key_share0)                                               | 0x50     |        4 | KMAC Secret Key                                          |
| kmac.[`KEY_SHARE0_5`](#key_share0)                                               | 0x54     |        4 | KMAC Secret Key                                          |
| kmac.[`KEY_SHARE0_6`](#key_share0)                                               | 0x58     |        4 | KMAC Secret Key                                          |
| kmac.[`KEY_SHARE0_7`](#key_share0)                                               | 0x5c     |        4 | KMAC Secret Key                                          |
| kmac.[`KEY_SHARE0_8`](#key_share0)                                               | 0x60     |        4 | KMAC Secret Key                                          |
| kmac.[`KEY_SHARE0_9`](#key_share0)                                               | 0x64     |        4 | KMAC Secret Key                                          |
| kmac.[`KEY_SHARE0_10`](#key_share0)                                              | 0x68     |        4 | KMAC Secret Key                                          |
| kmac.[`KEY_SHARE0_11`](#key_share0)                                              | 0x6c     |        4 | KMAC Secret Key                                          |
| kmac.[`KEY_SHARE0_12`](#key_share0)                                              | 0x70     |        4 | KMAC Secret Key                                          |
| kmac.[`KEY_SHARE0_13`](#key_share0)                                              | 0x74     |        4 | KMAC Secret Key                                          |
| kmac.[`KEY_SHARE0_14`](#key_share0)                                              | 0x78     |        4 | KMAC Secret Key                                          |
| kmac.[`KEY_SHARE0_15`](#key_share0)                                              | 0x7c     |        4 | KMAC Secret Key                                          |
| kmac.[`KEY_SHARE1_0`](#key_share1)                                               | 0x80     |        4 | KMAC Secret Key, 2nd share.                              |
| kmac.[`KEY_SHARE1_1`](#key_share1)                                               | 0x84     |        4 | KMAC Secret Key, 2nd share.                              |
| kmac.[`KEY_SHARE1_2`](#key_share1)                                               | 0x88     |        4 | KMAC Secret Key, 2nd share.                              |
| kmac.[`KEY_SHARE1_3`](#key_share1)                                               | 0x8c     |        4 | KMAC Secret Key, 2nd share.                              |
| kmac.[`KEY_SHARE1_4`](#key_share1)                                               | 0x90     |        4 | KMAC Secret Key, 2nd share.                              |
| kmac.[`KEY_SHARE1_5`](#key_share1)                                               | 0x94     |        4 | KMAC Secret Key, 2nd share.                              |
| kmac.[`KEY_SHARE1_6`](#key_share1)                                               | 0x98     |        4 | KMAC Secret Key, 2nd share.                              |
| kmac.[`KEY_SHARE1_7`](#key_share1)                                               | 0x9c     |        4 | KMAC Secret Key, 2nd share.                              |
| kmac.[`KEY_SHARE1_8`](#key_share1)                                               | 0xa0     |        4 | KMAC Secret Key, 2nd share.                              |
| kmac.[`KEY_SHARE1_9`](#key_share1)                                               | 0xa4     |        4 | KMAC Secret Key, 2nd share.                              |
| kmac.[`KEY_SHARE1_10`](#key_share1)                                              | 0xa8     |        4 | KMAC Secret Key, 2nd share.                              |
| kmac.[`KEY_SHARE1_11`](#key_share1)                                              | 0xac     |        4 | KMAC Secret Key, 2nd share.                              |
| kmac.[`KEY_SHARE1_12`](#key_share1)                                              | 0xb0     |        4 | KMAC Secret Key, 2nd share.                              |
| kmac.[`KEY_SHARE1_13`](#key_share1)                                              | 0xb4     |        4 | KMAC Secret Key, 2nd share.                              |
| kmac.[`KEY_SHARE1_14`](#key_share1)                                              | 0xb8     |        4 | KMAC Secret Key, 2nd share.                              |
| kmac.[`KEY_SHARE1_15`](#key_share1)                                              | 0xbc     |        4 | KMAC Secret Key, 2nd share.                              |
| kmac.[`KEY_LEN`](#key_len)                                                       | 0xc0     |        4 | Secret Key length in bit.                                |
| kmac.[`PREFIX_0`](#prefix)                                                       | 0xc4     |        4 | cSHAKE Prefix register.                                  |
| kmac.[`PREFIX_1`](#prefix)                                                       | 0xc8     |        4 | cSHAKE Prefix register.                                  |
| kmac.[`PREFIX_2`](#prefix)                                                       | 0xcc     |        4 | cSHAKE Prefix register.                                  |
| kmac.[`PREFIX_3`](#prefix)                                                       | 0xd0     |        4 | cSHAKE Prefix register.                                  |
| kmac.[`PREFIX_4`](#prefix)                                                       | 0xd4     |        4 | cSHAKE Prefix register.                                  |
| kmac.[`PREFIX_5`](#prefix)                                                       | 0xd8     |        4 | cSHAKE Prefix register.                                  |
| kmac.[`PREFIX_6`](#prefix)                                                       | 0xdc     |        4 | cSHAKE Prefix register.                                  |
| kmac.[`PREFIX_7`](#prefix)                                                       | 0xe0     |        4 | cSHAKE Prefix register.                                  |
| kmac.[`PREFIX_8`](#prefix)                                                       | 0xe4     |        4 | cSHAKE Prefix register.                                  |
| kmac.[`PREFIX_9`](#prefix)                                                       | 0xe8     |        4 | cSHAKE Prefix register.                                  |
| kmac.[`PREFIX_10`](#prefix)                                                      | 0xec     |        4 | cSHAKE Prefix register.                                  |
| kmac.[`ERR_CODE`](#err_code)                                                     | 0xf0     |        4 | KMAC/SHA3 Error Code                                     |
| kmac.[`STATE`](#state)                                                           | 0x400    |      512 | Keccak State (1600 bit) memory.                          |
| kmac.[`MSG_FIFO`](#msg_fifo)                                                     | 0x800    |     2048 | Message FIFO.                                            |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "kmac_done", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "fifo_empty", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "kmac_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                   |
|:------:|:------:|:-------:|:-----------|:--------------------------------------------------------------|
|  31:3  |        |         |            | Reserved                                                      |
|   2    |  rw1c  |   0x0   | kmac_err   | KMAC/SHA3 error occurred. ERR_CODE register shows the details |
|   1    |  rw1c  |   0x0   | fifo_empty | Message FIFO empty condition                                  |
|   0    |  rw1c  |   0x0   | kmac_done  | KMAC/SHA3 absorbing has been completed                        |

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
Controls the configurability of [`CFG_SHADOWED`](#cfg_shadowed) register.

This register ensures the contents of [`CFG_SHADOWED`](#cfg_shadowed) register cannot be
changed by the software while the KMAC/SHA3 is in operation mode.
- Offset: `0x10`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "en", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description           |
|:------:|:------:|:-------:|:-------|:----------------------|
|  31:1  |        |         |        | Reserved              |
|   0    |   ro   |   0x1   | en     | Configuration enable. |

## CFG_SHADOWED
KMAC Configuration register.

This register is  updated when the hashing engine is in Idle.
If the software updates the register while the engine computes, the
updated value will be discarded.
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0x71b133f`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "kmac_en", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "kstrength", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "mode", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 2}, {"name": "msg_endianness", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "state_endianness", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 2}, {"name": "sideload", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 3}, {"name": "entropy_mode", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 1}, {"name": "entropy_fast_process", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "msg_mask", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 3}, {"name": "entropy_ready", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "err_processed", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "en_unsupported_modestrength", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 5}], "config": {"lanes": 1, "fontsize": 10, "vspace": 290}}
```

|  Bits  |  Type  |  Reset  | Name                                                                      |
|:------:|:------:|:-------:|:--------------------------------------------------------------------------|
| 31:27  |        |         | Reserved                                                                  |
|   26   |   rw   |   0x0   | [en_unsupported_modestrength](#cfg_shadowed--en_unsupported_modestrength) |
|   25   |   rw   |   0x0   | [err_processed](#cfg_shadowed--err_processed)                             |
|   24   |   rw   |   0x0   | [entropy_ready](#cfg_shadowed--entropy_ready)                             |
| 23:21  |        |         | Reserved                                                                  |
|   20   |   rw   |   0x0   | [msg_mask](#cfg_shadowed--msg_mask)                                       |
|   19   |   rw   |   0x0   | [entropy_fast_process](#cfg_shadowed--entropy_fast_process)               |
|   18   |        |         | Reserved                                                                  |
| 17:16  |   rw   |   0x0   | [entropy_mode](#cfg_shadowed--entropy_mode)                               |
| 15:13  |        |         | Reserved                                                                  |
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

### CFG_SHADOWED . err_processed
When error occurs and one of the state machine stays at
 Error handling state, SW may process the error based on
 ERR_CODE, then let FSM back to the reset state

### CFG_SHADOWED . entropy_ready
Entropy Ready status.

Software sets this field to allow the entropy generator in KMAC to
fetch the entropy and run.

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

### CFG_SHADOWED . entropy_mode
Entropy Mode

Using this field, software can configure mode of operation of the internal pseudo-random number generator (PRNG).
For the hardware to actually switch to an entropy mode other than the default idle_mode, software further needs to set the [`CFG_SHADOWED.entropy_ready`](#cfg_shadowed) bit.
After that point, the hardware cannot be made to return to idle_mode unless the module is reset.

| Value   | Name      | Description                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
|:--------|:----------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0x0     | idle_mode | Default mode after reset.  The sole purpose of this mode is to enable ROM_CTRL operation right after coming out of reset.  The internal PRNG is not reseeded with fresh entropy, nor updated while the core operates. It should therefore not be used after this very initial stage. Software should setup a different mode and set !!CFG_SHADOWED.entropy_ready as early as possible.  The module cannot be made to return to idle_mode once any of the other modes have been used.                                                                                                                                                                                                                                                                                       |
| 0x1     | edn_mode  | Receive fresh entropy from EDN for reseeding the internal PRNG.  This entropy mode is to be used for regular operation.  Once the !!CFG_SHADOWED.entropy_ready bit is set after reset, the module requests fresh entropy from EDN for reseeding the internal PRNG. Only after that, the module can start processing commands. Depending on !!CFG_SHADOWED, the internal PRNG is then used for (re-)masking inputs (prefix, key, message) and intermediate results of the Keccak core.  Depending on !!ENTROPY_PERIOD, the module will periodically reseed the internal PRNG with fresh entropy from EDN. Using !!CMD.entropy_req software can manually initiate the reseeding.                                                                                             |
| 0x2     | sw_mode   | Receive initial entropy from software for reseeding the internal PRNG.  This entropy mode is a fall-back option to be used if the entropy complex is not available.  Once the !!CFG_SHADOWED.entropy_ready bit is set after reset, the module will wait for software to write each of the !!ENTROPY_SEED_0 - !!ENTROPY_SEED_4 registers exactly once and in ascending order. Only after that, the module can start processing commands. Depending on !!CFG_SHADOWED, the internal PRNG is then used for (re-)masking inputs (prefix, key, message) and intermediate results of the Keccak core.  After this point, the PRNG can no longer be reseeded by software - also after switching back into this mode from edn_mode. However, it is possible to switch to edn_mode. |

Other values are reserved.

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

If this bit is 1, the incoming message is processed in KMAC
with the secret key.

## CMD
KMAC/ SHA3 command register.

This register is to control the KMAC to start accepting message,
to process the message, and to manually run additional keccak
rounds at the end. Only at certain stage, the CMD affects to the
control logic. It follows the sequence of

`start` --> `process` --> {`run` if needed --> } `done`
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0x33f`

### Fields

```wavejson
{"reg": [{"name": "cmd", "bits": 6, "attr": ["r0w1c"], "rotate": 0}, {"bits": 2}, {"name": "entropy_req", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"name": "hash_cnt_clr", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"bits": 22}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name                               |
|:------:|:------:|:-------:|:-----------------------------------|
| 31:10  |        |         | Reserved                           |
|   9    | r0w1c  |    x    | [hash_cnt_clr](#cmd--hash_cnt_clr) |
|   8    | r0w1c  |    x    | [entropy_req](#cmd--entropy_req)   |
|  7:6   |        |         | Reserved                           |
|  5:0   | r0w1c  |    x    | [cmd](#cmd--cmd)                   |

### CMD . hash_cnt_clr
If writes 1, it clears the hash (KMAC) counter in the entropy module

### CMD . entropy_req
SW triggered Entropy Request

If writes 1 to this field

### CMD . cmd
Issue a command to the KMAC/SHA3 IP. The command is sparse
encoded. To prevent sw from writing multiple commands at once,
the field is defined as enum.

| Value   | Name    | Description                                                                                                                                                                                                                                                                                                                  |
|:--------|:--------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0x1d    | start   | Writing 6'b011101 or dec 29 into this field when KMAC/SHA3 is in idle, KMAC/SHA3 begins its operation.  If the mode is cSHAKE, before receiving the message, the hashing logic processes Function name string N and customization input string S first. If KMAC mode is enabled, additionally it processes secret key block. |
| 0x2e    | process | Writing 6'b101110 or dec 46 into this field when KMAC/SHA3 began its operation and received the entire message, it computes the digest or signing.                                                                                                                                                                           |
| 0x31    | run     | The `run` field is used in the sponge squeezing stage. It triggers the keccak round logic to run full 24 rounds. This is optional and used when software needs more digest bits than the keccak rate.  It only affects when the kmac/sha3 operation is completed.                                                            |
| 0x16    | done    | Writing 6'b010110 or dec 22 into this field when KMAC/SHA3 squeezing is completed, KMAC/SHA3 hashing engine clears internal variables and goes back to Idle state for next command.                                                                                                                                          |

Other values are reserved.

## STATUS
KMAC/SHA3 Status register.
- Offset: `0x1c`
- Reset default: `0x4001`
- Reset mask: `0x3df07`

### Fields

```wavejson
{"reg": [{"name": "sha3_idle", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "sha3_absorb", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "sha3_squeeze", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 5}, {"name": "fifo_depth", "bits": 5, "attr": ["ro"], "rotate": -90}, {"bits": 1}, {"name": "fifo_empty", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "fifo_full", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ALERT_FATAL_FAULT", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ALERT_RECOV_CTRL_UPDATE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 14}], "config": {"lanes": 1, "fontsize": 10, "vspace": 290}}
```

|  Bits  |  Type  |  Reset  | Name                                                                |
|:------:|:------:|:-------:|:--------------------------------------------------------------------|
| 31:18  |        |         | Reserved                                                            |
|   17   |   ro   |   0x0   | [ALERT_RECOV_CTRL_UPDATE_ERR](#status--alert_recov_ctrl_update_err) |
|   16   |   ro   |   0x0   | [ALERT_FATAL_FAULT](#status--alert_fatal_fault)                     |
|   15   |   ro   |    x    | [fifo_full](#status--fifo_full)                                     |
|   14   |   ro   |   0x1   | [fifo_empty](#status--fifo_empty)                                   |
|   13   |        |         | Reserved                                                            |
|  12:8  |   ro   |    x    | [fifo_depth](#status--fifo_depth)                                   |
|  7:3   |        |         | Reserved                                                            |
|   2    |   ro   |    x    | [sha3_squeeze](#status--sha3_squeeze)                               |
|   1    |   ro   |    x    | [sha3_absorb](#status--sha3_absorb)                                 |
|   0    |   ro   |   0x1   | [sha3_idle](#status--sha3_idle)                                     |

### STATUS . ALERT_RECOV_CTRL_UPDATE_ERR
An update error has not occurred (0) or has occured (1) in the shadowed Control Register.
KMAC operation needs to be restarted by re-writing the Control Register.

### STATUS . ALERT_FATAL_FAULT
No fatal fault has occurred inside the KMAC unit (0).
A fatal fault has occured and the KMAC unit needs to be reset (1),
Examples for such faults include
i) TL-UL bus integrity fault
ii) storage errors in the shadow registers
iii) errors in the message, round, or key counter
iv) any internal FSM entering an invalid state
v) an error in the redundant lfsr

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

### STATUS . sha3_squeeze
If 1, SHA3 completes sponge absorbing stage.
In this stage, SW can manually run the hashing engine.

### STATUS . sha3_absorb
If 1, SHA3 is receiving message stream and processing it

### STATUS . sha3_idle
If 1, SHA3 hashing engine is in idle state.

## ENTROPY_PERIOD
Entropy Timer Periods.
- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0xffff03ff`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "prescaler", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}, {"name": "wait_timer", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                      |
|:------:|:------:|:-------:|:------------------------------------------|
| 31:16  |   rw   |   0x0   | [wait_timer](#entropy_period--wait_timer) |
| 15:10  |        |         | Reserved                                  |
|  9:0   |   rw   |   0x0   | [prescaler](#entropy_period--prescaler)   |

### ENTROPY_PERIOD . wait_timer
EDN request wait timer.

The entropy module in KMAC waits up to this field in the timer pulse
after it sends request to EDN module. If the timer expires, the
entropy module moves to an error state and notifies to the system.

If there is a pending EDN request during wait timer update, then this update is delayed until the EDN request is complete.

If 0, the entropy module waits the EDN response always. If EDN does
not respond in this configuration, the software shall reset the IP.

### ENTROPY_PERIOD . prescaler
EDN Wait timer prescaler.

EDN Wait timer has 16 bit value. The timer value is increased when the timer pulse is generated. Timer pulse is raises when the number of the clock cycles hit this prescaler value.

The exact period of the timer pulse is unknown as the KMAC input clock may contain jitters.

## ENTROPY_REFRESH_HASH_CNT
Entropy Refresh Counter

KMAC entropy can be refreshed after the given threshold KMAC operations
run. If the KMAC hash counter [`ENTROPY_REFRESH_HASH_CNT`](#entropy_refresh_hash_cnt) hits (GTE) the
configured threshold [`ENTROPY_REFRESH_THRESHOLD_SHADOWED`](#entropy_refresh_threshold_shadowed), the entropy
module in the KMAC IP requests new seed to EDN and reset the KMAC
hash counter.

If the threshold is 0, the refresh by the counter does not work. And the
counter is only reset by the CMD.hash_cnt_clr CSR bit.
- Offset: `0x24`
- Reset default: `0x0`
- Reset mask: `0x3ff`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "hash_cnt", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 22}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description         |
|:------:|:------:|:-------:|:---------|:--------------------|
| 31:10  |        |         |          | Reserved            |
|  9:0   |   ro   |   0x0   | hash_cnt | Hash (KMAC) counter |

## ENTROPY_REFRESH_THRESHOLD_SHADOWED
Entropy Refresh Threshold

KMAC entropy can be refreshed after the given threshold KMAC operations
run. If the KMAC hash counter [`ENTROPY_REFRESH_HASH_CNT`](#entropy_refresh_hash_cnt) hits (GTE) the
configured threshold [`ENTROPY_REFRESH_THRESHOLD_SHADOWED`](#entropy_refresh_threshold_shadowed), the entropy
module in the KMAC IP requests new seed to EDN and reset the KMAC
hash counter.

If the threshold is 0, the refresh by the counter does not work. And the
counter is only reset by the CMD.hash_cnt_clr CSR bit.
- Offset: `0x28`
- Reset default: `0x0`
- Reset mask: `0x3ff`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "threshold", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 22}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name      | Description    |
|:------:|:------:|:-------:|:----------|:---------------|
| 31:10  |        |         |           | Reserved       |
|  9:0   |   rw   |   0x0   | threshold | Hash Threshold |

## ENTROPY_SEED
Entropy Seed

Entropy seed registers for the integrated entropy generator.

If [`CFG_SHADOWED.entropy_mode`](#cfg_shadowed) is set to sw_mode, software first needs to set
[`CFG_SHADOWED.entropy_ready`](#cfg_shadowed) and then write the [`ENTROPY_SEED_0`](#entropy_seed_0) -
[`ENTROPY_SEED_4`](#entropy_seed_4) registers in ascending order. Software writes one 32-bit value
to every register which is subsequently loaded into the corresponding 32-bit LFSR
chunk of the entropy generator.

After writing all [`ENTROPY_SEED_0`](#entropy_seed_0) registers, the entropy generator will start
its operation. After this point, writing these registers has no longer any
effect.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name           | Offset   |
|:---------------|:---------|
| ENTROPY_SEED_0 | 0x2c     |
| ENTROPY_SEED_1 | 0x30     |
| ENTROPY_SEED_2 | 0x34     |
| ENTROPY_SEED_3 | 0x38     |
| ENTROPY_SEED_4 | 0x3c     |


### Fields

```wavejson
{"reg": [{"name": "seed", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                |
|:------:|:------:|:-------:|:-------|:-------------------------------------------|
|  31:0  |   wo   |    x    | seed   | 32-bit chunk of the entropy generator seed |

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

### Instances

| Name          | Offset   |
|:--------------|:---------|
| KEY_SHARE0_0  | 0x40     |
| KEY_SHARE0_1  | 0x44     |
| KEY_SHARE0_2  | 0x48     |
| KEY_SHARE0_3  | 0x4c     |
| KEY_SHARE0_4  | 0x50     |
| KEY_SHARE0_5  | 0x54     |
| KEY_SHARE0_6  | 0x58     |
| KEY_SHARE0_7  | 0x5c     |
| KEY_SHARE0_8  | 0x60     |
| KEY_SHARE0_9  | 0x64     |
| KEY_SHARE0_10 | 0x68     |
| KEY_SHARE0_11 | 0x6c     |
| KEY_SHARE0_12 | 0x70     |
| KEY_SHARE0_13 | 0x74     |
| KEY_SHARE0_14 | 0x78     |
| KEY_SHARE0_15 | 0x7c     |


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

### Instances

| Name          | Offset   |
|:--------------|:---------|
| KEY_SHARE1_0  | 0x80     |
| KEY_SHARE1_1  | 0x84     |
| KEY_SHARE1_2  | 0x88     |
| KEY_SHARE1_3  | 0x8c     |
| KEY_SHARE1_4  | 0x90     |
| KEY_SHARE1_5  | 0x94     |
| KEY_SHARE1_6  | 0x98     |
| KEY_SHARE1_7  | 0x9c     |
| KEY_SHARE1_8  | 0xa0     |
| KEY_SHARE1_9  | 0xa4     |
| KEY_SHARE1_10 | 0xa8     |
| KEY_SHARE1_11 | 0xac     |
| KEY_SHARE1_12 | 0xb0     |
| KEY_SHARE1_13 | 0xb4     |
| KEY_SHARE1_14 | 0xb8     |
| KEY_SHARE1_15 | 0xbc     |


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
- Offset: `0xc0`
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

### Instances

| Name      | Offset   |
|:----------|:---------|
| PREFIX_0  | 0xc4     |
| PREFIX_1  | 0xc8     |
| PREFIX_2  | 0xcc     |
| PREFIX_3  | 0xd0     |
| PREFIX_4  | 0xd4     |
| PREFIX_5  | 0xd8     |
| PREFIX_6  | 0xdc     |
| PREFIX_7  | 0xe0     |
| PREFIX_8  | 0xe4     |
| PREFIX_9  | 0xe8     |
| PREFIX_10 | 0xec     |


### Fields

```wavejson
{"reg": [{"name": "prefix", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                       |
|:------:|:------:|:-------:|:-------|:----------------------------------|
|  31:0  |   rw   |   0x0   | prefix | 32-bit chunk of Encoded NS Prefix |

## ERR_CODE
KMAC/SHA3 Error Code
- Offset: `0xf0`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "err_code", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                                                                                                      |
|:------:|:------:|:-------:|:---------|:-------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   ro   |   0x0   | err_code | If error interrupt occurs, this register has information of error cause. Please take a look at `hw/ip/kmac/rtl/kmac_pkg.sv:err_code_e enum type. |

## STATE
Keccak State (1600 bit) memory.

The software can get the processed digest by reading this memory
region. Unlike MSG_FIFO, STATE memory space sees the addr[9:0].
If Masking feature is enabled, the software reads two shares from
this memory space.

0x400 - 0x4C7: State share
0x500 - 0x5C7: Mask share of the state, 0 if EnMasking = 0

- Word Aligned Offset Range: `0x400`to`0x5fc`
- Size (words): `128`
- Access: `ro`
- Byte writes are *not* supported.

## MSG_FIFO
Message FIFO.

Any write to this window will be appended to the FIFO. Only lower
2 bits `[1:0]` of the address matter to writes within the window
in order to handle with sub-word writes.

- Word Aligned Offset Range: `0x800`to`0xffc`
- Size (words): `512`
- Access: `wo`
- Byte writes are  supported.


<!-- END CMDGEN -->
