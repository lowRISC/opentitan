# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/lc_ctrl/data/lc_ctrl.hjson -->
## Summary

| Name                                                                | Offset   |   Length | Description                                                                              |
|:--------------------------------------------------------------------|:---------|---------:|:-----------------------------------------------------------------------------------------|
| lc_ctrl.[`ALERT_TEST`](#alert_test)                                 | 0x0      |        4 | Alert Test Register                                                                      |
| lc_ctrl.[`STATUS`](#status)                                         | 0x4      |        4 | life cycle status register. Note that all errors are terminal and require a reset cycle. |
| lc_ctrl.[`CLAIM_TRANSITION_IF_REGWEN`](#claim_transition_if_regwen) | 0x8      |        4 | Register write enable for the hardware mutex register.                                   |
| lc_ctrl.[`CLAIM_TRANSITION_IF`](#claim_transition_if)               | 0xc      |        4 | Hardware mutex to claim exclusive access to the transition interface.                    |
| lc_ctrl.[`TRANSITION_REGWEN`](#transition_regwen)                   | 0x10     |        4 | Register write enable for all transition interface registers.                            |
| lc_ctrl.[`TRANSITION_CMD`](#transition_cmd)                         | 0x14     |        4 | Command register for state transition requests.                                          |
| lc_ctrl.[`TRANSITION_CTRL`](#transition_ctrl)                       | 0x18     |        4 | Control register for state transition requests.                                          |
| lc_ctrl.[`TRANSITION_TOKEN_0`](#transition_token)                   | 0x1c     |        4 | 128bit token for conditional transitions.                                                |
| lc_ctrl.[`TRANSITION_TOKEN_1`](#transition_token)                   | 0x20     |        4 | 128bit token for conditional transitions.                                                |
| lc_ctrl.[`TRANSITION_TOKEN_2`](#transition_token)                   | 0x24     |        4 | 128bit token for conditional transitions.                                                |
| lc_ctrl.[`TRANSITION_TOKEN_3`](#transition_token)                   | 0x28     |        4 | 128bit token for conditional transitions.                                                |
| lc_ctrl.[`TRANSITION_TARGET`](#transition_target)                   | 0x2c     |        4 | This register exposes the decoded life cycle state.                                      |
| lc_ctrl.[`OTP_VENDOR_TEST_CTRL`](#otp_vendor_test_ctrl)             | 0x30     |        4 | Test/vendor-specific settings for the OTP macro wrapper.                                 |
| lc_ctrl.[`OTP_VENDOR_TEST_STATUS`](#otp_vendor_test_status)         | 0x34     |        4 | Test/vendor-specific settings for the OTP macro wrapper.                                 |
| lc_ctrl.[`LC_STATE`](#lc_state)                                     | 0x38     |        4 | This register exposes the decoded life cycle state.                                      |
| lc_ctrl.[`LC_TRANSITION_CNT`](#lc_transition_cnt)                   | 0x3c     |        4 | This register exposes the state of the decoded life cycle transition counter.            |
| lc_ctrl.[`LC_ID_STATE`](#lc_id_state)                               | 0x40     |        4 | This register exposes the id state of the device.                                        |
| lc_ctrl.[`HW_REVISION0`](#hw_revision0)                             | 0x44     |        4 | This register holds the SILICON_CREATOR_ID and the PRODUCT_ID.                           |
| lc_ctrl.[`HW_REVISION1`](#hw_revision1)                             | 0x48     |        4 | This register holds the REVISION_ID.                                                     |
| lc_ctrl.[`DEVICE_ID_0`](#device_id)                                 | 0x4c     |        4 | This is the 256bit DEVICE_ID value that is stored in the HW_CFG partition in OTP.        |
| lc_ctrl.[`DEVICE_ID_1`](#device_id)                                 | 0x50     |        4 | This is the 256bit DEVICE_ID value that is stored in the HW_CFG partition in OTP.        |
| lc_ctrl.[`DEVICE_ID_2`](#device_id)                                 | 0x54     |        4 | This is the 256bit DEVICE_ID value that is stored in the HW_CFG partition in OTP.        |
| lc_ctrl.[`DEVICE_ID_3`](#device_id)                                 | 0x58     |        4 | This is the 256bit DEVICE_ID value that is stored in the HW_CFG partition in OTP.        |
| lc_ctrl.[`DEVICE_ID_4`](#device_id)                                 | 0x5c     |        4 | This is the 256bit DEVICE_ID value that is stored in the HW_CFG partition in OTP.        |
| lc_ctrl.[`DEVICE_ID_5`](#device_id)                                 | 0x60     |        4 | This is the 256bit DEVICE_ID value that is stored in the HW_CFG partition in OTP.        |
| lc_ctrl.[`DEVICE_ID_6`](#device_id)                                 | 0x64     |        4 | This is the 256bit DEVICE_ID value that is stored in the HW_CFG partition in OTP.        |
| lc_ctrl.[`DEVICE_ID_7`](#device_id)                                 | 0x68     |        4 | This is the 256bit DEVICE_ID value that is stored in the HW_CFG partition in OTP.        |
| lc_ctrl.[`MANUF_STATE_0`](#manuf_state)                             | 0x6c     |        4 | This is a 256bit field used for keeping track of the manufacturing state.                |
| lc_ctrl.[`MANUF_STATE_1`](#manuf_state)                             | 0x70     |        4 | This is a 256bit field used for keeping track of the manufacturing state.                |
| lc_ctrl.[`MANUF_STATE_2`](#manuf_state)                             | 0x74     |        4 | This is a 256bit field used for keeping track of the manufacturing state.                |
| lc_ctrl.[`MANUF_STATE_3`](#manuf_state)                             | 0x78     |        4 | This is a 256bit field used for keeping track of the manufacturing state.                |
| lc_ctrl.[`MANUF_STATE_4`](#manuf_state)                             | 0x7c     |        4 | This is a 256bit field used for keeping track of the manufacturing state.                |
| lc_ctrl.[`MANUF_STATE_5`](#manuf_state)                             | 0x80     |        4 | This is a 256bit field used for keeping track of the manufacturing state.                |
| lc_ctrl.[`MANUF_STATE_6`](#manuf_state)                             | 0x84     |        4 | This is a 256bit field used for keeping track of the manufacturing state.                |
| lc_ctrl.[`MANUF_STATE_7`](#manuf_state)                             | 0x88     |        4 | This is a 256bit field used for keeping track of the manufacturing state.                |

## ALERT_TEST
Alert Test Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "fatal_prog_error", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_state_error", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_bus_integ_error", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                      |
|:------:|:------:|:-------:|:----------------------|:-------------------------------------------------|
|  31:3  |        |         |                       | Reserved                                         |
|   2    |   wo   |   0x0   | fatal_bus_integ_error | Write 1 to trigger one alert event of this kind. |
|   1    |   wo   |   0x0   | fatal_state_error     | Write 1 to trigger one alert event of this kind. |
|   0    |   wo   |   0x0   | fatal_prog_error      | Write 1 to trigger one alert event of this kind. |

## STATUS
life cycle status register. Note that all errors are terminal and require a reset cycle.
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0xfff`

### Fields

```wavejson
{"reg": [{"name": "INITIALIZED", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "READY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "EXT_CLOCK_SWITCHED", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TRANSITION_SUCCESSFUL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TRANSITION_COUNT_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TRANSITION_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TOKEN_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FLASH_RMA_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "OTP_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "STATE_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "BUS_INTEG_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "OTP_PARTITION_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 20}], "config": {"lanes": 1, "fontsize": 10, "vspace": 240}}
```

|  Bits  |  Type  |  Reset  | Name                                                      |
|:------:|:------:|:-------:|:----------------------------------------------------------|
| 31:12  |        |         | Reserved                                                  |
|   11   |   ro   |    x    | [OTP_PARTITION_ERROR](#status--otp_partition_error)       |
|   10   |   ro   |    x    | [BUS_INTEG_ERROR](#status--bus_integ_error)               |
|   9    |   ro   |    x    | [STATE_ERROR](#status--state_error)                       |
|   8    |   ro   |    x    | [OTP_ERROR](#status--otp_error)                           |
|   7    |   ro   |    x    | [FLASH_RMA_ERROR](#status--flash_rma_error)               |
|   6    |   ro   |    x    | [TOKEN_ERROR](#status--token_error)                       |
|   5    |   ro   |    x    | [TRANSITION_ERROR](#status--transition_error)             |
|   4    |   ro   |    x    | [TRANSITION_COUNT_ERROR](#status--transition_count_error) |
|   3    |   ro   |    x    | [TRANSITION_SUCCESSFUL](#status--transition_successful)   |
|   2    |   ro   |    x    | [EXT_CLOCK_SWITCHED](#status--ext_clock_switched)         |
|   1    |   ro   |    x    | [READY](#status--ready)                                   |
|   0    |   ro   |    x    | [INITIALIZED](#status--initialized)                       |

### STATUS . OTP_PARTITION_ERROR
This bit is set to 1 if the life cycle partition in OTP is in error state.
This bit is intended for production testing during the RAW life cycle state,
where the OTP control and status registers are not accessible.
This error does not trigger an alert in the life cycle controller.

### STATUS . BUS_INTEG_ERROR
This bit is set to 1 if a fatal bus integrity fault is detected.
This error triggers a fatal_bus_integ_error alert.

### STATUS . STATE_ERROR
This bit is set to 1 if either the controller FSM state or the life cycle state is invalid or
has been corrupted as part of a tampering attempt. This error will move the life cycle state
automatically to INVALID and raise a fatal_state_error alert.

### STATUS . OTP_ERROR
This bit is set to 1 if an error occurred during an OTP programming operation.
This error will move the life cycle state automatically to POST_TRANSITION and raise a
fatal_prog_error alert.

### STATUS . FLASH_RMA_ERROR
This bit is set to 1 if flash failed to correctly respond to an RMA request.
Note that each transition attempt increments the [`LC_TRANSITION_CNT`](#lc_transition_cnt) and
moves the life cycle state into POST_TRANSITION.

### STATUS . TOKEN_ERROR
This bit is set to 1 if the token supplied for a conditional transition was invalid.
Note that each transition attempt increments the [`LC_TRANSITION_CNT`](#lc_transition_cnt) and
moves the life cycle state into POST_TRANSITION.

### STATUS . TRANSITION_ERROR
This bit is set to 1 if the last transition command requested an invalid state transition
(e.g. DEV -> RAW). Note that each transition attempt increments the [`LC_TRANSITION_CNT`](#lc_transition_cnt) and
moves the life cycle state into POST_TRANSITION.

### STATUS . TRANSITION_COUNT_ERROR
This bit is set to 1 if the [`LC_TRANSITION_CNT`](#lc_transition_cnt) has reached its maximum.
If this is the case, no more state transitions can be performed.
Note that each transition attempt increments the [`LC_TRANSITION_CNT`](#lc_transition_cnt) and
moves the life cycle state into POST_TRANSITION.

### STATUS . TRANSITION_SUCCESSFUL
This bit is set to 1 if the last life cycle transition request was successful.
Note that each transition attempt increments the [`LC_TRANSITION_CNT`](#lc_transition_cnt) and
moves the life cycle state into POST_TRANSITION.

### STATUS . EXT_CLOCK_SWITCHED
This bit is set to 1 if the clock manager has successfully switched to the external clock due to
[`EXT_CLOCK_EN`](#ext_clock_en) being set to 1.

### STATUS . READY
This bit is set to 1 if the life cycle controller has successfully initialized and is
ready to accept a life cycle transition command.

### STATUS . INITIALIZED
This bit is set to 1 if the life cycle controller has successfully initialized and the
state exposed in [`LC_STATE`](#lc_state) and [`LC_TRANSITION_CNT`](#lc_transition_cnt) is valid.

## CLAIM_TRANSITION_IF_REGWEN
Register write enable for the hardware mutex register.
- Offset: `0x8`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "CLAIM_TRANSITION_IF_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 280}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                                                                                                                                                              |
|:------:|:------:|:-------:|:---------------------------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                            | Reserved                                                                                                                                                                                                 |
|   0    |  rw0c  |   0x1   | CLAIM_TRANSITION_IF_REGWEN | This bit is managed by software and is set to 1 by default. When cleared to 0, the [`CLAIM_TRANSITION_IF`](#claim_transition_if) mutex register cannot be written to anymore. Write 0 to clear this bit. |

## CLAIM_TRANSITION_IF
Hardware mutex to claim exclusive access to the transition interface.
- Offset: `0xc`
- Reset default: `0x69`
- Reset mask: `0xff`
- Register enable: [`CLAIM_TRANSITION_IF_REGWEN`](#claim_transition_if_regwen)

### Fields

```wavejson
{"reg": [{"name": "MUTEX", "bits": 8, "attr": ["rw"], "rotate": 0}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                 |
|:------:|:------:|:-------:|:-------------------------------------|
|  31:8  |        |         | Reserved                             |
|  7:0   |   rw   |  0x69   | [MUTEX](#claim_transition_if--mutex) |

### CLAIM_TRANSITION_IF . MUTEX
In order to have exclusive access to the transition interface, SW must first claim the associated
hardware mutex by writing kMultiBitBool8True to this register.
If the register reads back kMultiBitBool8True, the mutex claim has been successful, and [`TRANSITION_REGWEN`](#transition_regwen)
will be set automatically to 1 by HW.
Write 0 to this register in order to release the HW mutex.

## TRANSITION_REGWEN
Register write enable for all transition interface registers.
- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "TRANSITION_REGWEN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name                                                       |
|:------:|:------:|:-------:|:-----------------------------------------------------------|
|  31:1  |        |         | Reserved                                                   |
|   0    |   ro   |   0x0   | [TRANSITION_REGWEN](#transition_regwen--transition_regwen) |

### TRANSITION_REGWEN . TRANSITION_REGWEN
This bit is hardware-managed and only readable by software.
By default, this bit is set to 0 by hardware.
Once SW has claimed the [`CLAIM_TRANSITION_IF`](#claim_transition_if) mutex, this bit will be set to 1.
Note that the life cycle controller sets this bit temporarily to 0 while executing a life cycle state
transition.

## TRANSITION_CMD
Command register for state transition requests.
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0x1`
- Register enable: [`TRANSITION_REGWEN`](#transition_regwen)

### Fields

```wavejson
{"reg": [{"name": "START", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                            |
|:------:|:------:|:-------:|:--------------------------------|
|  31:1  |        |         | Reserved                        |
|   0    | r0w1c  |    x    | [START](#transition_cmd--start) |

### TRANSITION_CMD . START
Writing a 1 to this register initiates the life cycle state transition to the state
specified in [`TRANSITION_TARGET.`](#transition_target)
Note that not all transitions are possible, and certain conditional transitions require
an additional [`TRANSITION_TOKEN_0.`](#transition_token_0)
In order to have exclusive access to this register, SW must first claim the associated
hardware mutex via [`CLAIM_TRANSITION_IF.`](#claim_transition_if)

## TRANSITION_CTRL
Control register for state transition requests.
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0x3`
- Register enable: [`TRANSITION_REGWEN`](#transition_regwen)

### Fields

```wavejson
{"reg": [{"name": "EXT_CLOCK_EN", "bits": 1, "attr": ["rw1s"], "rotate": -90}, {"name": "VOLATILE_RAW_UNLOCK", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 210}}
```

|  Bits  |  Type  |  Reset  | Name                                                         |
|:------:|:------:|:-------:|:-------------------------------------------------------------|
|  31:2  |        |         | Reserved                                                     |
|   1    |   rw   |    x    | [VOLATILE_RAW_UNLOCK](#transition_ctrl--volatile_raw_unlock) |
|   0    |  rw1s  |    x    | [EXT_CLOCK_EN](#transition_ctrl--ext_clock_en)               |

### TRANSITION_CTRL . VOLATILE_RAW_UNLOCK
When set to 1, LC_CTRL performs a volatile lifecycle transition from RAW -> TEST_UNLOCKED0.
No state update will be written to OTP, and no reset will be needed after the transition has succeeded.
Note that the token to be provided has to be the hashed unlock token, since in this case the token is NOT passed through KMAC before performing the comparison.

After a successful VOLATILE_RAW_UNLOCK transition from RAW -> TEST_UNLOCKED0, the LC_CTRL FSM will go back to the IdleSt and set the STATUS.TRANSITION_SUCCESSFUL bit.
The LC_CTRL accepts further transition commands in this state.

IMPORTANT NOTE: this feature is intended for test chips only in order to mitigate the risks of a malfunctioning
OTP macro. Production devices will permanently disable this feature at compile time via the SecVolatileRawUnlockEn parameter.

Software can check whether VOLATILE_RAW_UNLOCK is available by writing 1 and reading back
the register value. If the register reads back as 1 the mechanism is available, and if it reads back 0 it is not.

### TRANSITION_CTRL . EXT_CLOCK_EN
When set to 1, the OTP clock will be switched to an externally supplied clock right away when the
device is in a non-PROD life cycle state. The clock mux will remain switched until the next system reset.

## TRANSITION_TOKEN
128bit token for conditional transitions.
Make sure to set this to 0 for unconditional transitions.
Note that this register is shared with the life cycle TAP interface.
In order to have exclusive access to this register, SW must first claim the associated
hardware mutex via [`CLAIM_TRANSITION_IF.`](#claim_transition_if)
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name               | Offset   |
|:-------------------|:---------|
| TRANSITION_TOKEN_0 | 0x1c     |
| TRANSITION_TOKEN_1 | 0x20     |
| TRANSITION_TOKEN_2 | 0x24     |
| TRANSITION_TOKEN_3 | 0x28     |


### Fields

```wavejson
{"reg": [{"name": "TRANSITION_TOKEN", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name             | Description   |
|:------:|:------:|:-------:|:-----------------|:--------------|
|  31:0  |   rw   |    x    | TRANSITION_TOKEN |               |

## TRANSITION_TARGET
This register exposes the decoded life cycle state.
- Offset: `0x2c`
- Reset default: `0x0`
- Reset mask: `0x3fffffff`
- Register enable: [`TRANSITION_REGWEN`](#transition_regwen)

### Fields

```wavejson
{"reg": [{"name": "STATE", "bits": 30, "attr": ["rw"], "rotate": 0}, {"bits": 2}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                               |
|:------:|:------:|:-------:|:-----------------------------------|
| 31:30  |        |         | Reserved                           |
|  29:0  |   rw   |    x    | [STATE](#transition_target--state) |

### TRANSITION_TARGET . STATE
This field encodes the target life cycle state in a redundant enum format.
The 5bit state enum is repeated 6x so that it fills the entire 32bit register.
The encoding is straightforward replication: [val, val, val, val, val, val].

Note that this register is shared with the life cycle TAP interface.
In order to have exclusive access to this register, SW must first claim the associated
hardware mutex via [`CLAIM_TRANSITION_IF.`](#claim_transition_if)

| Value      | Name           | Description                                                                  |
|:-----------|:---------------|:-----------------------------------------------------------------------------|
| 0x00000000 | RAW            | Raw life cycle state after fabrication where all functions are disabled.     |
| 0x02108421 | TEST_UNLOCKED0 | Unlocked test state where debug functions are enabled.                       |
| 0x04210842 | TEST_LOCKED0   | Locked test state where where all functions are disabled.                    |
| 0x06318c63 | TEST_UNLOCKED1 | Unlocked test state where debug functions are enabled.                       |
| 0x08421084 | TEST_LOCKED1   | Locked test state where where all functions are disabled.                    |
| 0x0a5294a5 | TEST_UNLOCKED2 | Unlocked test state where debug functions are enabled.                       |
| 0x0c6318c6 | TEST_LOCKED2   | Locked test state where debug all functions are disabled.                    |
| 0x0e739ce7 | TEST_UNLOCKED3 | Unlocked test state where debug functions are enabled.                       |
| 0x10842108 | TEST_LOCKED3   | Locked test state where debug all functions are disabled.                    |
| 0x1294a529 | TEST_UNLOCKED4 | Unlocked test state where debug functions are enabled.                       |
| 0x14a5294a | TEST_LOCKED4   | Locked test state where debug all functions are disabled.                    |
| 0x16b5ad6b | TEST_UNLOCKED5 | Unlocked test state where debug functions are enabled.                       |
| 0x18c6318c | TEST_LOCKED5   | Locked test state where debug all functions are disabled.                    |
| 0x1ad6b5ad | TEST_UNLOCKED6 | Unlocked test state where debug functions are enabled.                       |
| 0x1ce739ce | TEST_LOCKED6   | Locked test state where debug all functions are disabled.                    |
| 0x1ef7bdef | TEST_UNLOCKED7 | Unlocked test state where debug functions are enabled.                       |
| 0x21084210 | DEV            | Development life cycle state where limited debug functionality is available. |
| 0x2318c631 | PROD           | Production life cycle state.                                                 |
| 0x25294a52 | PROD_END       | Same as PROD, but transition into RMA is not possible from this state.       |
| 0x2739ce73 | RMA            | RMA life cycle state.                                                        |
| 0x294a5294 | SCRAP          | SCRAP life cycle state where all functions are disabled.                     |

Other values are reserved.

## OTP_VENDOR_TEST_CTRL
Test/vendor-specific settings for the OTP macro wrapper.
These values are only active during RAW, TEST_* and RMA life cycle states.
In all other states, these values will be gated to zero before sending
them to the OTP macro wrapper - even if this register is programmed to a non-zero value.
- Offset: `0x30`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`TRANSITION_REGWEN`](#transition_regwen)

### Fields

```wavejson
{"reg": [{"name": "OTP_VENDOR_TEST_CTRL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description   |
|:------:|:------:|:-------:|:---------------------|:--------------|
|  31:0  |   rw   |    x    | OTP_VENDOR_TEST_CTRL |               |

## OTP_VENDOR_TEST_STATUS
Test/vendor-specific settings for the OTP macro wrapper.
These values are only active during RAW, TEST_* and RMA life cycle states.
In all other states, these values will read as zero.
- Offset: `0x34`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "OTP_VENDOR_TEST_STATUS", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                   | Description   |
|:------:|:------:|:-------:|:-----------------------|:--------------|
|  31:0  |   ro   |    x    | OTP_VENDOR_TEST_STATUS |               |

## LC_STATE
This register exposes the decoded life cycle state.
- Offset: `0x38`
- Reset default: `0x0`
- Reset mask: `0x3fffffff`

### Fields

```wavejson
{"reg": [{"name": "STATE", "bits": 30, "attr": ["ro"], "rotate": 0}, {"bits": 2}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                      |
|:------:|:------:|:-------:|:--------------------------|
| 31:30  |        |         | Reserved                  |
|  29:0  |   ro   |    x    | [STATE](#lc_state--state) |

### LC_STATE . STATE
This field exposes the decoded life cycle state in a redundant enum format.
The 5bit state enum is repeated 6x so that it fills the entire 32bit register.
The encoding is straightforward replication: [val, val, val, val, val, val].

| Value      | Name            | Description                                                                                                                      |
|:-----------|:----------------|:---------------------------------------------------------------------------------------------------------------------------------|
| 0x00000000 | RAW             | Raw life cycle state after fabrication where all functions are disabled.                                                         |
| 0x02108421 | TEST_UNLOCKED0  | Unlocked test state where debug functions are enabled.                                                                           |
| 0x04210842 | TEST_LOCKED0    | Locked test state where where all functions are disabled.                                                                        |
| 0x06318c63 | TEST_UNLOCKED1  | Unlocked test state where debug functions are enabled.                                                                           |
| 0x08421084 | TEST_LOCKED1    | Locked test state where where all functions are disabled.                                                                        |
| 0x0a5294a5 | TEST_UNLOCKED2  | Unlocked test state where debug functions are enabled.                                                                           |
| 0x0c6318c6 | TEST_LOCKED2    | Locked test state where debug all functions are disabled.                                                                        |
| 0x0e739ce7 | TEST_UNLOCKED3  | Unlocked test state where debug functions are enabled.                                                                           |
| 0x10842108 | TEST_LOCKED3    | Locked test state where debug all functions are disabled.                                                                        |
| 0x1294a529 | TEST_UNLOCKED4  | Unlocked test state where debug functions are enabled.                                                                           |
| 0x14a5294a | TEST_LOCKED4    | Locked test state where debug all functions are disabled.                                                                        |
| 0x16b5ad6b | TEST_UNLOCKED5  | Unlocked test state where debug functions are enabled.                                                                           |
| 0x18c6318c | TEST_LOCKED5    | Locked test state where debug all functions are disabled.                                                                        |
| 0x1ad6b5ad | TEST_UNLOCKED6  | Unlocked test state where debug functions are enabled.                                                                           |
| 0x1ce739ce | TEST_LOCKED6    | Locked test state where debug all functions are disabled.                                                                        |
| 0x1ef7bdef | TEST_UNLOCKED7  | Unlocked test state where debug functions are enabled.                                                                           |
| 0x21084210 | DEV             | Development life cycle state where limited debug functionality is available.                                                     |
| 0x2318c631 | PROD            | Production life cycle state.                                                                                                     |
| 0x25294a52 | PROD_END        | Same as PROD, but transition into RMA is not possible from this state.                                                           |
| 0x2739ce73 | RMA             | RMA life cycle state.                                                                                                            |
| 0x294a5294 | SCRAP           | SCRAP life cycle state where all functions are disabled.                                                                         |
| 0x2b5ad6b5 | POST_TRANSITION | This state is temporary and behaves the same way as SCRAP.                                                                       |
| 0x2d6b5ad6 | ESCALATE        | This state is temporary and behaves the same way as SCRAP.                                                                       |
| 0x2f7bdef7 | INVALID         | This state is reported when the life cycle state encoding is invalid. This state is temporary and behaves the same way as SCRAP. |

Other values are reserved.

## LC_TRANSITION_CNT
This register exposes the state of the decoded life cycle transition counter.
- Offset: `0x3c`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "CNT", "bits": 5, "attr": ["ro"], "rotate": 0}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                           |
|:------:|:------:|:-------:|:-------------------------------|
|  31:5  |        |         | Reserved                       |
|  4:0   |   ro   |    x    | [CNT](#lc_transition_cnt--cnt) |

### LC_TRANSITION_CNT . CNT
Number of total life cycle state transition attempts.
The life cycle controller allows up to 24 transition attempts.
If this counter is equal to 24, the [`LC_STATE`](#lc_state) is considered
to be invalid and will read as SCRAP.

If the counter state is invalid, or the life cycle controller is in the post-transition state,
the counter will have the value 31 (i.e., all counter bits will be set).

## LC_ID_STATE
This register exposes the id state of the device.
- Offset: `0x40`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "STATE", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                         |
|:------:|:------:|:-------:|:-----------------------------|
|  31:0  |   ro   |    x    | [STATE](#lc_id_state--state) |

### LC_ID_STATE . STATE
This field exposes the id state in redundant enum format.
The 2bit id state enum is repeated 16x so that it fills the entire 32bit register.
The encoding is straightforward replication: [val, val, ... val]."

| Value      | Name         | Description                               |
|:-----------|:-------------|:------------------------------------------|
| 0x00000000 | BLANK        | The device has not yet been personalized. |
| 0x11111111 | PERSONALIZED | The device has been personalized.         |
| 0x22222222 | INVALID      | The state is not valid.                   |

Other values are reserved.

## HW_REVISION0
This register holds the SILICON_CREATOR_ID and the PRODUCT_ID.
- Offset: `0x44`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "PRODUCT_ID", "bits": 16, "attr": ["ro"], "rotate": 0}, {"name": "SILICON_CREATOR_ID", "bits": 16, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                    |
|:------:|:------:|:-------:|:--------------------------------------------------------|
| 31:16  |   ro   |    x    | [SILICON_CREATOR_ID](#hw_revision0--silicon_creator_id) |
|  15:0  |   ro   |    x    | [PRODUCT_ID](#hw_revision0--product_id)                 |

### HW_REVISION0 . SILICON_CREATOR_ID
ID of the silicon creator.
Assigned by the OpenTitan project.
Zero is an invalid value.
The encoding must follow the following range constraints:

0x0000: invalid value
0x0001 - 0x3FFF: reserved for use in the open-source OpenTitan project
0x4000 - 0x7FFF: reserved for real integrations of OpenTitan
0x8000 - 0xFFFF: reserved for future use

### HW_REVISION0 . PRODUCT_ID
Used to identify a class of devices.
Assigned by the Silicon Creator.
Zero is an invalid value.
The encoding must follow the following range constraints:

0x0000: invalid value
0x0001 - 0x3FFF: reserved for discrete chip products
0x4000 - 0x7FFF: reserved for integrated IP products
0x8000 - 0xFFFF: reserved for future use

## HW_REVISION1
This register holds the REVISION_ID.
- Offset: `0x48`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "REVISION_ID", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "RESERVED", "bits": 24, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                      |
|:------:|:------:|:-------:|:------------------------------------------|
|  31:8  |   ro   |   0x0   | [RESERVED](#hw_revision1--reserved)       |
|  7:0   |   ro   |    x    | [REVISION_ID](#hw_revision1--revision_id) |

### HW_REVISION1 . RESERVED
Reserved bits.
Set to zero.

### HW_REVISION1 . REVISION_ID
Product revision ID. Assigned by the Silicon Creator.
The encoding is not specified other than that different tapeouts must be assigned different revision numbers.
I.e., each base or metal layer respin must be reflected so that software can rely on it to modify firmware and driver behavior.
Zero is an invalid value.

## DEVICE_ID
This is the 256bit DEVICE_ID value that is stored in the HW_CFG partition in OTP.
If this register reads all-one, the HW_CFG partition has not been initialized yet or is in error state.
If this register reads all-zero, this is indicative that the value has not been programmed to OTP yet.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name        | Offset   |
|:------------|:---------|
| DEVICE_ID_0 | 0x4c     |
| DEVICE_ID_1 | 0x50     |
| DEVICE_ID_2 | 0x54     |
| DEVICE_ID_3 | 0x58     |
| DEVICE_ID_4 | 0x5c     |
| DEVICE_ID_5 | 0x60     |
| DEVICE_ID_6 | 0x64     |
| DEVICE_ID_7 | 0x68     |


### Fields

```wavejson
{"reg": [{"name": "DEVICE_ID", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name      | Description   |
|:------:|:------:|:-------:|:----------|:--------------|
|  31:0  |   ro   |    x    | DEVICE_ID |               |

## MANUF_STATE
This is a 256bit field used for keeping track of the manufacturing state.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name          | Offset   |
|:--------------|:---------|
| MANUF_STATE_0 | 0x6c     |
| MANUF_STATE_1 | 0x70     |
| MANUF_STATE_2 | 0x74     |
| MANUF_STATE_3 | 0x78     |
| MANUF_STATE_4 | 0x7c     |
| MANUF_STATE_5 | 0x80     |
| MANUF_STATE_6 | 0x84     |
| MANUF_STATE_7 | 0x88     |


### Fields

```wavejson
{"reg": [{"name": "MANUF_STATE", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name        | Description   |
|:------:|:------:|:-------:|:------------|:--------------|
|  31:0  |   ro   |    x    | MANUF_STATE |               |


<!-- END CMDGEN -->
