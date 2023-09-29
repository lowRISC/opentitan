# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/top_earlgrey/ip_autogen/pwrmgr/data/pwrmgr.hjson -->
## Summary

| Name                                                     | Offset   |   Length | Description                                                                     |
|:---------------------------------------------------------|:---------|---------:|:--------------------------------------------------------------------------------|
| pwrmgr.[`INTR_STATE`](#intr_state)                       | 0x0      |        4 | Interrupt State Register                                                        |
| pwrmgr.[`INTR_ENABLE`](#intr_enable)                     | 0x4      |        4 | Interrupt Enable Register                                                       |
| pwrmgr.[`INTR_TEST`](#intr_test)                         | 0x8      |        4 | Interrupt Test Register                                                         |
| pwrmgr.[`ALERT_TEST`](#alert_test)                       | 0xc      |        4 | Alert Test Register                                                             |
| pwrmgr.[`CTRL_CFG_REGWEN`](#ctrl_cfg_regwen)             | 0x10     |        4 | Controls the configurability of the !!CONTROL register.                         |
| pwrmgr.[`CONTROL`](#control)                             | 0x14     |        4 | Control register                                                                |
| pwrmgr.[`CFG_CDC_SYNC`](#cfg_cdc_sync)                   | 0x18     |        4 | The configuration registers CONTROL, WAKEUP_EN, RESET_EN are all written in the |
| pwrmgr.[`WAKEUP_EN_REGWEN`](#wakeup_en_regwen)           | 0x1c     |        4 | Configuration enable for wakeup_en register                                     |
| pwrmgr.[`WAKEUP_EN`](#WAKEUP_EN)                         | 0x20     |        4 | Bit mask for enabled wakeups                                                    |
| pwrmgr.[`WAKE_STATUS`](#WAKE_STATUS)                     | 0x24     |        4 | A read only register of all current wake requests post enable mask              |
| pwrmgr.[`RESET_EN_REGWEN`](#reset_en_regwen)             | 0x28     |        4 | Configuration enable for reset_en register                                      |
| pwrmgr.[`RESET_EN`](#RESET_EN)                           | 0x2c     |        4 | Bit mask for enabled reset requests                                             |
| pwrmgr.[`RESET_STATUS`](#RESET_STATUS)                   | 0x30     |        4 | A read only register of all current reset requests post enable mask             |
| pwrmgr.[`ESCALATE_RESET_STATUS`](#escalate_reset_status) | 0x34     |        4 | A read only register of escalation reset request                                |
| pwrmgr.[`WAKE_INFO_CAPTURE_DIS`](#wake_info_capture_dis) | 0x38     |        4 | Indicates which functions caused the chip to wakeup                             |
| pwrmgr.[`WAKE_INFO`](#wake_info)                         | 0x3c     |        4 | Indicates which functions caused the chip to wakeup.                            |
| pwrmgr.[`FAULT_STATUS`](#fault_status)                   | 0x40     |        4 | A read only register that shows the existing faults                             |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "wakeup", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                               |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                  |
|   0    |  rw1c  |   0x0   | wakeup | Wake from low power state. See wake info for more details |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "wakeup", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                      |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                         |
|   0    |   rw   |   0x0   | wakeup | Enable interrupt when [`INTR_STATE.wakeup`](#intr_state) is set. |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "wakeup", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                               |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                  |
|   0    |   wo   |   0x0   | wakeup | Write 1 to force [`INTR_STATE.wakeup`](#intr_state) to 1. |

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

## CTRL_CFG_REGWEN
Controls the configurability of the [`CONTROL`](#control) register.

This register ensures the contents do not change once a low power hint and
WFI has occurred.

It unlocks whenever a low power transition has completed (transition back to the
ACTIVE state) for any reason.
- Offset: `0x10`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                                                                                            |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                                                                                                                                                                                               |
|   0    |   ro   |   0x1   | EN     | Configuration enable.  This bit defaults to 1 and is set to 0 by hardware when low power entry is initiated. When the device transitions back from low power state to active state, this bit is set back to 1 to allow software configuration of [`CONTROL`](#control) |

## CONTROL
Control register
- Offset: `0x14`
- Reset default: `0x180`
- Reset mask: `0x1f1`
- Register enable: [`CTRL_CFG_REGWEN`](#ctrl_cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "LOW_POWER_HINT", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 3}, {"name": "CORE_CLK_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "IO_CLK_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "USB_CLK_EN_LP", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "USB_CLK_EN_ACTIVE", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "MAIN_PD_N", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 23}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name                                             |
|:------:|:------:|:-------:|:-------------------------------------------------|
|  31:9  |        |         | Reserved                                         |
|   8    |   rw   |   0x1   | [MAIN_PD_N](#control--main_pd_n)                 |
|   7    |   rw   |   0x1   | [USB_CLK_EN_ACTIVE](#control--usb_clk_en_active) |
|   6    |   rw   |   0x0   | [USB_CLK_EN_LP](#control--usb_clk_en_lp)         |
|   5    |   rw   |   0x0   | [IO_CLK_EN](#control--io_clk_en)                 |
|   4    |   rw   |   0x0   | [CORE_CLK_EN](#control--core_clk_en)             |
|  3:1   |        |         | Reserved                                         |
|   0    |   rw   |   0x0   | [LOW_POWER_HINT](#control--low_power_hint)       |

### CONTROL . MAIN_PD_N
Active low, main power domain power down

| Value   | Name       | Description                                               |
|:--------|:-----------|:----------------------------------------------------------|
| 0x0     | Power down | Main power domain is powered down during low power state. |
| 0x1     | Power up   | Main power domain is kept powered during low power state  |


### CONTROL . USB_CLK_EN_ACTIVE
USB clock enable during active power state

| Value   | Name     | Description                                  |
|:--------|:---------|:---------------------------------------------|
| 0x0     | Disabled | USB clock disabled during active power state |
| 0x1     | Enabled  | USB clock enabled during active power state  |


### CONTROL . USB_CLK_EN_LP
USB clock enable during low power state

| Value   | Name     | Description                                                                                                                    |
|:--------|:---------|:-------------------------------------------------------------------------------------------------------------------------------|
| 0x0     | Disabled | USB clock disabled during low power state                                                                                      |
| 0x1     | Enabled  | USB clock enabled during low power state.  However, if !!CONTROL.MAIN_PD_N is 0, USB clock is disabled during low power state. |


### CONTROL . IO_CLK_EN
IO clock enable during low power state

| Value   | Name     | Description                              |
|:--------|:---------|:-----------------------------------------|
| 0x0     | Disabled | IO clock disabled during low power state |
| 0x1     | Enabled  | IO clock enabled during low power state  |


### CONTROL . CORE_CLK_EN
core clock enable during low power state

| Value   | Name     | Description                                |
|:--------|:---------|:-------------------------------------------|
| 0x0     | Disabled | Core clock disabled during low power state |
| 0x1     | Enabled  | Core clock enabled during low power state  |


### CONTROL . LOW_POWER_HINT
The low power hint to power manager.
The hint is an indication for how the manager should treat the next WFI.
Once the power manager begins a low power transition, or if a valid reset request is registered,
this bit is automatically cleared by HW.

| Value   | Name      | Description                             |
|:--------|:----------|:----------------------------------------|
| 0x0     | None      | No low power intent                     |
| 0x1     | Low Power | Next WFI should trigger low power entry |


## CFG_CDC_SYNC
The configuration registers CONTROL, WAKEUP_EN, RESET_EN are all written in the
fast clock domain but used in the slow clock domain.

The configuration are not propagated across the clock boundary until this
register is triggered and read.  See fields below for more details
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "SYNC", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                        |
|:------:|:------:|:-------:|:----------------------------|
|  31:1  |        |         | Reserved                    |
|   0    |   rw   |   0x0   | [SYNC](#cfg_cdc_sync--sync) |

### CFG_CDC_SYNC . SYNC
Configuration sync.  When this bit is written to 1, a sync pulse is generated.  When
the sync completes, this bit then self clears.

Software should write this bit to 1, wait for it to clear, before assuming the slow clock
domain has accepted the programmed values.

## WAKEUP_EN_REGWEN
Configuration enable for wakeup_en register
- Offset: `0x1c`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                    |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                       |
|   0    |  rw0c  |   0x1   | EN     | When 1, WAKEUP_EN register can be configured. When 0, WAKEUP_EN register cannot be configured. |

## WAKEUP_EN
Bit mask for enabled wakeups
- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0x3f`
- Register enable: [`WAKEUP_EN_REGWEN`](#wakeup_en_regwen)

### Fields

```wavejson
{"reg": [{"name": "EN_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_4", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_5", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 26}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                   |
|:------:|:------:|:-------:|:-------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:6  |        |         |        | Reserved                                                                                                                                                      |
|   5    |   rw   |   0x0   | EN_5   | Whenever a particular bit is set to 1, that wakeup is also enabled. Whenever a particular bit is set to 0, that wakeup cannot wake the device from low power. |
|   4    |   rw   |   0x0   | EN_4   | Whenever a particular bit is set to 1, that wakeup is also enabled. Whenever a particular bit is set to 0, that wakeup cannot wake the device from low power. |
|   3    |   rw   |   0x0   | EN_3   | Whenever a particular bit is set to 1, that wakeup is also enabled. Whenever a particular bit is set to 0, that wakeup cannot wake the device from low power. |
|   2    |   rw   |   0x0   | EN_2   | Whenever a particular bit is set to 1, that wakeup is also enabled. Whenever a particular bit is set to 0, that wakeup cannot wake the device from low power. |
|   1    |   rw   |   0x0   | EN_1   | Whenever a particular bit is set to 1, that wakeup is also enabled. Whenever a particular bit is set to 0, that wakeup cannot wake the device from low power. |
|   0    |   rw   |   0x0   | EN_0   | Whenever a particular bit is set to 1, that wakeup is also enabled. Whenever a particular bit is set to 0, that wakeup cannot wake the device from low power. |

## WAKE_STATUS
A read only register of all current wake requests post enable mask
- Offset: `0x24`
- Reset default: `0x0`
- Reset mask: `0x3f`

### Fields

```wavejson
{"reg": [{"name": "VAL_0", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VAL_1", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VAL_2", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VAL_3", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VAL_4", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VAL_5", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 26}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                    |
|:------:|:------:|:-------:|:-------|:-------------------------------|
|  31:6  |        |         |        | Reserved                       |
|   5    |   ro   |   0x0   | VAL_5  | Current value of wake requests |
|   4    |   ro   |   0x0   | VAL_4  | Current value of wake requests |
|   3    |   ro   |   0x0   | VAL_3  | Current value of wake requests |
|   2    |   ro   |   0x0   | VAL_2  | Current value of wake requests |
|   1    |   ro   |   0x0   | VAL_1  | Current value of wake requests |
|   0    |   ro   |   0x0   | VAL_0  | Current value of wake requests |

## RESET_EN_REGWEN
Configuration enable for reset_en register
- Offset: `0x28`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                  |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                     |
|   0    |  rw0c  |   0x1   | EN     | When 1, RESET_EN register can be configured. When 0, RESET_EN register cannot be configured. |

## RESET_EN
Bit mask for enabled reset requests
- Offset: `0x2c`
- Reset default: `0x0`
- Reset mask: `0x3`
- Register enable: [`RESET_EN_REGWEN`](#reset_en_regwen)

### Fields

```wavejson
{"reg": [{"name": "EN_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "EN_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                              |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:2  |        |         |        | Reserved                                                                                                                                                 |
|   1    |   rw   |   0x0   | EN_1   | Whenever a particular bit is set to 1, that reset request is enabled. Whenever a particular bit is set to 0, that reset request cannot reset the device. |
|   0    |   rw   |   0x0   | EN_0   | Whenever a particular bit is set to 1, that reset request is enabled. Whenever a particular bit is set to 0, that reset request cannot reset the device. |

## RESET_STATUS
A read only register of all current reset requests post enable mask
- Offset: `0x30`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "VAL_0", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VAL_1", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                    |
|:------:|:------:|:-------:|:-------|:-------------------------------|
|  31:2  |        |         |        | Reserved                       |
|   1    |   ro   |   0x0   | VAL_1  | Current value of reset request |
|   0    |   ro   |   0x0   | VAL_0  | Current value of reset request |

## ESCALATE_RESET_STATUS
A read only register of escalation reset request
- Offset: `0x34`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                      |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                         |
|   0    |   ro   |   0x0   | VAL    | When 1, an escalation reset has been seen. When 0, there is no escalation reset. |

## WAKE_INFO_CAPTURE_DIS
Indicates which functions caused the chip to wakeup
- Offset: `0x38`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                             |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                                                                |
|   0    |   rw   |   0x0   | VAL    | When written to 1, this actively suppresses the wakeup info capture. When written to 0, wakeup info capture timing is controlled by HW. |

## WAKE_INFO
Indicates which functions caused the chip to wakeup.
The wake info recording begins whenever the device begins a valid low power entry.

This capture is continued until it is explicitly disabled through WAKE_INFO_CAPTURE_DIS.
This means it is possible to capture multiple wakeup reasons.
- Offset: `0x3c`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "REASONS", "bits": 6, "attr": ["rw1c"], "rotate": 0}, {"name": "FALL_THROUGH", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "ABORT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name                                     |
|:------:|:------:|:-------:|:-----------------------------------------|
|  31:8  |        |         | Reserved                                 |
|   7    |  rw1c  |   0x0   | [ABORT](#wake_info--abort)               |
|   6    |  rw1c  |   0x0   | [FALL_THROUGH](#wake_info--fall_through) |
|  5:0   |  rw1c  |   0x0   | [REASONS](#wake_info--reasons)           |

### WAKE_INFO . ABORT
The abort wakeup reason indicates that despite setting a WFI and providing a low power
hint, an active flash / lifecycle / otp transaction was ongoing when the power controller
attempted to initiate low power entry.

The power manager detects this condition, halts low power entry and reports as a wakeup reason

### WAKE_INFO . FALL_THROUGH
The fall through wakeup reason indicates that despite setting a WFI and providing a low power
hint, an interrupt arrived at just the right time to break the executing core out of WFI.

The power manager detects this condition, halts low power entry and reports as a wakeup reason

### WAKE_INFO . REASONS
Various peripheral wake reasons

## FAULT_STATUS
A read only register that shows the existing faults
- Offset: `0x40`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "REG_INTG_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ESC_TIMEOUT", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "MAIN_PD_GLITCH", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                                               |
|:------:|:------:|:-------:|:---------------|:----------------------------------------------------------|
|  31:3  |        |         |                | Reserved                                                  |
|   2    |   ro   |   0x0   | MAIN_PD_GLITCH | When 1, unexpected power glitch was observed on main PD.  |
|   1    |   ro   |   0x0   | ESC_TIMEOUT    | When 1, an escalation clock / reset timeout has occurred. |
|   0    |   ro   |   0x0   | REG_INTG_ERR   | When 1, an integrity error has occurred.                  |


<!-- END CMDGEN -->
