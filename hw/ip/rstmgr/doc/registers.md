# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/top_earlgrey/ip/rstmgr/data/autogen/rstmgr.hjson -->
## Summary

| Name                                         | Offset   |   Length | Description                                                        |
|:---------------------------------------------|:---------|---------:|:-------------------------------------------------------------------|
| rstmgr.[`ALERT_TEST`](#alert_test)           | 0x0      |        4 | Alert Test Register                                                |
| rstmgr.[`RESET_REQ`](#reset_req)             | 0x4      |        4 | Software requested system reset.                                   |
| rstmgr.[`RESET_INFO`](#reset_info)           | 0x8      |        4 | Device reset reason.                                               |
| rstmgr.[`ALERT_REGWEN`](#alert_regwen)       | 0xc      |        4 | Alert write enable                                                 |
| rstmgr.[`ALERT_INFO_CTRL`](#alert_info_ctrl) | 0x10     |        4 | Alert info dump controls.                                          |
| rstmgr.[`ALERT_INFO_ATTR`](#alert_info_attr) | 0x14     |        4 | Alert info dump attributes.                                        |
| rstmgr.[`ALERT_INFO`](#alert_info)           | 0x18     |        4 | Alert dump information prior to last reset.                        |
| rstmgr.[`CPU_REGWEN`](#cpu_regwen)           | 0x1c     |        4 | Cpu write enable                                                   |
| rstmgr.[`CPU_INFO_CTRL`](#cpu_info_ctrl)     | 0x20     |        4 | Cpu info dump controls.                                            |
| rstmgr.[`CPU_INFO_ATTR`](#cpu_info_attr)     | 0x24     |        4 | Cpu info dump attributes.                                          |
| rstmgr.[`CPU_INFO`](#cpu_info)               | 0x28     |        4 | Cpu dump information prior to last reset.                          |
| rstmgr.[`SW_RST_REGWEN_0`](#sw_rst_regwen)   | 0x2c     |        4 | Register write enable for software controllable resets.            |
| rstmgr.[`SW_RST_REGWEN_1`](#sw_rst_regwen)   | 0x30     |        4 | Register write enable for software controllable resets.            |
| rstmgr.[`SW_RST_REGWEN_2`](#sw_rst_regwen)   | 0x34     |        4 | Register write enable for software controllable resets.            |
| rstmgr.[`SW_RST_REGWEN_3`](#sw_rst_regwen)   | 0x38     |        4 | Register write enable for software controllable resets.            |
| rstmgr.[`SW_RST_REGWEN_4`](#sw_rst_regwen)   | 0x3c     |        4 | Register write enable for software controllable resets.            |
| rstmgr.[`SW_RST_REGWEN_5`](#sw_rst_regwen)   | 0x40     |        4 | Register write enable for software controllable resets.            |
| rstmgr.[`SW_RST_REGWEN_6`](#sw_rst_regwen)   | 0x44     |        4 | Register write enable for software controllable resets.            |
| rstmgr.[`SW_RST_REGWEN_7`](#sw_rst_regwen)   | 0x48     |        4 | Register write enable for software controllable resets.            |
| rstmgr.[`SW_RST_CTRL_N_0`](#sw_rst_ctrl_n)   | 0x4c     |        4 | Software controllable resets.                                      |
| rstmgr.[`SW_RST_CTRL_N_1`](#sw_rst_ctrl_n)   | 0x50     |        4 | Software controllable resets.                                      |
| rstmgr.[`SW_RST_CTRL_N_2`](#sw_rst_ctrl_n)   | 0x54     |        4 | Software controllable resets.                                      |
| rstmgr.[`SW_RST_CTRL_N_3`](#sw_rst_ctrl_n)   | 0x58     |        4 | Software controllable resets.                                      |
| rstmgr.[`SW_RST_CTRL_N_4`](#sw_rst_ctrl_n)   | 0x5c     |        4 | Software controllable resets.                                      |
| rstmgr.[`SW_RST_CTRL_N_5`](#sw_rst_ctrl_n)   | 0x60     |        4 | Software controllable resets.                                      |
| rstmgr.[`SW_RST_CTRL_N_6`](#sw_rst_ctrl_n)   | 0x64     |        4 | Software controllable resets.                                      |
| rstmgr.[`SW_RST_CTRL_N_7`](#sw_rst_ctrl_n)   | 0x68     |        4 | Software controllable resets.                                      |
| rstmgr.[`ERR_CODE`](#err_code)               | 0x6c     |        4 | A bit vector of all the errors that have occurred in reset manager |

## ALERT_TEST
Alert Test Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "fatal_fault", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_cnsty_fault", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                                      |
|:------:|:------:|:-------:|:------------------|:-------------------------------------------------|
|  31:2  |        |         |                   | Reserved                                         |
|   1    |   wo   |   0x0   | fatal_cnsty_fault | Write 1 to trigger one alert event of this kind. |
|   0    |   wo   |   0x0   | fatal_fault       | Write 1 to trigger one alert event of this kind. |

## RESET_REQ
Software requested system reset.
- Offset: `0x4`
- Reset default: `0x9`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                     |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:4  |        |         |        | Reserved                                                                                                                                        |
|  3:0   |   rw   |   0x9   | VAL    | When set to kMultiBitBool4True, a reset to power manager is requested. Upon completion of reset, this bit is automatically cleared by hardware. |

## RESET_INFO
Device reset reason.
- Offset: `0x8`
- Reset default: `0x1`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "POR", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "LOW_POWER_EXIT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "SW_RESET", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "HW_REQ", "bits": 5, "attr": ["rw1c"], "rotate": 0}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name                                          |
|:------:|:------:|:-------:|:----------------------------------------------|
|  31:8  |        |         | Reserved                                      |
|  7:3   |  rw1c  |   0x0   | [HW_REQ](#reset_info--hw_req)                 |
|   2    |  rw1c  |   0x0   | [SW_RESET](#reset_info--sw_reset)             |
|   1    |  rw1c  |   0x0   | [LOW_POWER_EXIT](#reset_info--low_power_exit) |
|   0    |  rw1c  |   0x1   | [POR](#reset_info--por)                       |

### RESET_INFO . HW_REQ
Indicates when a device has reset due to a hardware requested reset.
The bit mapping is as follows:
b3: sysrst_ctrl_aon: OpenTitan reset request to `rstmgr` (running on AON clock).
b4: aon_timer_aon: watchdog reset requestt
b5: pwrmgr_aon: main power glitch reset request
b6: alert_handler: escalation reset request
b7: rv_dm: non-debug-module reset request

### RESET_INFO . SW_RESET
Indicates when a device has reset due to [`RESET_REQ.`](#reset_req)

### RESET_INFO . LOW_POWER_EXIT
Indicates when a device has reset due low power exit.

### RESET_INFO . POR
Indicates when a device has reset due to power up.

## ALERT_REGWEN
Alert write enable
- Offset: `0xc`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                    |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                       |
|   0    |  rw0c  |   0x1   | EN     | When 1, [`ALERT_INFO_CTRL`](#alert_info_ctrl) can be modified. |

## ALERT_INFO_CTRL
Alert info dump controls.
- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0xf1`
- Register enable: [`ALERT_REGWEN`](#alert_regwen)

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 3}, {"name": "INDEX", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                         |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------------------------------------------------------------------------------|
|  31:8  |        |         |        | Reserved                                                                                                                            |
|  7:4   |   rw   |   0x0   | INDEX  | Controls which 32-bit value to read.                                                                                                |
|  3:1   |        |         |        | Reserved                                                                                                                            |
|   0    |   rw   |   0x0   | EN     | Enable alert dump to capture new information. This field is automatically set to 0 upon system reset (even if rstmgr is not reset). |

## ALERT_INFO_ATTR
Alert info dump attributes.
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "CNT_AVAIL", "bits": 4, "attr": ["ro"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                   |
|:------:|:------:|:-------:|:----------|:--------------------------------------------------------------|
|  31:4  |        |         |           | Reserved                                                      |
|  3:0   |   ro   |   0x0   | CNT_AVAIL | The number of 32-bit values contained in the alert info dump. |

## ALERT_INFO
  Alert dump information prior to last reset.
  Which value read is controlled by the [`ALERT_INFO_CTRL`](#alert_info_ctrl) register.
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "VALUE", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                             |
|:------:|:------:|:-------:|:-------|:----------------------------------------|
|  31:0  |   ro   |   0x0   | VALUE  | The current 32-bit value of crash dump. |

## CPU_REGWEN
Cpu write enable
- Offset: `0x1c`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                   |
|   0    |  rw0c  |   0x1   | EN     | When 1, [`CPU_INFO_CTRL`](#cpu_info_ctrl) can be modified. |

## CPU_INFO_CTRL
Cpu info dump controls.
- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0xf1`
- Register enable: [`CPU_REGWEN`](#cpu_regwen)

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 3}, {"name": "INDEX", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                       |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------------------------------------------------|
|  31:8  |        |         |        | Reserved                                                                                                                          |
|  7:4   |   rw   |   0x0   | INDEX  | Controls which 32-bit value to read.                                                                                              |
|  3:1   |        |         |        | Reserved                                                                                                                          |
|   0    |   rw   |   0x0   | EN     | Enable cpu dump to capture new information. This field is automatically set to 0 upon system reset (even if rstmgr is not reset). |

## CPU_INFO_ATTR
Cpu info dump attributes.
- Offset: `0x24`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "CNT_AVAIL", "bits": 4, "attr": ["ro"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                 |
|:------:|:------:|:-------:|:----------|:------------------------------------------------------------|
|  31:4  |        |         |           | Reserved                                                    |
|  3:0   |   ro   |   0x0   | CNT_AVAIL | The number of 32-bit values contained in the cpu info dump. |

## CPU_INFO
  Cpu dump information prior to last reset.
  Which value read is controlled by the [`CPU_INFO_CTRL`](#cpu_info_ctrl) register.
- Offset: `0x28`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "VALUE", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                             |
|:------:|:------:|:-------:|:-------|:----------------------------------------|
|  31:0  |   ro   |   0x0   | VALUE  | The current 32-bit value of crash dump. |

## SW_RST_REGWEN
Register write enable for software controllable resets.
When a particular bit value is 0, the corresponding value in [`SW_RST_CTRL_N`](#sw_rst_ctrl_n) can no longer be changed.
When a particular bit value is 1, the corresponding value in [`SW_RST_CTRL_N`](#sw_rst_ctrl_n) can be changed.
- Reset default: `0x1`
- Reset mask: `0x1`

### Instances

| Name            | Offset   |
|:----------------|:---------|
| SW_RST_REGWEN_0 | 0x2c     |
| SW_RST_REGWEN_1 | 0x30     |
| SW_RST_REGWEN_2 | 0x34     |
| SW_RST_REGWEN_3 | 0x38     |
| SW_RST_REGWEN_4 | 0x3c     |
| SW_RST_REGWEN_5 | 0x40     |
| SW_RST_REGWEN_6 | 0x44     |
| SW_RST_REGWEN_7 | 0x48     |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                            |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                               |
|   0    |  rw0c  |   0x1   | EN     | Register write enable for software controllable resets |

## SW_RST_CTRL_N
Software controllable resets.
When a particular bit value is 0, the corresponding module is held in reset.
When a particular bit value is 1, the corresponding module is not held in reset.
- Reset default: `0x1`
- Reset mask: `0x1`

### Instances

| Name            | Offset   |
|:----------------|:---------|
| SW_RST_CTRL_N_0 | 0x4c     |
| SW_RST_CTRL_N_1 | 0x50     |
| SW_RST_CTRL_N_2 | 0x54     |
| SW_RST_CTRL_N_3 | 0x58     |
| SW_RST_CTRL_N_4 | 0x5c     |
| SW_RST_CTRL_N_5 | 0x60     |
| SW_RST_CTRL_N_6 | 0x64     |
| SW_RST_CTRL_N_7 | 0x68     |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description          |
|:------:|:------:|:-------:|:-------|:---------------------|
|  31:1  |        |         |        | Reserved             |
|   0    |   rw   |   0x1   | VAL    | Software reset value |

## ERR_CODE
A bit vector of all the errors that have occurred in reset manager
- Offset: `0x6c`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "REG_INTG_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "RESET_CONSISTENCY_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FSM_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                           |
|:------:|:------:|:-------:|:----------------------|:------------------------------------------------------|
|  31:3  |        |         |                       | Reserved                                              |
|   2    |   ro   |   0x0   | FSM_ERR               | Sparsely encoded fsm error.                           |
|   1    |   ro   |   0x0   | RESET_CONSISTENCY_ERR | A inconsistent parent / child reset was observed.     |
|   0    |   ro   |   0x0   | REG_INTG_ERR          | The register file has experienced an integrity error. |


<!-- END CMDGEN -->
