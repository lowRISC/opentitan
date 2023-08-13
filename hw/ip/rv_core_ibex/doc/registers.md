# Registers

A number of memory-mapped registers are available to control Ibex-related functionality that's specific to OpenTitan.

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/rv_core_ibex/data/rv_core_ibex.hjson -->
## Summary

| Name                                                       | Offset   |   Length | Description                                          |
|:-----------------------------------------------------------|:---------|---------:|:-----------------------------------------------------|
| rv_core_ibex.[`ALERT_TEST`](#alert_test)                   | 0x0      |        4 | Alert Test Register                                  |
| rv_core_ibex.[`SW_RECOV_ERR`](#sw_recov_err)               | 0x4      |        4 | Software recoverable error                           |
| rv_core_ibex.[`SW_FATAL_ERR`](#sw_fatal_err)               | 0x8      |        4 | Software fatal error                                 |
| rv_core_ibex.[`IBUS_REGWEN_0`](#ibus_regwen)               | 0xc      |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_REGWEN_1`](#ibus_regwen)               | 0x10     |        4 | Ibus address control regwen.                         |
| rv_core_ibex.[`IBUS_ADDR_EN_0`](#ibus_addr_en)             | 0x14     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_EN_1`](#ibus_addr_en)             | 0x18     |        4 | Enable Ibus address matching                         |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_0`](#ibus_addr_matching) | 0x1c     |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_ADDR_MATCHING_1`](#ibus_addr_matching) | 0x20     |        4 | Matching region programming for ibus.                |
| rv_core_ibex.[`IBUS_REMAP_ADDR_0`](#ibus_remap_addr)       | 0x24     |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`IBUS_REMAP_ADDR_1`](#ibus_remap_addr)       | 0x28     |        4 | The remap address after a match has been made.       |
| rv_core_ibex.[`DBUS_REGWEN_0`](#dbus_regwen)               | 0x2c     |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_REGWEN_1`](#dbus_regwen)               | 0x30     |        4 | Dbus address control regwen.                         |
| rv_core_ibex.[`DBUS_ADDR_EN_0`](#dbus_addr_en)             | 0x34     |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_EN_1`](#dbus_addr_en)             | 0x38     |        4 | Enable dbus address matching                         |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_0`](#dbus_addr_matching) | 0x3c     |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_ADDR_MATCHING_1`](#dbus_addr_matching) | 0x40     |        4 | See !!IBUS_ADDR_MATCHING_0 for detailed description. |
| rv_core_ibex.[`DBUS_REMAP_ADDR_0`](#dbus_remap_addr)       | 0x44     |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`DBUS_REMAP_ADDR_1`](#dbus_remap_addr)       | 0x48     |        4 | See !!IBUS_REMAP_ADDR_0 for a detailed description.  |
| rv_core_ibex.[`NMI_ENABLE`](#nmi_enable)                   | 0x4c     |        4 | Enable mask for NMI.                                 |
| rv_core_ibex.[`NMI_STATE`](#nmi_state)                     | 0x50     |        4 | Current NMI state                                    |
| rv_core_ibex.[`ERR_STATUS`](#err_status)                   | 0x54     |        4 | error status                                         |
| rv_core_ibex.[`RND_DATA`](#rnd_data)                       | 0x58     |        4 | Random data from EDN                                 |
| rv_core_ibex.[`RND_STATUS`](#rnd_status)                   | 0x5c     |        4 | Status of random data in !!RND_DATA                  |
| rv_core_ibex.[`FPGA_INFO`](#fpga_info)                     | 0x60     |        4 | FPGA build timestamp info.                           |
| rv_core_ibex.[`DV_SIM_WINDOW`](#dv_sim_window)             | 0x80     |       32 | Exposed tlul window for DV only purposes.            |

## ALERT_TEST
Alert Test Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "fatal_sw_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "recov_sw_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_hw_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "recov_hw_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                      |
|:------:|:------:|:-------:|:-------------|:-------------------------------------------------|
|  31:4  |        |         |              | Reserved                                         |
|   3    |   wo   |   0x0   | recov_hw_err | Write 1 to trigger one alert event of this kind. |
|   2    |   wo   |   0x0   | fatal_hw_err | Write 1 to trigger one alert event of this kind. |
|   1    |   wo   |   0x0   | recov_sw_err | Write 1 to trigger one alert event of this kind. |
|   0    |   wo   |   0x0   | fatal_sw_err | Write 1 to trigger one alert event of this kind. |

## SW_RECOV_ERR
Software recoverable error
- Offset: `0x4`
- Reset default: `0x9`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                            |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:4  |        |         |        | Reserved                                                                                                                                                                               |
|  3:0   |   rw   |   0x9   | VAL    | Software recoverable alert. When set to any value other than kMultiBitBool4False, a recoverable alert is sent. Once the alert is sent, the field is then reset to kMultiBitBool4False. |

## SW_FATAL_ERR
Software fatal error
- Offset: `0x8`
- Reset default: `0x9`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 4, "attr": ["rw0c"], "rotate": 0}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                              |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:4  |        |         |        | Reserved                                                                                                                                                                                 |
|  3:0   |  rw0c  |   0x9   | VAL    | Software fatal alert. When set to any value other than kMultiBitBool4False, a fatal alert is sent. Note, this field once cleared cannot be set and will continuously cause alert events. |

## IBUS_REGWEN
Ibus address control regwen.
- Reset default: `0x1`
- Reset mask: `0x1`

### Instances

| Name          | Offset   |
|:--------------|:---------|
| IBUS_REGWEN_0 | 0xc      |
| IBUS_REGWEN_1 | 0x10     |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                   |
|:------:|:------:|:-------:|:-----------------------|
|  31:1  |        |         | Reserved               |
|   0    |  rw0c  |   0x1   | [EN](#ibus_regwen--en) |

### IBUS_REGWEN . EN
Ibus address controls write enable.  Once set to 0, it can longer be configured to 1

| Value   | Name    | Description                                                    |
|:--------|:--------|:---------------------------------------------------------------|
| 0x0     | locked  | Address controls can no longer be configured until next reset. |
| 0x1     | enabled | Address controls can still be configured.                      |


## IBUS_ADDR_EN
Enable Ibus address matching
- Reset default: `0x0`
- Reset mask: `0x1`

### Instances

| Name           | Offset   |
|:---------------|:---------|
| IBUS_ADDR_EN_0 | 0x14     |
| IBUS_ADDR_EN_1 | 0x18     |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                   |
|:------:|:------:|:-------:|:-------|:------------------------------|
|  31:1  |        |         |        | Reserved                      |
|   0    |   rw   |   0x0   | EN     | Enable ibus address matching. |

## IBUS_ADDR_MATCHING
  Matching region programming for ibus.

  The value programmed is done at power-of-2 alignment.
  For example, if the intended matching region is 0x8000_0000 to 0x8000_FFFF, the value programmed is 0x8000_7FFF.

  The value programmed can be determined from the translation granule.
  Assume the user wishes to translate a specific 64KB block to a different address:
  64KB has a hex value of 0x10000.
  Subtract 1 from this value and then right shift by one to obtain 0x7FFF.
  This value is then logically OR'd with the upper address bits that would select which 64KB to translate.

  In this example, the user wishes to translate the 0x8000-th 64KB block.
  The value programmed is then 0x8000_7FFF.

  If the user were to translate the 0x8001-th 64KB block, the value programmed would be 0x8001_7FFF.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                 | Offset   |
|:---------------------|:---------|
| IBUS_ADDR_MATCHING_0 | 0x1c     |
| IBUS_ADDR_MATCHING_1 | 0x20     |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description           |
|:------:|:------:|:-------:|:-------|:----------------------|
|  31:0  |   rw   |   0x0   | VAL    | Matching region value |

## IBUS_REMAP_ADDR
  The remap address after a match has been made.
  The remap bits apply only to top portion of address bits not covered by the matching region.

  For example, if the translation region is 64KB, the remapped address applies only to the upper
  address bits that select which 64KB to be translated.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name              | Offset   |
|:------------------|:---------|
| IBUS_REMAP_ADDR_0 | 0x24     |
| IBUS_REMAP_ADDR_1 | 0x28     |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description      |
|:------:|:------:|:-------:|:-------|:-----------------|
|  31:0  |   rw   |   0x0   | VAL    | Remap addr value |

## DBUS_REGWEN
Dbus address control regwen.
- Reset default: `0x1`
- Reset mask: `0x1`

### Instances

| Name          | Offset   |
|:--------------|:---------|
| DBUS_REGWEN_0 | 0x2c     |
| DBUS_REGWEN_1 | 0x30     |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                   |
|:------:|:------:|:-------:|:-----------------------|
|  31:1  |        |         | Reserved               |
|   0    |  rw0c  |   0x1   | [EN](#dbus_regwen--en) |

### DBUS_REGWEN . EN
Ibus address controls write enable.  Once set to 0, it can longer be configured to 1

| Value   | Name    | Description                                                    |
|:--------|:--------|:---------------------------------------------------------------|
| 0x0     | locked  | Address controls can no longer be configured until next reset. |
| 0x1     | enabled | Address controls can still be configured.                      |


## DBUS_ADDR_EN
Enable dbus address matching
- Reset default: `0x0`
- Reset mask: `0x1`

### Instances

| Name           | Offset   |
|:---------------|:---------|
| DBUS_ADDR_EN_0 | 0x34     |
| DBUS_ADDR_EN_1 | 0x38     |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                   |
|:------:|:------:|:-------:|:-------|:------------------------------|
|  31:1  |        |         |        | Reserved                      |
|   0    |   rw   |   0x0   | EN     | Enable dbus address matching. |

## DBUS_ADDR_MATCHING
See [`IBUS_ADDR_MATCHING_0`](#ibus_addr_matching_0) for detailed description.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                 | Offset   |
|:---------------------|:---------|
| DBUS_ADDR_MATCHING_0 | 0x3c     |
| DBUS_ADDR_MATCHING_1 | 0x40     |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description           |
|:------:|:------:|:-------:|:-------|:----------------------|
|  31:0  |   rw   |   0x0   | VAL    | Matching region value |

## DBUS_REMAP_ADDR
See [`IBUS_REMAP_ADDR_0`](#ibus_remap_addr_0) for a detailed description.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name              | Offset   |
|:------------------|:---------|
| DBUS_REMAP_ADDR_0 | 0x44     |
| DBUS_REMAP_ADDR_1 | 0x48     |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description      |
|:------:|:------:|:-------:|:-------|:-----------------|
|  31:0  |   rw   |   0x0   | VAL    | Remap addr value |

## NMI_ENABLE
Enable mask for NMI.
Once an enable mask is set, it cannot be disabled.
- Offset: `0x4c`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "ALERT_EN", "bits": 1, "attr": ["rw1s"], "rotate": -90}, {"name": "WDOG_EN", "bits": 1, "attr": ["rw1s"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                  |
|:------:|:------:|:-------:|:---------|:-----------------------------|
|  31:2  |        |         |          | Reserved                     |
|   1    |  rw1s  |   0x0   | WDOG_EN  | Enable mask for watchdog NMI |
|   0    |  rw1s  |   0x0   | ALERT_EN | Enable mask for alert NMI    |

## NMI_STATE
Current NMI state
- Offset: `0x50`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "ALERT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "WDOG", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                    |
|:------:|:------:|:-------:|:-------|:-------------------------------|
|  31:2  |        |         |        | Reserved                       |
|   1    |  rw1c  |   0x0   | WDOG   | Current state for watchdog NMI |
|   0    |  rw1c  |   0x0   | ALERT  | Current state for alert NMI    |

## ERR_STATUS
error status
- Offset: `0x54`
- Reset default: `0x0`
- Reset mask: `0x701`

### Fields

```wavejson
{"reg": [{"name": "REG_INTG_ERR", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 7}, {"name": "FATAL_INTG_ERR", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "FATAL_CORE_ERR", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "RECOV_CORE_ERR", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 21}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                                                                              |
|:------:|:------:|:-------:|:---------------|:-----------------------------------------------------------------------------------------|
| 31:11  |        |         |                | Reserved                                                                                 |
|   10   |  rw1c  |   0x0   | RECOV_CORE_ERR | rv_core_ibex detected a recoverable internal error (``alert_minor`` from Ibex seen)      |
|   9    |  rw1c  |   0x0   | FATAL_CORE_ERR | rv_core_ibex detected a fatal internal error (``alert_major_internal_o`` from Ibex seen) |
|   8    |  rw1c  |   0x0   | FATAL_INTG_ERR | rv_core_ibex detected a response integrity error                                         |
|  7:1   |        |         |                | Reserved                                                                                 |
|   0    |  rw1c  |   0x0   | REG_INTG_ERR   | rv_core_ibex_peri detected a register transmission integrity error                       |

## RND_DATA
Random data from EDN
- Offset: `0x58`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "DATA", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                    |
|:------:|:------:|:-------:|:------------------------|
|  31:0  |   ro   |   0x0   | [DATA](#rnd_data--data) |

### RND_DATA . DATA
Random bits taken from the EDN. [`RND_STATUS.RND_DATA_VALID`](#rnd_status)
indicates if this data is valid. When valid, reading from this
register invalidates the data and requests new data from the EDN.
The register becomes valid again when the EDN provides new data.
When invalid the register value will read as 0x0 with an EDN
request for new data pending. Upon reset the data will be invalid
with a new EDN request pending.

## RND_STATUS
Status of random data in [`RND_DATA`](#rnd_data)
- Offset: `0x5c`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "RND_DATA_VALID", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "RND_DATA_FIPS", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                                                                                                                                                                                               |
|:------:|:------:|:-------:|:---------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:2  |        |         |                | Reserved                                                                                                                                                                                                  |
|   1    |   ro   |   0x0   | RND_DATA_FIPS  | When [`RND_STATUS.RND_DATA_VALID`](#rnd_status) is 1, this bit indicates whether [`RND_DATA`](#rnd_data) is fips quality.  When [`RND_STATUS.RND_DATA_VALID`](#rnd_status) is 0, this bit has no meaning. |
|   0    |   ro   |   0x0   | RND_DATA_VALID | When set, the data in [`RND_DATA`](#rnd_data) is valid. When clear an EDN request for new data for [`RND_DATA`](#rnd_data) is pending.                                                                    |

## FPGA_INFO
FPGA build timestamp info.
This register only contains valid data for fpga, for all other variants it is simply 0.
- Offset: `0x60`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                       |
|:------:|:------:|:-------:|:-------|:----------------------------------|
|  31:0  |   ro   |   0x0   | VAL    | FPGA build timestamp information. |

## DV_SIM_WINDOW
Exposed tlul window for DV only purposes.

- Word Aligned Offset Range: `0x80`to`0x9c`
- Size (words): `8`
- Access: `rw`
- Byte writes are  supported.


<!-- END CMDGEN -->
