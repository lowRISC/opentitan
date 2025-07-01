# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/top_darjeeling/ip_autogen/clkmgr/data/clkmgr.hjson -->
## Summary

| Name                                                               | Offset   |   Length | Description                                                                              |
|:-------------------------------------------------------------------|:---------|---------:|:-----------------------------------------------------------------------------------------|
| clkmgr.[`ALERT_TEST`](#alert_test)                                 | 0x0      |        4 | Alert Test Register                                                                      |
| clkmgr.[`EXTCLK_CTRL_REGWEN`](#extclk_ctrl_regwen)                 | 0x4      |        4 | External clock control write enable                                                      |
| clkmgr.[`EXTCLK_CTRL`](#extclk_ctrl)                               | 0x8      |        4 | Select external clock                                                                    |
| clkmgr.[`EXTCLK_STATUS`](#extclk_status)                           | 0xc      |        4 | Status of requested external clock switch                                                |
| clkmgr.[`JITTER_REGWEN`](#jitter_regwen)                           | 0x10     |        4 | Jitter write enable                                                                      |
| clkmgr.[`JITTER_ENABLE`](#jitter_enable)                           | 0x14     |        4 | Enable jittery clock                                                                     |
| clkmgr.[`CLK_ENABLES`](#clk_enables)                               | 0x18     |        4 | Clock enable for software gateable clocks.                                               |
| clkmgr.[`CLK_HINTS`](#clk_hints)                                   | 0x1c     |        4 | Clock hint for software gateable transactional clocks during active mode.                |
| clkmgr.[`CLK_HINTS_STATUS`](#clk_hints_status)                     | 0x20     |        4 | Since the final state of [`CLK_HINTS`](#clk_hints) is not always determined by software, |
| clkmgr.[`MEASURE_CTRL_REGWEN`](#measure_ctrl_regwen)               | 0x24     |        4 | Measurement control write enable                                                         |
| clkmgr.[`IO_DIV4_MEAS_CTRL_EN`](#io_div4_meas_ctrl_en)             | 0x28     |        4 | Enable for measurement control                                                           |
| clkmgr.[`IO_DIV4_MEAS_CTRL_SHADOWED`](#io_div4_meas_ctrl_shadowed) | 0x2c     |        4 | Configuration controls for io_div4 measurement.                                          |
| clkmgr.[`MAIN_MEAS_CTRL_EN`](#main_meas_ctrl_en)                   | 0x30     |        4 | Enable for measurement control                                                           |
| clkmgr.[`MAIN_MEAS_CTRL_SHADOWED`](#main_meas_ctrl_shadowed)       | 0x34     |        4 | Configuration controls for main measurement.                                             |
| clkmgr.[`RECOV_ERR_CODE`](#recov_err_code)                         | 0x38     |        4 | Recoverable Error code                                                                   |
| clkmgr.[`FATAL_ERR_CODE`](#fatal_err_code)                         | 0x3c     |        4 | Error code                                                                               |

## ALERT_TEST
Alert Test Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "recov_fault", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_fault", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                      |
|:------:|:------:|:-------:|:------------|:-------------------------------------------------|
|  31:2  |        |         |             | Reserved                                         |
|   1    |   wo   |   0x0   | fatal_fault | Write 1 to trigger one alert event of this kind. |
|   0    |   wo   |   0x0   | recov_fault | Write 1 to trigger one alert event of this kind. |

## EXTCLK_CTRL_REGWEN
External clock control write enable
- Offset: `0x4`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                     |
|:------:|:------:|:-------:|:-------|:--------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                                                        |
|   0    |  rw0c  |   0x1   | EN     | When 1, the value of [`EXTCLK_CTRL`](#extclk_ctrl) can be set.  When 0, writes to [`EXTCLK_CTRL`](#extclk_ctrl) have no effect. |

## EXTCLK_CTRL
Select external clock
- Offset: `0x8`
- Reset default: `0x99`
- Reset mask: `0xff`
- Register enable: [`EXTCLK_CTRL_REGWEN`](#extclk_ctrl_regwen)

### Fields

```wavejson
{"reg": [{"name": "SEL", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "HI_SPEED_SEL", "bits": 4, "attr": ["rw"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name                                       |
|:------:|:------:|:-------:|:-------------------------------------------|
|  31:8  |        |         | Reserved                                   |
|  7:4   |   rw   |   0x9   | [HI_SPEED_SEL](#extclk_ctrl--hi_speed_sel) |
|  3:0   |   rw   |   0x9   | [SEL](#extclk_ctrl--sel)                   |

### EXTCLK_CTRL . HI_SPEED_SEL
A value of kMultiBitBool4True selects nominal speed external clock.
All other values selects low speed clocks.

Note this field only has an effect when the [`EXTCLK_CTRL.SEL`](#extclk_ctrl) field is set to
kMultiBitBool4True.

Nominal speed means the external clock is approximately the same frequency as
the internal oscillator source.  When this option is used, all clocks operate
at roughly the nominal frequency.

Low speed means the external clock is approximately half the frequency of the
internal oscillator source. When this option is used, the internal dividers are
stepped down.  As a result, previously undivided clocks now run at half frequency,
while previously divided clocks run at roughly the nominal frequency.

See external clock switch support in documentation for more details.

### EXTCLK_CTRL . SEL
When the current value is not kMultiBitBool4True, writing a value of kMultiBitBool4True
selects external clock as clock for the system.  Writing any other value has
no impact.

When the current value is kMultiBitBool4True, writing a value of kMultiBitBool4False
selects internal clock as clock for the system. Writing any other value during this stage
has no impact.

While this register can always be programmed, it only takes effect when debug functions are enabled
in life cycle TEST, DEV or RMA states.

## EXTCLK_STATUS
Status of requested external clock switch
- Offset: `0xc`
- Reset default: `0x9`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "ACK", "bits": 4, "attr": ["ro"], "rotate": 0}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                       |
|:------:|:------:|:-------:|:---------------------------|
|  31:4  |        |         | Reserved                   |
|  3:0   |   ro   |   0x9   | [ACK](#extclk_status--ack) |

### EXTCLK_STATUS . ACK
When [`EXTCLK_CTRL.SEL`](#extclk_ctrl) is set to kMultiBitBool4True, this field reflects
whether the clock has been switched the external source.

kMultiBitBool4True indicates the switch is complete.
kMultiBitBool4False indicates the switch is either not possible or still ongoing.

## JITTER_REGWEN
Jitter write enable
- Offset: `0x10`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                            |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                               |
|   0    |  rw0c  |   0x1   | EN     | When 1, the value of [`JITTER_ENABLE`](#jitter_enable) can be changed.  When 0, writes have no effect. |

## JITTER_ENABLE
Enable jittery clock
- Offset: `0x14`
- Reset default: `0x9`
- Reset mask: `0xf`
- Register enable: [`JITTER_REGWEN`](#jitter_regwen)

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                   |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------------------------------------------------------------------------|
|  31:4  |        |         |        | Reserved                                                                                                                      |
|  3:0   |   rw   |   0x9   | VAL    | Enable jittery clock. A value of kMultiBitBool4False disables the jittery clock, while all other values enable jittery clock. |

## CLK_ENABLES
Clock enable for software gateable clocks.
These clocks are directly controlled by software.
- Offset: `0x18`
- Reset default: `0x3`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "CLK_IO_DIV4_PERI_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CLK_IO_DIV2_PERI_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 210}}
```

|  Bits  |  Type  |  Reset  | Name                | Description                                                    |
|:------:|:------:|:-------:|:--------------------|:---------------------------------------------------------------|
|  31:2  |        |         |                     | Reserved                                                       |
|   1    |   rw   |   0x1   | CLK_IO_DIV2_PERI_EN | 0 CLK_IO_DIV2_PERI is disabled. 1 CLK_IO_DIV2_PERI is enabled. |
|   0    |   rw   |   0x1   | CLK_IO_DIV4_PERI_EN | 0 CLK_IO_DIV4_PERI is disabled. 1 CLK_IO_DIV4_PERI is enabled. |

## CLK_HINTS
Clock hint for software gateable transactional clocks during active mode.
During low power mode, all clocks are gated off regardless of the software hint.

Transactional clocks are not fully controlled by software.  Instead software provides only a disable hint.

When software provides a disable hint, the clock manager checks to see if the associated hardware block is idle.
If the hardware block is idle, then the clock is disabled.
If the hardware block is not idle, the clock is kept on.

For the enable case, the software hint is immediately honored and the clock turned on.  Hardware does not provide any
feedback in this case.
- Offset: `0x1c`
- Reset default: `0xf`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "CLK_MAIN_AES_HINT", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CLK_MAIN_HMAC_HINT", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CLK_MAIN_KMAC_HINT", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CLK_MAIN_OTBN_HINT", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                                  |
|:------:|:------:|:-------:|:-------------------|:-------------------------------------------------------------|
|  31:4  |        |         |                    | Reserved                                                     |
|   3    |   rw   |   0x1   | CLK_MAIN_OTBN_HINT | 0 CLK_MAIN_OTBN can be disabled. 1 CLK_MAIN_OTBN is enabled. |
|   2    |   rw   |   0x1   | CLK_MAIN_KMAC_HINT | 0 CLK_MAIN_KMAC can be disabled. 1 CLK_MAIN_KMAC is enabled. |
|   1    |   rw   |   0x1   | CLK_MAIN_HMAC_HINT | 0 CLK_MAIN_HMAC can be disabled. 1 CLK_MAIN_HMAC is enabled. |
|   0    |   rw   |   0x1   | CLK_MAIN_AES_HINT  | 0 CLK_MAIN_AES can be disabled. 1 CLK_MAIN_AES is enabled.   |

## CLK_HINTS_STATUS
Since the final state of [`CLK_HINTS`](#clk_hints) is not always determined by software,
this register provides read feedback for the current clock state.

- Offset: `0x20`
- Reset default: `0xf`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "CLK_MAIN_AES_VAL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CLK_MAIN_HMAC_VAL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CLK_MAIN_KMAC_VAL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CLK_MAIN_OTBN_VAL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                                              |
|:------:|:------:|:-------:|:------------------|:---------------------------------------------------------|
|  31:4  |        |         |                   | Reserved                                                 |
|   3    |   ro   |   0x1   | CLK_MAIN_OTBN_VAL | 0 CLK_MAIN_OTBN is disabled. 1 CLK_MAIN_OTBN is enabled. |
|   2    |   ro   |   0x1   | CLK_MAIN_KMAC_VAL | 0 CLK_MAIN_KMAC is disabled. 1 CLK_MAIN_KMAC is enabled. |
|   1    |   ro   |   0x1   | CLK_MAIN_HMAC_VAL | 0 CLK_MAIN_HMAC is disabled. 1 CLK_MAIN_HMAC is enabled. |
|   0    |   ro   |   0x1   | CLK_MAIN_AES_VAL  | 0 CLK_MAIN_AES is disabled. 1 CLK_MAIN_AES is enabled.   |

## MEASURE_CTRL_REGWEN
Measurement control write enable
- Offset: `0x24`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                              |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                 |
|   0    |  rw0c  |   0x1   | EN     | When 1, the value of the measurement control can be set.  When 0, writes have no effect. |

## IO_DIV4_MEAS_CTRL_EN
Enable for measurement control
- Offset: `0x28`
- Reset default: `0x9`
- Reset mask: `0xf`
- Register enable: [`MEASURE_CTRL_REGWEN`](#measure_ctrl_regwen)

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                    |
|:------:|:------:|:-------:|:-------|:-------------------------------|
|  31:4  |        |         |        | Reserved                       |
|  3:0   |   rw   |   0x9   | EN     | Enable measurement for io_div4 |

## IO_DIV4_MEAS_CTRL_SHADOWED
Configuration controls for io_div4 measurement.

The threshold fields are made wider than required (by 1 bit) to ensure
there is room to adjust for measurement inaccuracies.
- Offset: `0x2c`
- Reset default: `0xec8a`
- Reset mask: `0x3ffff`
- Register enable: [`MEASURE_CTRL_REGWEN`](#measure_ctrl_regwen)

### Fields

```wavejson
{"reg": [{"name": "HI", "bits": 9, "attr": ["rw"], "rotate": 0}, {"name": "LO", "bits": 9, "attr": ["rw"], "rotate": 0}, {"bits": 14}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                           |
|:------:|:------:|:-------:|:-------|:--------------------------------------|
| 31:18  |        |         |        | Reserved                              |
|  17:9  |   rw   |  0x76   | LO     | Min threshold for io_div4 measurement |
|  8:0   |   rw   |  0x8a   | HI     | Max threshold for io_div4 measurement |

## MAIN_MEAS_CTRL_EN
Enable for measurement control
- Offset: `0x30`
- Reset default: `0x9`
- Reset mask: `0xf`
- Register enable: [`MEASURE_CTRL_REGWEN`](#measure_ctrl_regwen)

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                 |
|:------:|:------:|:-------:|:-------|:----------------------------|
|  31:4  |        |         |        | Reserved                    |
|  3:0   |   rw   |   0x9   | EN     | Enable measurement for main |

## MAIN_MEAS_CTRL_SHADOWED
Configuration controls for main measurement.

The threshold fields are made wider than required (by 1 bit) to ensure
there is room to adjust for measurement inaccuracies.
- Offset: `0x34`
- Reset default: `0xec8a`
- Reset mask: `0x3ffff`
- Register enable: [`MEASURE_CTRL_REGWEN`](#measure_ctrl_regwen)

### Fields

```wavejson
{"reg": [{"name": "HI", "bits": 9, "attr": ["rw"], "rotate": 0}, {"name": "LO", "bits": 9, "attr": ["rw"], "rotate": 0}, {"bits": 14}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                        |
|:------:|:------:|:-------:|:-------|:-----------------------------------|
| 31:18  |        |         |        | Reserved                           |
|  17:9  |   rw   |  0x76   | LO     | Min threshold for main measurement |
|  8:0   |   rw   |  0x8a   | HI     | Max threshold for main measurement |

## RECOV_ERR_CODE
Recoverable Error code
- Offset: `0x38`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "SHADOW_UPDATE_ERR", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "IO_DIV4_MEASURE_ERR", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "MAIN_MEASURE_ERR", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "IO_DIV4_TIMEOUT_ERR", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "MAIN_TIMEOUT_ERR", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 210}}
```

|  Bits  |  Type  |  Reset  | Name                | Description                                              |
|:------:|:------:|:-------:|:--------------------|:---------------------------------------------------------|
|  31:5  |        |         |                     | Reserved                                                 |
|   4    |  rw1c  |   0x0   | MAIN_TIMEOUT_ERR    | main has timed out.                                      |
|   3    |  rw1c  |   0x0   | IO_DIV4_TIMEOUT_ERR | io_div4 has timed out.                                   |
|   2    |  rw1c  |   0x0   | MAIN_MEASURE_ERR    | main has encountered a measurement error.                |
|   1    |  rw1c  |   0x0   | IO_DIV4_MEASURE_ERR | io_div4 has encountered a measurement error.             |
|   0    |  rw1c  |   0x0   | SHADOW_UPDATE_ERR   | One of the shadow registers encountered an update error. |

## FATAL_ERR_CODE
Error code
- Offset: `0x3c`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "REG_INTG", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "IDLE_CNT", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SHADOW_STORAGE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                              |
|:------:|:------:|:-------:|:-------------------|:---------------------------------------------------------|
|  31:3  |        |         |                    | Reserved                                                 |
|   2    |   ro   |   0x0   | SHADOW_STORAGE_ERR | One of the shadow registers encountered a storage error. |
|   1    |   ro   |   0x0   | IDLE_CNT           | One of the idle counts encountered a duplicate error.    |
|   0    |   ro   |   0x0   | REG_INTG           | Register file has experienced a fatal integrity error.   |


<!-- END CMDGEN -->
