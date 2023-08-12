# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/gpio/data/gpio.hjson -->
## Summary

| Name                                                 | Offset   |   Length | Description                                   |
|:-----------------------------------------------------|:---------|---------:|:----------------------------------------------|
| gpio.[`INTR_STATE`](#intr_state)                     | 0x0      |        4 | Interrupt State Register                      |
| gpio.[`INTR_ENABLE`](#intr_enable)                   | 0x4      |        4 | Interrupt Enable Register                     |
| gpio.[`INTR_TEST`](#intr_test)                       | 0x8      |        4 | Interrupt Test Register                       |
| gpio.[`ALERT_TEST`](#alert_test)                     | 0xc      |        4 | Alert Test Register                           |
| gpio.[`DATA_IN`](#data_in)                           | 0x10     |        4 | GPIO Input data read value                    |
| gpio.[`DIRECT_OUT`](#direct_out)                     | 0x14     |        4 | GPIO direct output data write value           |
| gpio.[`MASKED_OUT_LOWER`](#masked_out_lower)         | 0x18     |        4 | GPIO write data lower with mask.              |
| gpio.[`MASKED_OUT_UPPER`](#masked_out_upper)         | 0x1c     |        4 | GPIO write data upper with mask.              |
| gpio.[`DIRECT_OE`](#direct_oe)                       | 0x20     |        4 | GPIO Output Enable.                           |
| gpio.[`MASKED_OE_LOWER`](#masked_oe_lower)           | 0x24     |        4 | GPIO write Output Enable lower with mask.     |
| gpio.[`MASKED_OE_UPPER`](#masked_oe_upper)           | 0x28     |        4 | GPIO write Output Enable upper with mask.     |
| gpio.[`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)   | 0x2c     |        4 | GPIO interrupt enable for GPIO, rising edge.  |
| gpio.[`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling) | 0x30     |        4 | GPIO interrupt enable for GPIO, falling edge. |
| gpio.[`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh) | 0x34     |        4 | GPIO interrupt enable for GPIO, level high.   |
| gpio.[`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)   | 0x38     |        4 | GPIO interrupt enable for GPIO, level low.    |
| gpio.[`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter) | 0x3c     |        4 | filter enable for GPIO input bits.            |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "gpio", "bits": 32, "attr": ["rw1c"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                 |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------|
|  31:0  |  rw1c  |   0x0   | gpio   | raised if any of GPIO pin detects configured interrupt mode |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "gpio", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                         |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | gpio   | Enable interrupt when corresponding bit in [`INTR_STATE.gpio`](#intr_state) is set. |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "gpio", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                  |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------|
|  31:0  |   wo   |   0x0   | gpio   | Write 1 to force corresponding bit in [`INTR_STATE.gpio`](#intr_state) to 1. |

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

## DATA_IN
GPIO Input data read value
- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "DATA_IN", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name    | Description   |
|:------:|:------:|:-------:|:--------|:--------------|
|  31:0  |   ro   |    x    | DATA_IN |               |

## DIRECT_OUT
GPIO direct output data write value
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "DIRECT_OUT", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description   |
|:------:|:------:|:-------:|:-----------|:--------------|
|  31:0  |   rw   |    x    | DIRECT_OUT |               |

## MASKED_OUT_LOWER
GPIO write data lower with mask.

Masked write for DATA_OUT[15:0].

Upper 16 bits of this register are used as mask. Writing
lower 16 bits of the register changes DATA_OUT[15:0] value
if mask bits are set.

Read-back of this register returns upper 16 bits as zero
and lower 16 bits as DATA_OUT[15:0].
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "data", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "mask", "bits": 16, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------------------------------------------------------|
| 31:16  |   wo   |    x    | mask   | Write data mask[15:0].  A value of 1 in mask[i] allows the updating of DATA_OUT[i], 0 <= i <= 15 |
|  15:0  |   rw   |    x    | data   | Write data value[15:0].  Value to write into DATA_OUT[i], valid in the presence of mask[i]==1    |

## MASKED_OUT_UPPER
GPIO write data upper with mask.

Masked write for DATA_OUT[31:16].

Upper 16 bits of this register are used as mask. Writing
lower 16 bits of the register changes DATA_OUT[31:16] value
if mask bits are set.

Read-back of this register returns upper 16 bits as zero
and lower 16 bits as DATA_OUT[31:16].
- Offset: `0x1c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "data", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "mask", "bits": 16, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                        |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------------------------|
| 31:16  |   wo   |    x    | mask   | Write data mask[31:16].  A value of 1 in mask[i] allows the updating of DATA_OUT[i], 16 <= i <= 31 |
|  15:0  |   rw   |    x    | data   | Write data value[31:16].     Value to write into DATA_OUT[i], valid in the presence of mask[i]==1  |

## DIRECT_OE
GPIO Output Enable.

Setting direct_oe[i] to 1 enables output mode for GPIO[i]
- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "DIRECT_OE", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name      | Description   |
|:------:|:------:|:-------:|:----------|:--------------|
|  31:0  |   rw   |    x    | DIRECT_OE |               |

## MASKED_OE_LOWER
GPIO write Output Enable lower with mask.

Masked write for DATA_OE[15:0], the register that controls
output mode for GPIO pins [15:0].

Upper 16 bits of this register are used as mask. Writing
lower 16 bits of the register changes DATA_OE[15:0] value
if mask bits are set.

Read-back of this register returns upper 16 bits as zero
and lower 16 bits as DATA_OE[15:0].
- Offset: `0x24`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "data", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "mask", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                   |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------------|
| 31:16  |   rw   |    x    | mask   | Write OE mask[15:0].  A value of 1 in mask[i] allows the updating of DATA_OE[i], 0 <= i <= 15 |
|  15:0  |   rw   |    x    | data   | Write OE value[15:0].  Value to write into DATA_OE[i], valid in the presence of mask[i]==1    |

## MASKED_OE_UPPER
GPIO write Output Enable upper with mask.

Masked write for DATA_OE[31:16], the register that controls
output mode for GPIO pins [31:16].

Upper 16 bits of this register are used as mask. Writing
lower 16 bits of the register changes DATA_OE[31:16] value
if mask bits are set.

Read-back of this register returns upper 16 bits as zero
and lower 16 bits as DATA_OE[31:16].
- Offset: `0x28`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "data", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "mask", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                     |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------------------------------------------|
| 31:16  |   rw   |    x    | mask   | Write OE mask[31:16].  A value of 1 in mask[i] allows the updating of DATA_OE[i], 16 <= i <= 31 |
|  15:0  |   rw   |    x    | data   | Write OE value[31:16].  Value to write into DATA_OE[i], valid in the presence of mask[i]==1     |

## INTR_CTRL_EN_RISING
GPIO interrupt enable for GPIO, rising edge.

If [`INTR_ENABLE`](#intr_enable)[i] is true, a value of 1 on [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[i]
enables rising-edge interrupt detection on GPIO[i].
- Offset: `0x2c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "INTR_CTRL_EN_RISING", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                | Description   |
|:------:|:------:|:-------:|:--------------------|:--------------|
|  31:0  |   rw   |   0x0   | INTR_CTRL_EN_RISING |               |

## INTR_CTRL_EN_FALLING
GPIO interrupt enable for GPIO, falling edge.

If [`INTR_ENABLE`](#intr_enable)[i] is true, a value of 1 on [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[i]
enables falling-edge interrupt detection on GPIO[i].
- Offset: `0x30`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "INTR_CTRL_EN_FALLING", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description   |
|:------:|:------:|:-------:|:---------------------|:--------------|
|  31:0  |   rw   |   0x0   | INTR_CTRL_EN_FALLING |               |

## INTR_CTRL_EN_LVLHIGH
GPIO interrupt enable for GPIO, level high.

If [`INTR_ENABLE`](#intr_enable)[i] is true, a value of 1 on [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[i]
enables level high interrupt detection on GPIO[i].
- Offset: `0x34`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "INTR_CTRL_EN_LVLHIGH", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description   |
|:------:|:------:|:-------:|:---------------------|:--------------|
|  31:0  |   rw   |   0x0   | INTR_CTRL_EN_LVLHIGH |               |

## INTR_CTRL_EN_LVLLOW
GPIO interrupt enable for GPIO, level low.

If [`INTR_ENABLE`](#intr_enable)[i] is true, a value of 1 on [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[i]
enables level low interrupt detection on GPIO[i].
- Offset: `0x38`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "INTR_CTRL_EN_LVLLOW", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                | Description   |
|:------:|:------:|:-------:|:--------------------|:--------------|
|  31:0  |   rw   |   0x0   | INTR_CTRL_EN_LVLLOW |               |

## CTRL_EN_INPUT_FILTER
filter enable for GPIO input bits.

If [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[i] is true, a value of input bit [i]
must be stable for 16 cycles before transitioning.
- Offset: `0x3c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "CTRL_EN_INPUT_FILTER", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description   |
|:------:|:------:|:-------:|:---------------------|:--------------|
|  31:0  |   rw   |   0x0   | CTRL_EN_INPUT_FILTER |               |


<!-- END CMDGEN -->
