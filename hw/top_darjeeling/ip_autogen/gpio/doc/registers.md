# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/top_darjeeling/ip_autogen/gpio/data/gpio.hjson -->
## Summary

| Name                                                       | Offset   |   Length | Description                                                                       |
|:-----------------------------------------------------------|:---------|---------:|:----------------------------------------------------------------------------------|
| gpio.[`INTR_STATE`](#intr_state)                           | 0x0      |        4 | Interrupt State Register                                                          |
| gpio.[`INTR_ENABLE`](#intr_enable)                         | 0x4      |        4 | Interrupt Enable Register                                                         |
| gpio.[`INTR_TEST`](#intr_test)                             | 0x8      |        4 | Interrupt Test Register                                                           |
| gpio.[`ALERT_TEST`](#alert_test)                           | 0xc      |        4 | Alert Test Register                                                               |
| gpio.[`DATA_IN`](#data_in)                                 | 0x10     |        4 | GPIO Input data read value                                                        |
| gpio.[`DIRECT_OUT`](#direct_out)                           | 0x14     |        4 | GPIO direct output data write value                                               |
| gpio.[`MASKED_OUT_LOWER`](#masked_out_lower)               | 0x18     |        4 | GPIO write data lower with mask.                                                  |
| gpio.[`MASKED_OUT_UPPER`](#masked_out_upper)               | 0x1c     |        4 | GPIO write data upper with mask.                                                  |
| gpio.[`DIRECT_OE`](#direct_oe)                             | 0x20     |        4 | GPIO Output Enable.                                                               |
| gpio.[`MASKED_OE_LOWER`](#masked_oe_lower)                 | 0x24     |        4 | GPIO write Output Enable lower with mask.                                         |
| gpio.[`MASKED_OE_UPPER`](#masked_oe_upper)                 | 0x28     |        4 | GPIO write Output Enable upper with mask.                                         |
| gpio.[`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)         | 0x2c     |        4 | GPIO interrupt enable for GPIO, rising edge.                                      |
| gpio.[`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)       | 0x30     |        4 | GPIO interrupt enable for GPIO, falling edge.                                     |
| gpio.[`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)       | 0x34     |        4 | GPIO interrupt enable for GPIO, level high.                                       |
| gpio.[`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)         | 0x38     |        4 | GPIO interrupt enable for GPIO, level low.                                        |
| gpio.[`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)       | 0x3c     |        4 | filter enable for GPIO input bits.                                                |
| gpio.[`HW_STRAPS_DATA_IN_VALID`](#hw_straps_data_in_valid) | 0x40     |        4 | Indicates whether the data in [`HW_STRAPS_DATA_IN`](#hw_straps_data_in) is valid. |
| gpio.[`HW_STRAPS_DATA_IN`](#hw_straps_data_in)             | 0x44     |        4 | GPIO input data that was sampled as straps at most once after the block           |
| gpio.[`INP_PRD_CNT_CTRL_0`](#inp_prd_cnt_ctrl)             | 0x48     |        4 | Control register of one input period counter.                                     |
| gpio.[`INP_PRD_CNT_CTRL_1`](#inp_prd_cnt_ctrl)             | 0x4c     |        4 | Control register of one input period counter.                                     |
| gpio.[`INP_PRD_CNT_CTRL_2`](#inp_prd_cnt_ctrl)             | 0x50     |        4 | Control register of one input period counter.                                     |
| gpio.[`INP_PRD_CNT_CTRL_3`](#inp_prd_cnt_ctrl)             | 0x54     |        4 | Control register of one input period counter.                                     |
| gpio.[`INP_PRD_CNT_CTRL_4`](#inp_prd_cnt_ctrl)             | 0x58     |        4 | Control register of one input period counter.                                     |
| gpio.[`INP_PRD_CNT_CTRL_5`](#inp_prd_cnt_ctrl)             | 0x5c     |        4 | Control register of one input period counter.                                     |
| gpio.[`INP_PRD_CNT_CTRL_6`](#inp_prd_cnt_ctrl)             | 0x60     |        4 | Control register of one input period counter.                                     |
| gpio.[`INP_PRD_CNT_CTRL_7`](#inp_prd_cnt_ctrl)             | 0x64     |        4 | Control register of one input period counter.                                     |
| gpio.[`INP_PRD_CNT_VAL_0`](#inp_prd_cnt_val)               | 0x68     |        4 | Output value of one input period counter.                                         |
| gpio.[`INP_PRD_CNT_VAL_1`](#inp_prd_cnt_val)               | 0x6c     |        4 | Output value of one input period counter.                                         |
| gpio.[`INP_PRD_CNT_VAL_2`](#inp_prd_cnt_val)               | 0x70     |        4 | Output value of one input period counter.                                         |
| gpio.[`INP_PRD_CNT_VAL_3`](#inp_prd_cnt_val)               | 0x74     |        4 | Output value of one input period counter.                                         |
| gpio.[`INP_PRD_CNT_VAL_4`](#inp_prd_cnt_val)               | 0x78     |        4 | Output value of one input period counter.                                         |
| gpio.[`INP_PRD_CNT_VAL_5`](#inp_prd_cnt_val)               | 0x7c     |        4 | Output value of one input period counter.                                         |
| gpio.[`INP_PRD_CNT_VAL_6`](#inp_prd_cnt_val)               | 0x80     |        4 | Output value of one input period counter.                                         |
| gpio.[`INP_PRD_CNT_VAL_7`](#inp_prd_cnt_val)               | 0x84     |        4 | Output value of one input period counter.                                         |
| gpio.[`PER_PIN_IO_0`](#per_pin_io)                         | 0x100    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_1`](#per_pin_io)                         | 0x104    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_2`](#per_pin_io)                         | 0x108    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_3`](#per_pin_io)                         | 0x10c    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_4`](#per_pin_io)                         | 0x110    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_5`](#per_pin_io)                         | 0x114    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_6`](#per_pin_io)                         | 0x118    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_7`](#per_pin_io)                         | 0x11c    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_8`](#per_pin_io)                         | 0x120    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_9`](#per_pin_io)                         | 0x124    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_10`](#per_pin_io)                        | 0x128    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_11`](#per_pin_io)                        | 0x12c    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_12`](#per_pin_io)                        | 0x130    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_13`](#per_pin_io)                        | 0x134    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_14`](#per_pin_io)                        | 0x138    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_15`](#per_pin_io)                        | 0x13c    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_16`](#per_pin_io)                        | 0x140    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_17`](#per_pin_io)                        | 0x144    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_18`](#per_pin_io)                        | 0x148    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_19`](#per_pin_io)                        | 0x14c    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_20`](#per_pin_io)                        | 0x150    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_21`](#per_pin_io)                        | 0x154    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_22`](#per_pin_io)                        | 0x158    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_23`](#per_pin_io)                        | 0x15c    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_24`](#per_pin_io)                        | 0x160    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_25`](#per_pin_io)                        | 0x164    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_26`](#per_pin_io)                        | 0x168    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_27`](#per_pin_io)                        | 0x16c    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_28`](#per_pin_io)                        | 0x170    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_29`](#per_pin_io)                        | 0x174    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_30`](#per_pin_io)                        | 0x178    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_IO_31`](#per_pin_io)                        | 0x17c    |        4 | Per-pin view of the output and input data of one GPIO.                            |
| gpio.[`PER_PIN_CFG_0`](#per_pin_cfg)                       | 0x200    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_1`](#per_pin_cfg)                       | 0x204    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_2`](#per_pin_cfg)                       | 0x208    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_3`](#per_pin_cfg)                       | 0x20c    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_4`](#per_pin_cfg)                       | 0x210    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_5`](#per_pin_cfg)                       | 0x214    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_6`](#per_pin_cfg)                       | 0x218    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_7`](#per_pin_cfg)                       | 0x21c    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_8`](#per_pin_cfg)                       | 0x220    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_9`](#per_pin_cfg)                       | 0x224    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_10`](#per_pin_cfg)                      | 0x228    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_11`](#per_pin_cfg)                      | 0x22c    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_12`](#per_pin_cfg)                      | 0x230    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_13`](#per_pin_cfg)                      | 0x234    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_14`](#per_pin_cfg)                      | 0x238    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_15`](#per_pin_cfg)                      | 0x23c    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_16`](#per_pin_cfg)                      | 0x240    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_17`](#per_pin_cfg)                      | 0x244    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_18`](#per_pin_cfg)                      | 0x248    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_19`](#per_pin_cfg)                      | 0x24c    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_20`](#per_pin_cfg)                      | 0x250    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_21`](#per_pin_cfg)                      | 0x254    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_22`](#per_pin_cfg)                      | 0x258    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_23`](#per_pin_cfg)                      | 0x25c    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_24`](#per_pin_cfg)                      | 0x260    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_25`](#per_pin_cfg)                      | 0x264    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_26`](#per_pin_cfg)                      | 0x268    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_27`](#per_pin_cfg)                      | 0x26c    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_28`](#per_pin_cfg)                      | 0x270    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_29`](#per_pin_cfg)                      | 0x274    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_30`](#per_pin_cfg)                      | 0x278    |        4 | Per-pin view of the configuration of one GPIO.                                    |
| gpio.[`PER_PIN_CFG_31`](#per_pin_cfg)                      | 0x27c    |        4 | Per-pin view of the configuration of one GPIO.                                    |

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

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                     |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------------------------------------------|
| 31:16  |   wo   |    x    | mask   | Write data mask[15:0]. A value of 1 in mask[i] allows the updating of DATA_OUT[i], 0 <= i <= 15 |
|  15:0  |   rw   |    x    | data   | Write data value[15:0]. Value to write into DATA_OUT[i], valid in the presence of mask[i]==1    |

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

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                       |
|:------:|:------:|:-------:|:-------|:--------------------------------------------------------------------------------------------------|
| 31:16  |   wo   |    x    | mask   | Write data mask[31:16]. A value of 1 in mask[i] allows the updating of DATA_OUT[i], 16 <= i <= 31 |
|  15:0  |   rw   |    x    | data   | Write data value[31:16]. Value to write into DATA_OUT[i], valid in the presence of mask[i]==1     |

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

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                  |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------------------|
| 31:16  |   rw   |    x    | mask   | Write OE mask[15:0]. A value of 1 in mask[i] allows the updating of DATA_OE[i], 0 <= i <= 15 |
|  15:0  |   rw   |    x    | data   | Write OE value[15:0]. Value to write into DATA_OE[i], valid in the presence of mask[i]==1    |

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

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                    |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------------|
| 31:16  |   rw   |    x    | mask   | Write OE mask[31:16]. A value of 1 in mask[i] allows the updating of DATA_OE[i], 16 <= i <= 31 |
|  15:0  |   rw   |    x    | data   | Write OE value[31:16]. Value to write into DATA_OE[i], valid in the presence of mask[i]==1     |

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
|  31:0  |   rw   |    x    | INTR_CTRL_EN_RISING |               |

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
|  31:0  |   rw   |    x    | INTR_CTRL_EN_FALLING |               |

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
|  31:0  |   rw   |    x    | INTR_CTRL_EN_LVLHIGH |               |

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
|  31:0  |   rw   |    x    | INTR_CTRL_EN_LVLLOW |               |

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
|  31:0  |   rw   |    x    | CTRL_EN_INPUT_FILTER |               |

## HW_STRAPS_DATA_IN_VALID
Indicates whether the data in [`HW_STRAPS_DATA_IN`](#hw_straps_data_in) is valid.
- Offset: `0x40`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "HW_STRAPS_DATA_IN_VALID", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 250}}
```

|  Bits  |  Type  |  Reset  | Name                    | Description   |
|:------:|:------:|:-------:|:------------------------|:--------------|
|  31:1  |        |         |                         | Reserved      |
|   0    |   ro   |   0x0   | HW_STRAPS_DATA_IN_VALID |               |

## HW_STRAPS_DATA_IN
GPIO input data that was sampled as straps at most once after the block
came out of reset.

The behavior of this register depends on the GpioAsHwStrapsEn parameter.
- If the parameter is false then the register reads as zero.
- If the parameter is true then GPIO input data is sampled after reset
on the first cycle where the strap_en_i input is high. The
sampled data is then stored in this register.
- Offset: `0x44`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "HW_STRAPS_DATA_IN", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name              | Description   |
|:------:|:------:|:-------:|:------------------|:--------------|
|  31:0  |   ro   |   0x0   | HW_STRAPS_DATA_IN |               |

## INP_PRD_CNT_CTRL
Control register of one input period counter.
- Reset default: `0x4`
- Reset mask: `0xffff07`

### Instances

| Name               | Offset   |
|:-------------------|:---------|
| INP_PRD_CNT_CTRL_0 | 0x48     |
| INP_PRD_CNT_CTRL_1 | 0x4c     |
| INP_PRD_CNT_CTRL_2 | 0x50     |
| INP_PRD_CNT_CTRL_3 | 0x54     |
| INP_PRD_CNT_CTRL_4 | 0x58     |
| INP_PRD_CNT_CTRL_5 | 0x5c     |
| INP_PRD_CNT_CTRL_6 | 0x60     |
| INP_PRD_CNT_CTRL_7 | 0x64     |


### Fields

```wavejson
{"reg": [{"name": "enable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "continuous_mode", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "polarity", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 5}, {"name": "input_select", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "prescaler", "bits": 8, "attr": ["rw"], "rotate": 0}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name                                                  |
|:------:|:------:|:-------:|:------------------------------------------------------|
| 31:24  |        |         | Reserved                                              |
| 23:16  |   rw   |   0x0   | [prescaler](#inp_prd_cnt_ctrl--prescaler)             |
|  15:8  |   rw   |   0x0   | [input_select](#inp_prd_cnt_ctrl--input_select)       |
|  7:3   |        |         | Reserved                                              |
|   2    |   rw   |   0x1   | [polarity](#inp_prd_cnt_ctrl--polarity)               |
|   1    |   rw   |   0x0   | [continuous_mode](#inp_prd_cnt_ctrl--continuous_mode) |
|   0    |   rw   |   0x0   | [enable](#inp_prd_cnt_ctrl--enable)                   |

### INP_PRD_CNT_CTRL . prescaler
Prescaler for this input period counter.
The basic idea is that the value returned in [`INP_PRD_CNT_VAL`](#inp_prd_cnt_val) can be multiplied by the value of this register plus one to obtain the number of `clk_i` cycles between two relevant edges.

For example, assume the input pattern `00100100`:
- For `prescaler = 0`, [`INP_PRD_CNT_VAL`](#inp_prd_cnt_val) = 2
- For `prescaler = 1`, [`INP_PRD_CNT_VAL`](#inp_prd_cnt_val) = 1

Note that, regardless of the prescaler, the input is sampled at every positive edge of `clk_i`.
The detection of relevant edges is thus not affected by the prescaler.

This may only be changed while the `enable` field is zero.

### INP_PRD_CNT_CTRL . input_select
Index (starting at 0) of the input that this period counter should operate on.
The value must be smaller than the number of inputs (N), as only the `ceil(log2(N))` least significant bits of this field are considered.

This may only be changed while the `enable` field is zero.

### INP_PRD_CNT_CTRL . polarity
Polarity of this input period counter.
If 0, *falling* edges of the input are relevant.
If 1, *rising* edges of the input are relevant.

This field may only be changed while the `enable` field is zero.

### INP_PRD_CNT_CTRL . continuous_mode
Continuously count the input period.
When one measurement is completed (see description of `enable` field) and this field is set, all of the following apply:
- the wait for a relevant edge will immediately restart, with an internal counter of zero (while [`INP_PRD_CNT_VAL`](#inp_prd_cnt_val) keeps the value of the completed measurement);
- the `enable` field is not cleared.

This field may only be changed while the `enable` field is zero.

### INP_PRD_CNT_CTRL . enable
Enable this input period counter.
After enabling, this counter waits for the next relevant edge (see `polarity` field) of the input to start counting.
After that, it counts clock cycles until the next relevant edge.
On that edge, the measurement is complete and the count is stored in the [`INP_PRD_CNT_VAL`](#inp_prd_cnt_val) register of this input period counter.
Then, if the `continuous_mode` field of this register is not set, the counter clears the `enable` field and returns to idle (see description of the `continuous_mode` field for what happens if that field is set).

## INP_PRD_CNT_VAL
Output value of one input period counter.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name              | Offset   |
|:------------------|:---------|
| INP_PRD_CNT_VAL_0 | 0x68     |
| INP_PRD_CNT_VAL_1 | 0x6c     |
| INP_PRD_CNT_VAL_2 | 0x70     |
| INP_PRD_CNT_VAL_3 | 0x74     |
| INP_PRD_CNT_VAL_4 | 0x78     |
| INP_PRD_CNT_VAL_5 | 0x7c     |
| INP_PRD_CNT_VAL_6 | 0x80     |
| INP_PRD_CNT_VAL_7 | 0x84     |


### Fields

```wavejson
{"reg": [{"name": "value", "bits": 32, "attr": ["rc"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                             |
|:------:|:------:|:-------:|:---------------------------------|
|  31:0  |   rc   |   0x0   | [value](#inp_prd_cnt_val--value) |

### INP_PRD_CNT_VAL . value
Number of clock cycles in one complete period.
If this contains the value 0, no complete period has been measured since the last time this register got cleared.
The minimum number of clock cycles in one complete period is 1, which is returned when the input inverts for one clock cycle and then inverts again.

Expected values for some example patterns:
- `01010101` -> 1
- `00100100` -> 2
- `00010001` -> 3

The counter saturates at the maximum value.

This register gets cleared after every read from SW.

## PER_PIN_IO
Per-pin view of the output and input data of one GPIO.

This register aliases bit i of [`DIRECT_OUT`](#direct_out) and [`DATA_IN`](#data_in) for GPIO[i].
Writing it updates only DATA_OUT[i], without affecting the other GPIOs.
- Reset default: `0x0`
- Reset mask: `0x101`

### Instances

| Name          | Offset   |
|:--------------|:---------|
| PER_PIN_IO_0  | 0x100    |
| PER_PIN_IO_1  | 0x104    |
| PER_PIN_IO_2  | 0x108    |
| PER_PIN_IO_3  | 0x10c    |
| PER_PIN_IO_4  | 0x110    |
| PER_PIN_IO_5  | 0x114    |
| PER_PIN_IO_6  | 0x118    |
| PER_PIN_IO_7  | 0x11c    |
| PER_PIN_IO_8  | 0x120    |
| PER_PIN_IO_9  | 0x124    |
| PER_PIN_IO_10 | 0x128    |
| PER_PIN_IO_11 | 0x12c    |
| PER_PIN_IO_12 | 0x130    |
| PER_PIN_IO_13 | 0x134    |
| PER_PIN_IO_14 | 0x138    |
| PER_PIN_IO_15 | 0x13c    |
| PER_PIN_IO_16 | 0x140    |
| PER_PIN_IO_17 | 0x144    |
| PER_PIN_IO_18 | 0x148    |
| PER_PIN_IO_19 | 0x14c    |
| PER_PIN_IO_20 | 0x150    |
| PER_PIN_IO_21 | 0x154    |
| PER_PIN_IO_22 | 0x158    |
| PER_PIN_IO_23 | 0x15c    |
| PER_PIN_IO_24 | 0x160    |
| PER_PIN_IO_25 | 0x164    |
| PER_PIN_IO_26 | 0x168    |
| PER_PIN_IO_27 | 0x16c    |
| PER_PIN_IO_28 | 0x170    |
| PER_PIN_IO_29 | 0x174    |
| PER_PIN_IO_30 | 0x178    |
| PER_PIN_IO_31 | 0x17c    |


### Fields

```wavejson
{"reg": [{"name": "data_out", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 7}, {"name": "data_in", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 23}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                     |
|:------:|:------:|:-------:|:---------|:----------------------------------------------------------------|
|  31:9  |        |         |          | Reserved                                                        |
|   8    |   ro   |    x    | data_in  | Input data value of GPIO[i], alias of [`DATA_IN`](#data_in)[i]. |
|  7:1   |        |         |          | Reserved                                                        |
|   0    |   rw   |    x    | data_out | Output data value of GPIO[i], alias of DATA_OUT[i].             |

## PER_PIN_CFG
Per-pin view of the configuration of one GPIO.

This register aliases bit i of [`DIRECT_OE`](#direct_oe), [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter) for GPIO[i].
Writing it updates only the configuration of GPIO[i], without affecting the other GPIOs.
It is placed in a separate address range from [`PER_PIN_IO`](#per_pin_io), so access to the data and to the configuration of a GPIO can be controlled independently.
- Reset default: `0x0`
- Reset mask: `0x1f01`

### Instances

| Name           | Offset   |
|:---------------|:---------|
| PER_PIN_CFG_0  | 0x200    |
| PER_PIN_CFG_1  | 0x204    |
| PER_PIN_CFG_2  | 0x208    |
| PER_PIN_CFG_3  | 0x20c    |
| PER_PIN_CFG_4  | 0x210    |
| PER_PIN_CFG_5  | 0x214    |
| PER_PIN_CFG_6  | 0x218    |
| PER_PIN_CFG_7  | 0x21c    |
| PER_PIN_CFG_8  | 0x220    |
| PER_PIN_CFG_9  | 0x224    |
| PER_PIN_CFG_10 | 0x228    |
| PER_PIN_CFG_11 | 0x22c    |
| PER_PIN_CFG_12 | 0x230    |
| PER_PIN_CFG_13 | 0x234    |
| PER_PIN_CFG_14 | 0x238    |
| PER_PIN_CFG_15 | 0x23c    |
| PER_PIN_CFG_16 | 0x240    |
| PER_PIN_CFG_17 | 0x244    |
| PER_PIN_CFG_18 | 0x248    |
| PER_PIN_CFG_19 | 0x24c    |
| PER_PIN_CFG_20 | 0x250    |
| PER_PIN_CFG_21 | 0x254    |
| PER_PIN_CFG_22 | 0x258    |
| PER_PIN_CFG_23 | 0x25c    |
| PER_PIN_CFG_24 | 0x260    |
| PER_PIN_CFG_25 | 0x264    |
| PER_PIN_CFG_26 | 0x268    |
| PER_PIN_CFG_27 | 0x26c    |
| PER_PIN_CFG_28 | 0x270    |
| PER_PIN_CFG_29 | 0x274    |
| PER_PIN_CFG_30 | 0x278    |
| PER_PIN_CFG_31 | 0x27c    |


### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 7}, {"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 19}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                            |
|:------:|:------:|:-------:|:---------------------|:-------------------------------------------------------------------------------------------------------|
| 31:13  |        |         |                      | Reserved                                                                                               |
|   12   |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[i], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[i].           |
|   11   |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[i], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[i].      |
|   10   |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[i], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[i].   |
|   9    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[i], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[i]. |
|   8    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[i], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[i].    |
|  7:1   |        |         |                      | Reserved                                                                                               |
|   0    |   rw   |    x    | oe                   | Output enable of GPIO[i], alias of DATA_OE[i].                                                         |


<!-- END CMDGEN -->
