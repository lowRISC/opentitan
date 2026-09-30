# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/top_earlgrey/ip_autogen/gpio/data/gpio.hjson -->
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
| gpio.[`PER_PIN_OE_0`](#per_pin_oe_0)                       | 0x200    |        4 | Per-pin view of the output enable of GPIO[0].                                     |
| gpio.[`PER_PIN_INTR_CTRL_0`](#per_pin_intr_ctrl_0)         | 0x204    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[0].  |
| gpio.[`PER_PIN_OE_1`](#per_pin_oe_1)                       | 0x208    |        4 | Per-pin view of the output enable of GPIO[1].                                     |
| gpio.[`PER_PIN_INTR_CTRL_1`](#per_pin_intr_ctrl_1)         | 0x20c    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[1].  |
| gpio.[`PER_PIN_OE_2`](#per_pin_oe_2)                       | 0x210    |        4 | Per-pin view of the output enable of GPIO[2].                                     |
| gpio.[`PER_PIN_INTR_CTRL_2`](#per_pin_intr_ctrl_2)         | 0x214    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[2].  |
| gpio.[`PER_PIN_OE_3`](#per_pin_oe_3)                       | 0x218    |        4 | Per-pin view of the output enable of GPIO[3].                                     |
| gpio.[`PER_PIN_INTR_CTRL_3`](#per_pin_intr_ctrl_3)         | 0x21c    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[3].  |
| gpio.[`PER_PIN_OE_4`](#per_pin_oe_4)                       | 0x220    |        4 | Per-pin view of the output enable of GPIO[4].                                     |
| gpio.[`PER_PIN_INTR_CTRL_4`](#per_pin_intr_ctrl_4)         | 0x224    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[4].  |
| gpio.[`PER_PIN_OE_5`](#per_pin_oe_5)                       | 0x228    |        4 | Per-pin view of the output enable of GPIO[5].                                     |
| gpio.[`PER_PIN_INTR_CTRL_5`](#per_pin_intr_ctrl_5)         | 0x22c    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[5].  |
| gpio.[`PER_PIN_OE_6`](#per_pin_oe_6)                       | 0x230    |        4 | Per-pin view of the output enable of GPIO[6].                                     |
| gpio.[`PER_PIN_INTR_CTRL_6`](#per_pin_intr_ctrl_6)         | 0x234    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[6].  |
| gpio.[`PER_PIN_OE_7`](#per_pin_oe_7)                       | 0x238    |        4 | Per-pin view of the output enable of GPIO[7].                                     |
| gpio.[`PER_PIN_INTR_CTRL_7`](#per_pin_intr_ctrl_7)         | 0x23c    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[7].  |
| gpio.[`PER_PIN_OE_8`](#per_pin_oe_8)                       | 0x240    |        4 | Per-pin view of the output enable of GPIO[8].                                     |
| gpio.[`PER_PIN_INTR_CTRL_8`](#per_pin_intr_ctrl_8)         | 0x244    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[8].  |
| gpio.[`PER_PIN_OE_9`](#per_pin_oe_9)                       | 0x248    |        4 | Per-pin view of the output enable of GPIO[9].                                     |
| gpio.[`PER_PIN_INTR_CTRL_9`](#per_pin_intr_ctrl_9)         | 0x24c    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[9].  |
| gpio.[`PER_PIN_OE_10`](#per_pin_oe_10)                     | 0x250    |        4 | Per-pin view of the output enable of GPIO[10].                                    |
| gpio.[`PER_PIN_INTR_CTRL_10`](#per_pin_intr_ctrl_10)       | 0x254    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[10]. |
| gpio.[`PER_PIN_OE_11`](#per_pin_oe_11)                     | 0x258    |        4 | Per-pin view of the output enable of GPIO[11].                                    |
| gpio.[`PER_PIN_INTR_CTRL_11`](#per_pin_intr_ctrl_11)       | 0x25c    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[11]. |
| gpio.[`PER_PIN_OE_12`](#per_pin_oe_12)                     | 0x260    |        4 | Per-pin view of the output enable of GPIO[12].                                    |
| gpio.[`PER_PIN_INTR_CTRL_12`](#per_pin_intr_ctrl_12)       | 0x264    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[12]. |
| gpio.[`PER_PIN_OE_13`](#per_pin_oe_13)                     | 0x268    |        4 | Per-pin view of the output enable of GPIO[13].                                    |
| gpio.[`PER_PIN_INTR_CTRL_13`](#per_pin_intr_ctrl_13)       | 0x26c    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[13]. |
| gpio.[`PER_PIN_OE_14`](#per_pin_oe_14)                     | 0x270    |        4 | Per-pin view of the output enable of GPIO[14].                                    |
| gpio.[`PER_PIN_INTR_CTRL_14`](#per_pin_intr_ctrl_14)       | 0x274    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[14]. |
| gpio.[`PER_PIN_OE_15`](#per_pin_oe_15)                     | 0x278    |        4 | Per-pin view of the output enable of GPIO[15].                                    |
| gpio.[`PER_PIN_INTR_CTRL_15`](#per_pin_intr_ctrl_15)       | 0x27c    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[15]. |
| gpio.[`PER_PIN_OE_16`](#per_pin_oe_16)                     | 0x280    |        4 | Per-pin view of the output enable of GPIO[16].                                    |
| gpio.[`PER_PIN_INTR_CTRL_16`](#per_pin_intr_ctrl_16)       | 0x284    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[16]. |
| gpio.[`PER_PIN_OE_17`](#per_pin_oe_17)                     | 0x288    |        4 | Per-pin view of the output enable of GPIO[17].                                    |
| gpio.[`PER_PIN_INTR_CTRL_17`](#per_pin_intr_ctrl_17)       | 0x28c    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[17]. |
| gpio.[`PER_PIN_OE_18`](#per_pin_oe_18)                     | 0x290    |        4 | Per-pin view of the output enable of GPIO[18].                                    |
| gpio.[`PER_PIN_INTR_CTRL_18`](#per_pin_intr_ctrl_18)       | 0x294    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[18]. |
| gpio.[`PER_PIN_OE_19`](#per_pin_oe_19)                     | 0x298    |        4 | Per-pin view of the output enable of GPIO[19].                                    |
| gpio.[`PER_PIN_INTR_CTRL_19`](#per_pin_intr_ctrl_19)       | 0x29c    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[19]. |
| gpio.[`PER_PIN_OE_20`](#per_pin_oe_20)                     | 0x2a0    |        4 | Per-pin view of the output enable of GPIO[20].                                    |
| gpio.[`PER_PIN_INTR_CTRL_20`](#per_pin_intr_ctrl_20)       | 0x2a4    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[20]. |
| gpio.[`PER_PIN_OE_21`](#per_pin_oe_21)                     | 0x2a8    |        4 | Per-pin view of the output enable of GPIO[21].                                    |
| gpio.[`PER_PIN_INTR_CTRL_21`](#per_pin_intr_ctrl_21)       | 0x2ac    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[21]. |
| gpio.[`PER_PIN_OE_22`](#per_pin_oe_22)                     | 0x2b0    |        4 | Per-pin view of the output enable of GPIO[22].                                    |
| gpio.[`PER_PIN_INTR_CTRL_22`](#per_pin_intr_ctrl_22)       | 0x2b4    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[22]. |
| gpio.[`PER_PIN_OE_23`](#per_pin_oe_23)                     | 0x2b8    |        4 | Per-pin view of the output enable of GPIO[23].                                    |
| gpio.[`PER_PIN_INTR_CTRL_23`](#per_pin_intr_ctrl_23)       | 0x2bc    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[23]. |
| gpio.[`PER_PIN_OE_24`](#per_pin_oe_24)                     | 0x2c0    |        4 | Per-pin view of the output enable of GPIO[24].                                    |
| gpio.[`PER_PIN_INTR_CTRL_24`](#per_pin_intr_ctrl_24)       | 0x2c4    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[24]. |
| gpio.[`PER_PIN_OE_25`](#per_pin_oe_25)                     | 0x2c8    |        4 | Per-pin view of the output enable of GPIO[25].                                    |
| gpio.[`PER_PIN_INTR_CTRL_25`](#per_pin_intr_ctrl_25)       | 0x2cc    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[25]. |
| gpio.[`PER_PIN_OE_26`](#per_pin_oe_26)                     | 0x2d0    |        4 | Per-pin view of the output enable of GPIO[26].                                    |
| gpio.[`PER_PIN_INTR_CTRL_26`](#per_pin_intr_ctrl_26)       | 0x2d4    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[26]. |
| gpio.[`PER_PIN_OE_27`](#per_pin_oe_27)                     | 0x2d8    |        4 | Per-pin view of the output enable of GPIO[27].                                    |
| gpio.[`PER_PIN_INTR_CTRL_27`](#per_pin_intr_ctrl_27)       | 0x2dc    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[27]. |
| gpio.[`PER_PIN_OE_28`](#per_pin_oe_28)                     | 0x2e0    |        4 | Per-pin view of the output enable of GPIO[28].                                    |
| gpio.[`PER_PIN_INTR_CTRL_28`](#per_pin_intr_ctrl_28)       | 0x2e4    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[28]. |
| gpio.[`PER_PIN_OE_29`](#per_pin_oe_29)                     | 0x2e8    |        4 | Per-pin view of the output enable of GPIO[29].                                    |
| gpio.[`PER_PIN_INTR_CTRL_29`](#per_pin_intr_ctrl_29)       | 0x2ec    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[29]. |
| gpio.[`PER_PIN_OE_30`](#per_pin_oe_30)                     | 0x2f0    |        4 | Per-pin view of the output enable of GPIO[30].                                    |
| gpio.[`PER_PIN_INTR_CTRL_30`](#per_pin_intr_ctrl_30)       | 0x2f4    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[30]. |
| gpio.[`PER_PIN_OE_31`](#per_pin_oe_31)                     | 0x2f8    |        4 | Per-pin view of the output enable of GPIO[31].                                    |
| gpio.[`PER_PIN_INTR_CTRL_31`](#per_pin_intr_ctrl_31)       | 0x2fc    |        4 | Per-pin view of the interrupt control and input filter configuration of GPIO[31]. |

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
- Reset default: `0x80000000`
- Reset mask: `0x80000001`

### Fields

```wavejson
{"reg": [{"name": "fatal_fault", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}, {"name": "regwen", "bits": 1, "attr": ["rw0c"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                            |
|:------:|:------:|:-------:|:------------|:-------------------------------------------------------|
|   31   |  rw0c  |   0x1   | regwen      | Write 0 to disable alert testing until the next reset. |
|  30:1  |        |         |             | Reserved                                               |
|   0    |   wo   |   0x0   | fatal_fault | Write 1 to trigger one alert event of this kind.       |

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

## PER_PIN_OE_0
Per-pin view of the output enable of GPIO[0].

This register aliases bit 0 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[0], without affecting the other GPIOs.
- Offset: `0x200`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                    |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------|
|  31:1  |        |         |        | Reserved                                       |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[0], alias of DATA_OE[0]. |

## PER_PIN_INTR_CTRL_0
Per-pin view of the interrupt control and input filter configuration of GPIO[0].

This register aliases bit 0 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[0], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_0`](#per_pin_oe_0), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x204`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                            |
|:------:|:------:|:-------:|:---------------------|:-------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                               |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[0], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[0].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[0], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[0].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[0], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[0].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[0], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[0]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[0], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[0].    |

## PER_PIN_OE_1
Per-pin view of the output enable of GPIO[1].

This register aliases bit 1 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[1], without affecting the other GPIOs.
- Offset: `0x208`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                    |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------|
|  31:1  |        |         |        | Reserved                                       |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[1], alias of DATA_OE[1]. |

## PER_PIN_INTR_CTRL_1
Per-pin view of the interrupt control and input filter configuration of GPIO[1].

This register aliases bit 1 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[1], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_1`](#per_pin_oe_1), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x20c`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                            |
|:------:|:------:|:-------:|:---------------------|:-------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                               |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[1], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[1].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[1], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[1].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[1], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[1].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[1], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[1]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[1], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[1].    |

## PER_PIN_OE_2
Per-pin view of the output enable of GPIO[2].

This register aliases bit 2 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[2], without affecting the other GPIOs.
- Offset: `0x210`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                    |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------|
|  31:1  |        |         |        | Reserved                                       |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[2], alias of DATA_OE[2]. |

## PER_PIN_INTR_CTRL_2
Per-pin view of the interrupt control and input filter configuration of GPIO[2].

This register aliases bit 2 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[2], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_2`](#per_pin_oe_2), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x214`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                            |
|:------:|:------:|:-------:|:---------------------|:-------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                               |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[2], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[2].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[2], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[2].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[2], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[2].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[2], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[2]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[2], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[2].    |

## PER_PIN_OE_3
Per-pin view of the output enable of GPIO[3].

This register aliases bit 3 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[3], without affecting the other GPIOs.
- Offset: `0x218`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                    |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------|
|  31:1  |        |         |        | Reserved                                       |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[3], alias of DATA_OE[3]. |

## PER_PIN_INTR_CTRL_3
Per-pin view of the interrupt control and input filter configuration of GPIO[3].

This register aliases bit 3 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[3], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_3`](#per_pin_oe_3), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x21c`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                            |
|:------:|:------:|:-------:|:---------------------|:-------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                               |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[3], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[3].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[3], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[3].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[3], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[3].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[3], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[3]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[3], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[3].    |

## PER_PIN_OE_4
Per-pin view of the output enable of GPIO[4].

This register aliases bit 4 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[4], without affecting the other GPIOs.
- Offset: `0x220`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                    |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------|
|  31:1  |        |         |        | Reserved                                       |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[4], alias of DATA_OE[4]. |

## PER_PIN_INTR_CTRL_4
Per-pin view of the interrupt control and input filter configuration of GPIO[4].

This register aliases bit 4 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[4], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_4`](#per_pin_oe_4), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x224`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                            |
|:------:|:------:|:-------:|:---------------------|:-------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                               |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[4], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[4].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[4], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[4].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[4], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[4].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[4], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[4]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[4], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[4].    |

## PER_PIN_OE_5
Per-pin view of the output enable of GPIO[5].

This register aliases bit 5 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[5], without affecting the other GPIOs.
- Offset: `0x228`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                    |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------|
|  31:1  |        |         |        | Reserved                                       |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[5], alias of DATA_OE[5]. |

## PER_PIN_INTR_CTRL_5
Per-pin view of the interrupt control and input filter configuration of GPIO[5].

This register aliases bit 5 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[5], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_5`](#per_pin_oe_5), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x22c`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                            |
|:------:|:------:|:-------:|:---------------------|:-------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                               |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[5], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[5].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[5], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[5].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[5], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[5].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[5], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[5]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[5], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[5].    |

## PER_PIN_OE_6
Per-pin view of the output enable of GPIO[6].

This register aliases bit 6 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[6], without affecting the other GPIOs.
- Offset: `0x230`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                    |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------|
|  31:1  |        |         |        | Reserved                                       |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[6], alias of DATA_OE[6]. |

## PER_PIN_INTR_CTRL_6
Per-pin view of the interrupt control and input filter configuration of GPIO[6].

This register aliases bit 6 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[6], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_6`](#per_pin_oe_6), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x234`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                            |
|:------:|:------:|:-------:|:---------------------|:-------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                               |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[6], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[6].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[6], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[6].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[6], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[6].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[6], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[6]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[6], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[6].    |

## PER_PIN_OE_7
Per-pin view of the output enable of GPIO[7].

This register aliases bit 7 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[7], without affecting the other GPIOs.
- Offset: `0x238`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                    |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------|
|  31:1  |        |         |        | Reserved                                       |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[7], alias of DATA_OE[7]. |

## PER_PIN_INTR_CTRL_7
Per-pin view of the interrupt control and input filter configuration of GPIO[7].

This register aliases bit 7 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[7], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_7`](#per_pin_oe_7), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x23c`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                            |
|:------:|:------:|:-------:|:---------------------|:-------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                               |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[7], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[7].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[7], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[7].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[7], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[7].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[7], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[7]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[7], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[7].    |

## PER_PIN_OE_8
Per-pin view of the output enable of GPIO[8].

This register aliases bit 8 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[8], without affecting the other GPIOs.
- Offset: `0x240`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                    |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------|
|  31:1  |        |         |        | Reserved                                       |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[8], alias of DATA_OE[8]. |

## PER_PIN_INTR_CTRL_8
Per-pin view of the interrupt control and input filter configuration of GPIO[8].

This register aliases bit 8 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[8], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_8`](#per_pin_oe_8), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x244`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                            |
|:------:|:------:|:-------:|:---------------------|:-------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                               |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[8], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[8].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[8], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[8].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[8], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[8].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[8], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[8]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[8], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[8].    |

## PER_PIN_OE_9
Per-pin view of the output enable of GPIO[9].

This register aliases bit 9 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[9], without affecting the other GPIOs.
- Offset: `0x248`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                    |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------|
|  31:1  |        |         |        | Reserved                                       |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[9], alias of DATA_OE[9]. |

## PER_PIN_INTR_CTRL_9
Per-pin view of the interrupt control and input filter configuration of GPIO[9].

This register aliases bit 9 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[9], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_9`](#per_pin_oe_9), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x24c`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                            |
|:------:|:------:|:-------:|:---------------------|:-------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                               |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[9], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[9].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[9], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[9].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[9], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[9].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[9], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[9]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[9], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[9].    |

## PER_PIN_OE_10
Per-pin view of the output enable of GPIO[10].

This register aliases bit 10 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[10], without affecting the other GPIOs.
- Offset: `0x250`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[10], alias of DATA_OE[10]. |

## PER_PIN_INTR_CTRL_10
Per-pin view of the interrupt control and input filter configuration of GPIO[10].

This register aliases bit 10 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[10], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_10`](#per_pin_oe_10), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x254`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[10], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[10].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[10], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[10].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[10], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[10].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[10], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[10]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[10], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[10].    |

## PER_PIN_OE_11
Per-pin view of the output enable of GPIO[11].

This register aliases bit 11 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[11], without affecting the other GPIOs.
- Offset: `0x258`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[11], alias of DATA_OE[11]. |

## PER_PIN_INTR_CTRL_11
Per-pin view of the interrupt control and input filter configuration of GPIO[11].

This register aliases bit 11 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[11], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_11`](#per_pin_oe_11), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x25c`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[11], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[11].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[11], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[11].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[11], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[11].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[11], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[11]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[11], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[11].    |

## PER_PIN_OE_12
Per-pin view of the output enable of GPIO[12].

This register aliases bit 12 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[12], without affecting the other GPIOs.
- Offset: `0x260`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[12], alias of DATA_OE[12]. |

## PER_PIN_INTR_CTRL_12
Per-pin view of the interrupt control and input filter configuration of GPIO[12].

This register aliases bit 12 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[12], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_12`](#per_pin_oe_12), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x264`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[12], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[12].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[12], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[12].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[12], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[12].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[12], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[12]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[12], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[12].    |

## PER_PIN_OE_13
Per-pin view of the output enable of GPIO[13].

This register aliases bit 13 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[13], without affecting the other GPIOs.
- Offset: `0x268`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[13], alias of DATA_OE[13]. |

## PER_PIN_INTR_CTRL_13
Per-pin view of the interrupt control and input filter configuration of GPIO[13].

This register aliases bit 13 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[13], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_13`](#per_pin_oe_13), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x26c`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[13], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[13].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[13], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[13].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[13], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[13].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[13], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[13]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[13], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[13].    |

## PER_PIN_OE_14
Per-pin view of the output enable of GPIO[14].

This register aliases bit 14 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[14], without affecting the other GPIOs.
- Offset: `0x270`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[14], alias of DATA_OE[14]. |

## PER_PIN_INTR_CTRL_14
Per-pin view of the interrupt control and input filter configuration of GPIO[14].

This register aliases bit 14 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[14], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_14`](#per_pin_oe_14), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x274`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[14], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[14].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[14], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[14].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[14], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[14].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[14], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[14]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[14], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[14].    |

## PER_PIN_OE_15
Per-pin view of the output enable of GPIO[15].

This register aliases bit 15 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[15], without affecting the other GPIOs.
- Offset: `0x278`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[15], alias of DATA_OE[15]. |

## PER_PIN_INTR_CTRL_15
Per-pin view of the interrupt control and input filter configuration of GPIO[15].

This register aliases bit 15 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[15], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_15`](#per_pin_oe_15), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x27c`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[15], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[15].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[15], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[15].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[15], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[15].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[15], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[15]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[15], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[15].    |

## PER_PIN_OE_16
Per-pin view of the output enable of GPIO[16].

This register aliases bit 16 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[16], without affecting the other GPIOs.
- Offset: `0x280`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[16], alias of DATA_OE[16]. |

## PER_PIN_INTR_CTRL_16
Per-pin view of the interrupt control and input filter configuration of GPIO[16].

This register aliases bit 16 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[16], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_16`](#per_pin_oe_16), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x284`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[16], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[16].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[16], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[16].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[16], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[16].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[16], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[16]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[16], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[16].    |

## PER_PIN_OE_17
Per-pin view of the output enable of GPIO[17].

This register aliases bit 17 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[17], without affecting the other GPIOs.
- Offset: `0x288`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[17], alias of DATA_OE[17]. |

## PER_PIN_INTR_CTRL_17
Per-pin view of the interrupt control and input filter configuration of GPIO[17].

This register aliases bit 17 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[17], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_17`](#per_pin_oe_17), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x28c`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[17], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[17].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[17], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[17].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[17], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[17].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[17], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[17]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[17], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[17].    |

## PER_PIN_OE_18
Per-pin view of the output enable of GPIO[18].

This register aliases bit 18 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[18], without affecting the other GPIOs.
- Offset: `0x290`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[18], alias of DATA_OE[18]. |

## PER_PIN_INTR_CTRL_18
Per-pin view of the interrupt control and input filter configuration of GPIO[18].

This register aliases bit 18 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[18], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_18`](#per_pin_oe_18), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x294`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[18], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[18].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[18], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[18].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[18], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[18].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[18], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[18]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[18], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[18].    |

## PER_PIN_OE_19
Per-pin view of the output enable of GPIO[19].

This register aliases bit 19 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[19], without affecting the other GPIOs.
- Offset: `0x298`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[19], alias of DATA_OE[19]. |

## PER_PIN_INTR_CTRL_19
Per-pin view of the interrupt control and input filter configuration of GPIO[19].

This register aliases bit 19 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[19], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_19`](#per_pin_oe_19), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x29c`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[19], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[19].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[19], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[19].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[19], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[19].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[19], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[19]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[19], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[19].    |

## PER_PIN_OE_20
Per-pin view of the output enable of GPIO[20].

This register aliases bit 20 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[20], without affecting the other GPIOs.
- Offset: `0x2a0`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[20], alias of DATA_OE[20]. |

## PER_PIN_INTR_CTRL_20
Per-pin view of the interrupt control and input filter configuration of GPIO[20].

This register aliases bit 20 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[20], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_20`](#per_pin_oe_20), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x2a4`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[20], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[20].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[20], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[20].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[20], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[20].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[20], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[20]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[20], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[20].    |

## PER_PIN_OE_21
Per-pin view of the output enable of GPIO[21].

This register aliases bit 21 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[21], without affecting the other GPIOs.
- Offset: `0x2a8`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[21], alias of DATA_OE[21]. |

## PER_PIN_INTR_CTRL_21
Per-pin view of the interrupt control and input filter configuration of GPIO[21].

This register aliases bit 21 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[21], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_21`](#per_pin_oe_21), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x2ac`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[21], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[21].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[21], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[21].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[21], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[21].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[21], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[21]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[21], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[21].    |

## PER_PIN_OE_22
Per-pin view of the output enable of GPIO[22].

This register aliases bit 22 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[22], without affecting the other GPIOs.
- Offset: `0x2b0`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[22], alias of DATA_OE[22]. |

## PER_PIN_INTR_CTRL_22
Per-pin view of the interrupt control and input filter configuration of GPIO[22].

This register aliases bit 22 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[22], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_22`](#per_pin_oe_22), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x2b4`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[22], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[22].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[22], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[22].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[22], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[22].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[22], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[22]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[22], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[22].    |

## PER_PIN_OE_23
Per-pin view of the output enable of GPIO[23].

This register aliases bit 23 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[23], without affecting the other GPIOs.
- Offset: `0x2b8`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[23], alias of DATA_OE[23]. |

## PER_PIN_INTR_CTRL_23
Per-pin view of the interrupt control and input filter configuration of GPIO[23].

This register aliases bit 23 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[23], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_23`](#per_pin_oe_23), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x2bc`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[23], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[23].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[23], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[23].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[23], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[23].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[23], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[23]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[23], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[23].    |

## PER_PIN_OE_24
Per-pin view of the output enable of GPIO[24].

This register aliases bit 24 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[24], without affecting the other GPIOs.
- Offset: `0x2c0`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[24], alias of DATA_OE[24]. |

## PER_PIN_INTR_CTRL_24
Per-pin view of the interrupt control and input filter configuration of GPIO[24].

This register aliases bit 24 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[24], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_24`](#per_pin_oe_24), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x2c4`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[24], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[24].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[24], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[24].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[24], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[24].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[24], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[24]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[24], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[24].    |

## PER_PIN_OE_25
Per-pin view of the output enable of GPIO[25].

This register aliases bit 25 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[25], without affecting the other GPIOs.
- Offset: `0x2c8`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[25], alias of DATA_OE[25]. |

## PER_PIN_INTR_CTRL_25
Per-pin view of the interrupt control and input filter configuration of GPIO[25].

This register aliases bit 25 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[25], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_25`](#per_pin_oe_25), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x2cc`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[25], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[25].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[25], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[25].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[25], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[25].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[25], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[25]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[25], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[25].    |

## PER_PIN_OE_26
Per-pin view of the output enable of GPIO[26].

This register aliases bit 26 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[26], without affecting the other GPIOs.
- Offset: `0x2d0`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[26], alias of DATA_OE[26]. |

## PER_PIN_INTR_CTRL_26
Per-pin view of the interrupt control and input filter configuration of GPIO[26].

This register aliases bit 26 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[26], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_26`](#per_pin_oe_26), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x2d4`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[26], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[26].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[26], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[26].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[26], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[26].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[26], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[26]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[26], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[26].    |

## PER_PIN_OE_27
Per-pin view of the output enable of GPIO[27].

This register aliases bit 27 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[27], without affecting the other GPIOs.
- Offset: `0x2d8`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[27], alias of DATA_OE[27]. |

## PER_PIN_INTR_CTRL_27
Per-pin view of the interrupt control and input filter configuration of GPIO[27].

This register aliases bit 27 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[27], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_27`](#per_pin_oe_27), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x2dc`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[27], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[27].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[27], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[27].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[27], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[27].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[27], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[27]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[27], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[27].    |

## PER_PIN_OE_28
Per-pin view of the output enable of GPIO[28].

This register aliases bit 28 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[28], without affecting the other GPIOs.
- Offset: `0x2e0`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[28], alias of DATA_OE[28]. |

## PER_PIN_INTR_CTRL_28
Per-pin view of the interrupt control and input filter configuration of GPIO[28].

This register aliases bit 28 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[28], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_28`](#per_pin_oe_28), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x2e4`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[28], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[28].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[28], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[28].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[28], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[28].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[28], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[28]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[28], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[28].    |

## PER_PIN_OE_29
Per-pin view of the output enable of GPIO[29].

This register aliases bit 29 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[29], without affecting the other GPIOs.
- Offset: `0x2e8`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[29], alias of DATA_OE[29]. |

## PER_PIN_INTR_CTRL_29
Per-pin view of the interrupt control and input filter configuration of GPIO[29].

This register aliases bit 29 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[29], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_29`](#per_pin_oe_29), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x2ec`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[29], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[29].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[29], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[29].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[29], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[29].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[29], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[29]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[29], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[29].    |

## PER_PIN_OE_30
Per-pin view of the output enable of GPIO[30].

This register aliases bit 30 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[30], without affecting the other GPIOs.
- Offset: `0x2f0`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[30], alias of DATA_OE[30]. |

## PER_PIN_INTR_CTRL_30
Per-pin view of the interrupt control and input filter configuration of GPIO[30].

This register aliases bit 30 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[30], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_30`](#per_pin_oe_30), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x2f4`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[30], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[30].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[30], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[30].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[30], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[30].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[30], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[30]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[30], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[30].    |

## PER_PIN_OE_31
Per-pin view of the output enable of GPIO[31].

This register aliases bit 31 of [`DIRECT_OE.`](#direct_oe)
Writing it updates only DATA_OE[31], without affecting the other GPIOs.
- Offset: `0x2f8`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "oe", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   rw   |    x    | oe     | Output enable of GPIO[31], alias of DATA_OE[31]. |

## PER_PIN_INTR_CTRL_31
Per-pin view of the interrupt control and input filter configuration of GPIO[31].

This register aliases bit 31 of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising), [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling), [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh), [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow) and [`CTRL_EN_INPUT_FILTER.`](#ctrl_en_input_filter)
Writing it updates only the configuration of GPIO[31], without affecting the other GPIOs.
It is separate from [`PER_PIN_OE_31`](#per_pin_oe_31), so access to the output enable and to the interrupt configuration of a GPIO can be controlled independently.
- Offset: `0x2fc`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "intr_ctrl_en_rising", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_falling", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvlhigh", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "intr_ctrl_en_lvllow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ctrl_en_input_filter", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                              |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                 |
|   4    |   rw   |    x    | ctrl_en_input_filter | Input filter enable of GPIO[31], alias of [`CTRL_EN_INPUT_FILTER`](#ctrl_en_input_filter)[31].           |
|   3    |   rw   |    x    | intr_ctrl_en_lvllow  | Level-low interrupt enable of GPIO[31], alias of [`INTR_CTRL_EN_LVLLOW`](#intr_ctrl_en_lvllow)[31].      |
|   2    |   rw   |    x    | intr_ctrl_en_lvlhigh | Level-high interrupt enable of GPIO[31], alias of [`INTR_CTRL_EN_LVLHIGH`](#intr_ctrl_en_lvlhigh)[31].   |
|   1    |   rw   |    x    | intr_ctrl_en_falling | Falling-edge interrupt enable of GPIO[31], alias of [`INTR_CTRL_EN_FALLING`](#intr_ctrl_en_falling)[31]. |
|   0    |   rw   |    x    | intr_ctrl_en_rising  | Rising-edge interrupt enable of GPIO[31], alias of [`INTR_CTRL_EN_RISING`](#intr_ctrl_en_rising)[31].    |


<!-- END CMDGEN -->
