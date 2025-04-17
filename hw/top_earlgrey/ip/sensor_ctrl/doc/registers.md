# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/top_earlgrey/ip/sensor_ctrl/data/sensor_ctrl.hjson -->
## Summary

| Name                                                              | Offset   |   Length | Description                                                             |
|:------------------------------------------------------------------|:---------|---------:|:------------------------------------------------------------------------|
| sensor_ctrl.[`INTR_STATE`](#intr_state)                           | 0x0      |        4 | Interrupt State Register                                                |
| sensor_ctrl.[`INTR_ENABLE`](#intr_enable)                         | 0x4      |        4 | Interrupt Enable Register                                               |
| sensor_ctrl.[`INTR_TEST`](#intr_test)                             | 0x8      |        4 | Interrupt Test Register                                                 |
| sensor_ctrl.[`ALERT_TEST`](#alert_test)                           | 0xc      |        4 | Alert Test Register                                                     |
| sensor_ctrl.[`CFG_REGWEN`](#cfg_regwen)                           | 0x10     |        4 | Controls the configurability of !!FATAL_ALERT_EN register.              |
| sensor_ctrl.[`ALERT_TRIG`](#alert_trig)                           | 0x14     |        4 | Alert trigger test                                                      |
| sensor_ctrl.[`ALERT_EN_0`](#alert_en)                             | 0x18     |        4 | Each multibit value enables a corresponding alert.                      |
| sensor_ctrl.[`ALERT_EN_1`](#alert_en)                             | 0x1c     |        4 | Each multibit value enables a corresponding alert.                      |
| sensor_ctrl.[`ALERT_EN_2`](#alert_en)                             | 0x20     |        4 | Each multibit value enables a corresponding alert.                      |
| sensor_ctrl.[`ALERT_EN_3`](#alert_en)                             | 0x24     |        4 | Each multibit value enables a corresponding alert.                      |
| sensor_ctrl.[`ALERT_EN_4`](#alert_en)                             | 0x28     |        4 | Each multibit value enables a corresponding alert.                      |
| sensor_ctrl.[`ALERT_EN_5`](#alert_en)                             | 0x2c     |        4 | Each multibit value enables a corresponding alert.                      |
| sensor_ctrl.[`ALERT_EN_6`](#alert_en)                             | 0x30     |        4 | Each multibit value enables a corresponding alert.                      |
| sensor_ctrl.[`ALERT_EN_7`](#alert_en)                             | 0x34     |        4 | Each multibit value enables a corresponding alert.                      |
| sensor_ctrl.[`ALERT_EN_8`](#alert_en)                             | 0x38     |        4 | Each multibit value enables a corresponding alert.                      |
| sensor_ctrl.[`ALERT_EN_9`](#alert_en)                             | 0x3c     |        4 | Each multibit value enables a corresponding alert.                      |
| sensor_ctrl.[`ALERT_EN_10`](#alert_en)                            | 0x40     |        4 | Each multibit value enables a corresponding alert.                      |
| sensor_ctrl.[`FATAL_ALERT_EN`](#fatal_alert_en)                   | 0x44     |        4 | Each bit marks a corresponding alert as fatal or recoverable.           |
| sensor_ctrl.[`RECOV_ALERT`](#recov_alert)                         | 0x48     |        4 | Each bit represents a recoverable alert that has been triggered by AST. |
| sensor_ctrl.[`FATAL_ALERT`](#fatal_alert)                         | 0x4c     |        4 | Each bit represents a fatal alert that has been triggered by AST.       |
| sensor_ctrl.[`STATUS`](#status)                                   | 0x50     |        4 | Status readback for ast                                                 |
| sensor_ctrl.[`MANUAL_PAD_ATTR_REGWEN_0`](#manual_pad_attr_regwen) | 0x54     |        4 | Register write enable for attributes of manual pads                     |
| sensor_ctrl.[`MANUAL_PAD_ATTR_REGWEN_1`](#manual_pad_attr_regwen) | 0x58     |        4 | Register write enable for attributes of manual pads                     |
| sensor_ctrl.[`MANUAL_PAD_ATTR_REGWEN_2`](#manual_pad_attr_regwen) | 0x5c     |        4 | Register write enable for attributes of manual pads                     |
| sensor_ctrl.[`MANUAL_PAD_ATTR_REGWEN_3`](#manual_pad_attr_regwen) | 0x60     |        4 | Register write enable for attributes of manual pads                     |
| sensor_ctrl.[`MANUAL_PAD_ATTR_0`](#manual_pad_attr)               | 0x64     |        4 | Attributes of manual pads.                                              |
| sensor_ctrl.[`MANUAL_PAD_ATTR_1`](#manual_pad_attr)               | 0x68     |        4 | Attributes of manual pads.                                              |
| sensor_ctrl.[`MANUAL_PAD_ATTR_2`](#manual_pad_attr)               | 0x6c     |        4 | Attributes of manual pads.                                              |
| sensor_ctrl.[`MANUAL_PAD_ATTR_3`](#manual_pad_attr)               | 0x70     |        4 | Attributes of manual pads.                                              |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "io_status_change", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "init_status_change", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                 |
|:------:|:------:|:-------:|:-------------------|:----------------------------|
|  31:2  |        |         |                    | Reserved                    |
|   1    |  rw1c  |   0x0   | init_status_change | ast init status has changed |
|   0    |  rw1c  |   0x0   | io_status_change   | io power status has changed |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "io_status_change", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "init_status_change", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                                                  |
|:------:|:------:|:-------:|:-------------------|:-----------------------------------------------------------------------------|
|  31:2  |        |         |                    | Reserved                                                                     |
|   1    |   rw   |   0x0   | init_status_change | Enable interrupt when [`INTR_STATE.init_status_change`](#intr_state) is set. |
|   0    |   rw   |   0x0   | io_status_change   | Enable interrupt when [`INTR_STATE.io_status_change`](#intr_state) is set.   |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "io_status_change", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "init_status_change", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                                           |
|:------:|:------:|:-------:|:-------------------|:----------------------------------------------------------------------|
|  31:2  |        |         |                    | Reserved                                                              |
|   1    |   wo   |   0x0   | init_status_change | Write 1 to force [`INTR_STATE.init_status_change`](#intr_state) to 1. |
|   0    |   wo   |   0x0   | io_status_change   | Write 1 to force [`INTR_STATE.io_status_change`](#intr_state) to 1.   |

## ALERT_TEST
Alert Test Register
- Offset: `0xc`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "recov_alert", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_alert", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                      |
|:------:|:------:|:-------:|:------------|:-------------------------------------------------|
|  31:2  |        |         |             | Reserved                                         |
|   1    |   wo   |   0x0   | fatal_alert | Write 1 to trigger one alert event of this kind. |
|   0    |   wo   |   0x0   | recov_alert | Write 1 to trigger one alert event of this kind. |

## CFG_REGWEN
Controls the configurability of [`FATAL_ALERT_EN`](#fatal_alert_en) register.
- Offset: `0x10`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description           |
|:------:|:------:|:-------:|:-------|:----------------------|
|  31:1  |        |         |        | Reserved              |
|   0    |  rw0c  |   0x1   | EN     | Configuration enable. |

## ALERT_TRIG
Alert trigger test
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0x7ff`

### Fields

```wavejson
{"reg": [{"name": "VAL_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VAL_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VAL_2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VAL_3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VAL_4", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VAL_5", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VAL_6", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VAL_7", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VAL_8", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VAL_9", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VAL_10", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 21}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                         |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:11  |        |         |        | Reserved                                                                                                                                            |
|   10   |   rw   |   0x0   | VAL_10 | Alert trigger for testing 0 No alerts triggered 1 Continuously trigger alert until disabled For bit mapping, please see [`ALERT_TEST`](#alert_test) |
|   9    |   rw   |   0x0   | VAL_9  | Alert trigger for testing 0 No alerts triggered 1 Continuously trigger alert until disabled For bit mapping, please see [`ALERT_TEST`](#alert_test) |
|   8    |   rw   |   0x0   | VAL_8  | Alert trigger for testing 0 No alerts triggered 1 Continuously trigger alert until disabled For bit mapping, please see [`ALERT_TEST`](#alert_test) |
|   7    |   rw   |   0x0   | VAL_7  | Alert trigger for testing 0 No alerts triggered 1 Continuously trigger alert until disabled For bit mapping, please see [`ALERT_TEST`](#alert_test) |
|   6    |   rw   |   0x0   | VAL_6  | Alert trigger for testing 0 No alerts triggered 1 Continuously trigger alert until disabled For bit mapping, please see [`ALERT_TEST`](#alert_test) |
|   5    |   rw   |   0x0   | VAL_5  | Alert trigger for testing 0 No alerts triggered 1 Continuously trigger alert until disabled For bit mapping, please see [`ALERT_TEST`](#alert_test) |
|   4    |   rw   |   0x0   | VAL_4  | Alert trigger for testing 0 No alerts triggered 1 Continuously trigger alert until disabled For bit mapping, please see [`ALERT_TEST`](#alert_test) |
|   3    |   rw   |   0x0   | VAL_3  | Alert trigger for testing 0 No alerts triggered 1 Continuously trigger alert until disabled For bit mapping, please see [`ALERT_TEST`](#alert_test) |
|   2    |   rw   |   0x0   | VAL_2  | Alert trigger for testing 0 No alerts triggered 1 Continuously trigger alert until disabled For bit mapping, please see [`ALERT_TEST`](#alert_test) |
|   1    |   rw   |   0x0   | VAL_1  | Alert trigger for testing 0 No alerts triggered 1 Continuously trigger alert until disabled For bit mapping, please see [`ALERT_TEST`](#alert_test) |
|   0    |   rw   |   0x0   | VAL_0  | Alert trigger for testing 0 No alerts triggered 1 Continuously trigger alert until disabled For bit mapping, please see [`ALERT_TEST`](#alert_test) |

## ALERT_EN
Each multibit value enables a corresponding alert.
- Reset default: `0x6`
- Reset mask: `0xf`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Instances

| Name        | Offset   |
|:------------|:---------|
| ALERT_EN_0  | 0x18     |
| ALERT_EN_1  | 0x1c     |
| ALERT_EN_2  | 0x20     |
| ALERT_EN_3  | 0x24     |
| ALERT_EN_4  | 0x28     |
| ALERT_EN_5  | 0x2c     |
| ALERT_EN_6  | 0x30     |
| ALERT_EN_7  | 0x34     |
| ALERT_EN_8  | 0x38     |
| ALERT_EN_9  | 0x3c     |
| ALERT_EN_10 | 0x40     |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                  |
|:------:|:------:|:-------:|:----------------------|
|  31:4  |        |         | Reserved              |
|  3:0   |   rw   |   0x6   | [VAL](#alert_en--val) |

### ALERT_EN . VAL
kMultiBitBool4True - An alert event is enabled.
kMultiBitBool4False - An alert event is disabled.

At reset, all alerts are enabled.
This is by design so that no alerts get missed unless they get disabled explicitly.
Firmware can disable alerts that may be problematic for the designated use case.

## FATAL_ALERT_EN
Each bit marks a corresponding alert as fatal or recoverable.

Note that alerts are ignored if they are not enabled in [`ALERT_EN.`](#alert_en)
- Offset: `0x44`
- Reset default: `0x0`
- Reset mask: `0x7ff`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "VAL_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VAL_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VAL_2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VAL_3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VAL_4", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VAL_5", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VAL_6", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VAL_7", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VAL_8", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VAL_9", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VAL_10", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 21}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                              |
|:------:|:------:|:-------:|:----------------------------------|
| 31:11  |        |         | Reserved                          |
|   10   |   rw   |   0x0   | [VAL_10](#fatal_alert_en--val_10) |
|   9    |   rw   |   0x0   | [VAL_9](#fatal_alert_en--val_9)   |
|   8    |   rw   |   0x0   | [VAL_8](#fatal_alert_en--val_8)   |
|   7    |   rw   |   0x0   | [VAL_7](#fatal_alert_en--val_7)   |
|   6    |   rw   |   0x0   | [VAL_6](#fatal_alert_en--val_6)   |
|   5    |   rw   |   0x0   | [VAL_5](#fatal_alert_en--val_5)   |
|   4    |   rw   |   0x0   | [VAL_4](#fatal_alert_en--val_4)   |
|   3    |   rw   |   0x0   | [VAL_3](#fatal_alert_en--val_3)   |
|   2    |   rw   |   0x0   | [VAL_2](#fatal_alert_en--val_2)   |
|   1    |   rw   |   0x0   | [VAL_1](#fatal_alert_en--val_1)   |
|   0    |   rw   |   0x0   | [VAL_0](#fatal_alert_en--val_0)   |

### FATAL_ALERT_EN . VAL_10
1 - An alert event is fatal.
0 - An alert event is recoverable.

At reset, all alerts are recoverable.
This is by design so that a false-positive alert event early in the reset sequence doesn't jam the alert until the next reset.
Firmware can define alerts that are critical for the designated use case as fatal.

### FATAL_ALERT_EN . VAL_9
1 - An alert event is fatal.
0 - An alert event is recoverable.

At reset, all alerts are recoverable.
This is by design so that a false-positive alert event early in the reset sequence doesn't jam the alert until the next reset.
Firmware can define alerts that are critical for the designated use case as fatal.

### FATAL_ALERT_EN . VAL_8
1 - An alert event is fatal.
0 - An alert event is recoverable.

At reset, all alerts are recoverable.
This is by design so that a false-positive alert event early in the reset sequence doesn't jam the alert until the next reset.
Firmware can define alerts that are critical for the designated use case as fatal.

### FATAL_ALERT_EN . VAL_7
1 - An alert event is fatal.
0 - An alert event is recoverable.

At reset, all alerts are recoverable.
This is by design so that a false-positive alert event early in the reset sequence doesn't jam the alert until the next reset.
Firmware can define alerts that are critical for the designated use case as fatal.

### FATAL_ALERT_EN . VAL_6
1 - An alert event is fatal.
0 - An alert event is recoverable.

At reset, all alerts are recoverable.
This is by design so that a false-positive alert event early in the reset sequence doesn't jam the alert until the next reset.
Firmware can define alerts that are critical for the designated use case as fatal.

### FATAL_ALERT_EN . VAL_5
1 - An alert event is fatal.
0 - An alert event is recoverable.

At reset, all alerts are recoverable.
This is by design so that a false-positive alert event early in the reset sequence doesn't jam the alert until the next reset.
Firmware can define alerts that are critical for the designated use case as fatal.

### FATAL_ALERT_EN . VAL_4
1 - An alert event is fatal.
0 - An alert event is recoverable.

At reset, all alerts are recoverable.
This is by design so that a false-positive alert event early in the reset sequence doesn't jam the alert until the next reset.
Firmware can define alerts that are critical for the designated use case as fatal.

### FATAL_ALERT_EN . VAL_3
1 - An alert event is fatal.
0 - An alert event is recoverable.

At reset, all alerts are recoverable.
This is by design so that a false-positive alert event early in the reset sequence doesn't jam the alert until the next reset.
Firmware can define alerts that are critical for the designated use case as fatal.

### FATAL_ALERT_EN . VAL_2
1 - An alert event is fatal.
0 - An alert event is recoverable.

At reset, all alerts are recoverable.
This is by design so that a false-positive alert event early in the reset sequence doesn't jam the alert until the next reset.
Firmware can define alerts that are critical for the designated use case as fatal.

### FATAL_ALERT_EN . VAL_1
1 - An alert event is fatal.
0 - An alert event is recoverable.

At reset, all alerts are recoverable.
This is by design so that a false-positive alert event early in the reset sequence doesn't jam the alert until the next reset.
Firmware can define alerts that are critical for the designated use case as fatal.

### FATAL_ALERT_EN . VAL_0
1 - An alert event is fatal.
0 - An alert event is recoverable.

At reset, all alerts are recoverable.
This is by design so that a false-positive alert event early in the reset sequence doesn't jam the alert until the next reset.
Firmware can define alerts that are critical for the designated use case as fatal.

## RECOV_ALERT
Each bit represents a recoverable alert that has been triggered by AST.
Since these are recoverable alerts, they can be cleared by software.
- Offset: `0x48`
- Reset default: `0x0`
- Reset mask: `0x7ff`

### Fields

```wavejson
{"reg": [{"name": "VAL_0", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "VAL_1", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "VAL_2", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "VAL_3", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "VAL_4", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "VAL_5", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "VAL_6", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "VAL_7", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "VAL_8", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "VAL_9", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "VAL_10", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 21}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                     |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------|
| 31:11  |        |         |        | Reserved                                                        |
|   10   |  rw1c  |   0x0   | VAL_10 | 1 - An alert event has been set 0 - No alert event has been set |
|   9    |  rw1c  |   0x0   | VAL_9  | 1 - An alert event has been set 0 - No alert event has been set |
|   8    |  rw1c  |   0x0   | VAL_8  | 1 - An alert event has been set 0 - No alert event has been set |
|   7    |  rw1c  |   0x0   | VAL_7  | 1 - An alert event has been set 0 - No alert event has been set |
|   6    |  rw1c  |   0x0   | VAL_6  | 1 - An alert event has been set 0 - No alert event has been set |
|   5    |  rw1c  |   0x0   | VAL_5  | 1 - An alert event has been set 0 - No alert event has been set |
|   4    |  rw1c  |   0x0   | VAL_4  | 1 - An alert event has been set 0 - No alert event has been set |
|   3    |  rw1c  |   0x0   | VAL_3  | 1 - An alert event has been set 0 - No alert event has been set |
|   2    |  rw1c  |   0x0   | VAL_2  | 1 - An alert event has been set 0 - No alert event has been set |
|   1    |  rw1c  |   0x0   | VAL_1  | 1 - An alert event has been set 0 - No alert event has been set |
|   0    |  rw1c  |   0x0   | VAL_0  | 1 - An alert event has been set 0 - No alert event has been set |

## FATAL_ALERT
Each bit represents a fatal alert that has been triggered by AST.
Since these registers represent fatal alerts, they cannot be cleared.

The lower bits are used for ast alert events.
The upper bits are used for local events.
- Offset: `0x4c`
- Reset default: `0x0`
- Reset mask: `0xfff`

### Fields

```wavejson
{"reg": [{"name": "VAL_0", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VAL_1", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VAL_2", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VAL_3", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VAL_4", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VAL_5", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VAL_6", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VAL_7", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VAL_8", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VAL_9", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VAL_10", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VAL_11", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 20}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                     |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------|
| 31:12  |        |         |        | Reserved                                                        |
|   11   |   ro   |   0x0   | VAL_11 | 1 - An alert event has been set 0 - No alert event has been set |
|   10   |   ro   |   0x0   | VAL_10 | 1 - An alert event has been set 0 - No alert event has been set |
|   9    |   ro   |   0x0   | VAL_9  | 1 - An alert event has been set 0 - No alert event has been set |
|   8    |   ro   |   0x0   | VAL_8  | 1 - An alert event has been set 0 - No alert event has been set |
|   7    |   ro   |   0x0   | VAL_7  | 1 - An alert event has been set 0 - No alert event has been set |
|   6    |   ro   |   0x0   | VAL_6  | 1 - An alert event has been set 0 - No alert event has been set |
|   5    |   ro   |   0x0   | VAL_5  | 1 - An alert event has been set 0 - No alert event has been set |
|   4    |   ro   |   0x0   | VAL_4  | 1 - An alert event has been set 0 - No alert event has been set |
|   3    |   ro   |   0x0   | VAL_3  | 1 - An alert event has been set 0 - No alert event has been set |
|   2    |   ro   |   0x0   | VAL_2  | 1 - An alert event has been set 0 - No alert event has been set |
|   1    |   ro   |   0x0   | VAL_1  | 1 - An alert event has been set 0 - No alert event has been set |
|   0    |   ro   |   0x0   | VAL_0  | 1 - An alert event has been set 0 - No alert event has been set |

## STATUS
Status readback for ast
- Offset: `0x50`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "ast_init_done", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "io_pok", "bits": 2, "attr": ["ro"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                   |
|:------:|:------:|:-------:|:--------------|:------------------------------|
|  31:3  |        |         |               | Reserved                      |
|  2:1   |   ro   |   0x0   | io_pok        | IO power is ready             |
|   0    |   ro   |   0x0   | ast_init_done | AST has finished initializing |

## MANUAL_PAD_ATTR_REGWEN
Register write enable for attributes of manual pads
- Reset default: `0x1`
- Reset mask: `0x1`

### Instances

| Name                     | Offset   |
|:-------------------------|:---------|
| MANUAL_PAD_ATTR_REGWEN_0 | 0x54     |
| MANUAL_PAD_ATTR_REGWEN_1 | 0x58     |
| MANUAL_PAD_ATTR_REGWEN_2 | 0x5c     |
| MANUAL_PAD_ATTR_REGWEN_3 | 0x60     |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                          |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                                                             |
|   0    |  rw0c  |   0x1   | EN     | Register write enable bit. If this is cleared to 0, the corresponding [`MANUAL_PAD_ATTR`](#manual_pad_attr) is not writable anymore. |

## MANUAL_PAD_ATTR
Attributes of manual pads.
This register has WARL behavior since not every pad may support each attribute.
The mapping of registers to pads is as follows (only supported for targets that instantiate `chip_earlgrey_asic`):
- MANUAL_PAD_ATTR_0: CC1
- MANUAL_PAD_ATTR_1: CC2
- MANUAL_PAD_ATTR_2: FLASH_TEST_MODE0
- MANUAL_PAD_ATTR_3: FLASH_TEST_MODE1
- Reset default: `0x0`
- Reset mask: `0x8c`
- Register enable: [`MANUAL_PAD_ATTR_REGWEN`](#manual_pad_attr_regwen)

### Instances

| Name              | Offset   |
|:------------------|:---------|
| MANUAL_PAD_ATTR_0 | 0x64     |
| MANUAL_PAD_ATTR_1 | 0x68     |
| MANUAL_PAD_ATTR_2 | 0x6c     |
| MANUAL_PAD_ATTR_3 | 0x70     |


### Fields

```wavejson
{"reg": [{"bits": 2}, {"name": "pull_en", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "pull_select", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 3}, {"name": "input_disable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name                                             |
|:------:|:------:|:-------:|:-------------------------------------------------|
|  31:8  |        |         | Reserved                                         |
|   7    |   rw   |   0x0   | [input_disable](#manual_pad_attr--input_disable) |
|  6:4   |        |         | Reserved                                         |
|   3    |   rw   |   0x0   | [pull_select](#manual_pad_attr--pull_select)     |
|   2    |   rw   |   0x0   | [pull_en](#manual_pad_attr--pull_en)             |
|  1:0   |        |         | Reserved                                         |

### MANUAL_PAD_ATTR . input_disable
Disable input drivers.
Setting this to 1 for pads that are not used as input can reduce their leakage current.

### MANUAL_PAD_ATTR . pull_select
Pull select (0: pull-down, 1: pull-up).

| Value   | Name      | Description                    |
|:--------|:----------|:-------------------------------|
| 0x0     | pull_down | Select the pull-down resistor. |
| 0x1     | pull_up   | Select the pull-up resistor.   |


### MANUAL_PAD_ATTR . pull_en
Enable pull-up or pull-down resistor.


<!-- END CMDGEN -->
