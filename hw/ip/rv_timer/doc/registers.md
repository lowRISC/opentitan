# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/rv_timer/data/rv_timer.hjson -->
## Summary

| Name                                             | Offset   |   Length | Description              |
|:-------------------------------------------------|:---------|---------:|:-------------------------|
| rv_timer.[`ALERT_TEST`](#alert_test)             | 0x0      |        4 | Alert Test Register      |
| rv_timer.[`CTRL`](#CTRL)                         | 0x4      |        4 | Control register         |
| rv_timer.[`INTR_ENABLE0`](#INTR_ENABLE0)         | 0x100    |        4 | Interrupt Enable         |
| rv_timer.[`INTR_STATE0`](#INTR_STATE0)           | 0x104    |        4 | Interrupt Status         |
| rv_timer.[`INTR_TEST0`](#INTR_TEST0)             | 0x108    |        4 | Interrupt test register  |
| rv_timer.[`CFG0`](#cfg0)                         | 0x10c    |        4 | Configuration for Hart 0 |
| rv_timer.[`TIMER_V_LOWER0`](#timer_v_lower0)     | 0x110    |        4 | Timer value Lower        |
| rv_timer.[`TIMER_V_UPPER0`](#timer_v_upper0)     | 0x114    |        4 | Timer value Upper        |
| rv_timer.[`COMPARE_LOWER0_0`](#compare_lower0_0) | 0x118    |        4 | Timer value Lower        |
| rv_timer.[`COMPARE_UPPER0_0`](#compare_upper0_0) | 0x11c    |        4 | Timer value Upper        |

## ALERT_TEST
Alert Test Register
- Offset: `0x0`
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

## CTRL
Control register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "active_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name     | Description          |
|:------:|:------:|:-------:|:---------|:---------------------|
|  31:1  |        |         |          | Reserved             |
|   0    |   rw   |   0x0   | active_0 | If 1, timer operates |

## INTR_ENABLE0
Interrupt Enable
- Offset: `0x100`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "IE_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                |
|:------:|:------:|:-------:|:-------|:---------------------------|
|  31:1  |        |         |        | Reserved                   |
|   0    |   rw   |   0x0   | IE_0   | Interrupt Enable for timer |

## INTR_STATE0
Interrupt Status
- Offset: `0x104`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "IS_0", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                |
|:------:|:------:|:-------:|:-------|:---------------------------|
|  31:1  |        |         |        | Reserved                   |
|   0    |  rw1c  |   0x0   | IS_0   | Interrupt status for timer |

## INTR_TEST0
Interrupt test register
- Offset: `0x108`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "T_0", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description              |
|:------:|:------:|:-------:|:-------|:-------------------------|
|  31:1  |        |         |        | Reserved                 |
|   0    |   wo   |    x    | T_0    | Interrupt test for timer |

## CFG0
Configuration for Hart 0
- Offset: `0x10c`
- Reset default: `0x10000`
- Reset mask: `0xff0fff`

### Fields

```wavejson
{"reg": [{"name": "prescale", "bits": 12, "attr": ["rw"], "rotate": 0}, {"bits": 4}, {"name": "step", "bits": 8, "attr": ["rw"], "rotate": 0}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                     |
|:------:|:------:|:-------:|:---------|:--------------------------------|
| 31:24  |        |         |          | Reserved                        |
| 23:16  |   rw   |   0x1   | step     | Incremental value for each tick |
| 15:12  |        |         |          | Reserved                        |
|  11:0  |   rw   |   0x0   | prescale | Prescaler to generate tick      |

## TIMER_V_LOWER0
Timer value Lower
- Offset: `0x110`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "v", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description        |
|:------:|:------:|:-------:|:-------|:-------------------|
|  31:0  |   rw   |   0x0   | v      | Timer value [31:0] |

## TIMER_V_UPPER0
Timer value Upper
- Offset: `0x114`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "v", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description         |
|:------:|:------:|:-------:|:-------|:--------------------|
|  31:0  |   rw   |   0x0   | v      | Timer value [63:32] |

## COMPARE_LOWER0_0
Timer value Lower
- Offset: `0x118`
- Reset default: `0xffffffff`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "v", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |   Reset    | Name   | Description                |
|:------:|:------:|:----------:|:-------|:---------------------------|
|  31:0  |   rw   | 0xffffffff | v      | Timer compare value [31:0] |

## COMPARE_UPPER0_0
Timer value Upper
- Offset: `0x11c`
- Reset default: `0xffffffff`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "v", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |   Reset    | Name   | Description                 |
|:------:|:------:|:----------:|:-------|:----------------------------|
|  31:0  |   rw   | 0xffffffff | v      | Timer compare value [63:32] |


<!-- END CMDGEN -->
