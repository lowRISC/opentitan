# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/aon_timer/data/aon_timer.hjson -->
## Summary

| Name                                            | Offset   |   Length | Description                            |
|:------------------------------------------------|:---------|---------:|:---------------------------------------|
| aon_timer.[`ALERT_TEST`](#alert_test)           | 0x0      |        4 | Alert Test Register                    |
| aon_timer.[`WKUP_CTRL`](#wkup_ctrl)             | 0x4      |        4 | Wakeup Timer Control register          |
| aon_timer.[`WKUP_THOLD`](#wkup_thold)           | 0x8      |        4 | Wakeup Timer Threshold Register        |
| aon_timer.[`WKUP_COUNT`](#wkup_count)           | 0xc      |        4 | Wakeup Timer Count Register            |
| aon_timer.[`WDOG_REGWEN`](#wdog_regwen)         | 0x10     |        4 | Watchdog Timer Write Enable Register   |
| aon_timer.[`WDOG_CTRL`](#wdog_ctrl)             | 0x14     |        4 | Watchdog Timer Control register        |
| aon_timer.[`WDOG_BARK_THOLD`](#wdog_bark_thold) | 0x18     |        4 | Watchdog Timer Bark Threshold Register |
| aon_timer.[`WDOG_BITE_THOLD`](#wdog_bite_thold) | 0x1c     |        4 | Watchdog Timer Bite Threshold Register |
| aon_timer.[`WDOG_COUNT`](#wdog_count)           | 0x20     |        4 | Watchdog Timer Count Register          |
| aon_timer.[`INTR_STATE`](#intr_state)           | 0x24     |        4 | Interrupt State Register               |
| aon_timer.[`INTR_TEST`](#intr_test)             | 0x28     |        4 | Interrupt Test Register                |
| aon_timer.[`WKUP_CAUSE`](#wkup_cause)           | 0x2c     |        4 | Wakeup request status                  |

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

## WKUP_CTRL
Wakeup Timer Control register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x1fff`

### Fields

```wavejson
{"reg": [{"name": "enable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "prescaler", "bits": 12, "attr": ["rw"], "rotate": 0}, {"bits": 19}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                |
|:------:|:------:|:-------:|:----------|:-------------------------------------------|
| 31:13  |        |         |           | Reserved                                   |
|  12:1  |   rw   |   0x0   | prescaler | Pre-scaler value for wakeup timer count    |
|   0    |   rw   |   0x0   | enable    | When set to 1, the wakeup timer will count |

## WKUP_THOLD
Wakeup Timer Threshold Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "threshold", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                               |
|:------:|:------:|:-------:|:----------|:----------------------------------------------------------|
|  31:0  |   rw   |   0x0   | threshold | The count at which a wakeup interrupt should be generated |

## WKUP_COUNT
Wakeup Timer Count Register
- Offset: `0xc`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "count", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                      |
|:------:|:------:|:-------:|:-------|:---------------------------------|
|  31:0  |   rw   |   0x0   | count  | The current wakeup counter value |

## WDOG_REGWEN
Watchdog Timer Write Enable Register
- Offset: `0x10`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "regwen", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                  |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                     |
|   0    |  rw0c  |   0x1   | regwen | Once cleared, the watchdog configuration will be locked until the next reset |

## WDOG_CTRL
Watchdog Timer Control register
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0x3`
- Register enable: [`WDOG_REGWEN`](#wdog_regwen)

### Fields

```wavejson
{"reg": [{"name": "enable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "pause_in_sleep", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                                                   |
|:------:|:------:|:-------:|:---------------|:--------------------------------------------------------------|
|  31:2  |        |         |                | Reserved                                                      |
|   1    |   rw   |   0x0   | pause_in_sleep | When set to 1, the watchdog timer will not count during sleep |
|   0    |   rw   |   0x0   | enable         | When set to 1, the watchdog timer will count                  |

## WDOG_BARK_THOLD
Watchdog Timer Bark Threshold Register
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`WDOG_REGWEN`](#wdog_regwen)

### Fields

```wavejson
{"reg": [{"name": "threshold", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                      |
|:------:|:------:|:-------:|:----------|:-----------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | threshold | The count at which a watchdog bark interrupt should be generated |

## WDOG_BITE_THOLD
Watchdog Timer Bite Threshold Register
- Offset: `0x1c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`WDOG_REGWEN`](#wdog_regwen)

### Fields

```wavejson
{"reg": [{"name": "threshold", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                  |
|:------:|:------:|:-------:|:----------|:-------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | threshold | The count at which a watchdog bite reset should be generated |

## WDOG_COUNT
Watchdog Timer Count Register
- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "count", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                        |
|:------:|:------:|:-------:|:-------|:-----------------------------------|
|  31:0  |   rw   |   0x0   | count  | The current watchdog counter value |

## INTR_STATE
Interrupt State Register
- Offset: `0x24`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "wkup_timer_expired", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "wdog_timer_bark", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                                |
|:------:|:------:|:-------:|:-------------------|:-----------------------------------------------------------|
|  31:2  |        |         |                    | Reserved                                                   |
|   1    |  rw1c  |   0x0   | wdog_timer_bark    | Raised if the watchdog timer has hit the bark threshold    |
|   0    |  rw1c  |   0x0   | wkup_timer_expired | Raised if the wakeup timer has hit the specified threshold |

## INTR_TEST
Interrupt Test Register
- Offset: `0x28`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "wkup_timer_expired", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "wdog_timer_bark", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                   |
|:------:|:------:|:-------:|:-------------------|:----------------------------------------------|
|  31:2  |        |         |                    | Reserved                                      |
|   1    |   wo   |    x    | wdog_timer_bark    | Write 1 to force wdog_timer_bark interrupt    |
|   0    |   wo   |    x    | wkup_timer_expired | Write 1 to force wkup_timer_expired interrupt |

## WKUP_CAUSE
Wakeup request status
- Offset: `0x2c`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "cause", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                  |
|:------:|:------:|:-------:|:-------|:---------------------------------------------|
|  31:1  |        |         |        | Reserved                                     |
|   0    |  rw0c  |   0x0   | cause  | AON timer requested wakeup, write 0 to clear |


<!-- END CMDGEN -->
