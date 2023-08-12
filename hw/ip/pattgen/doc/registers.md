# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/pattgen/data/pattgen.hjson -->
## Summary

| Name                                  | Offset   |   Length | Description                                         |
|:--------------------------------------|:---------|---------:|:----------------------------------------------------|
| pattgen.[`INTR_STATE`](#intr_state)   | 0x0      |        4 | Interrupt State Register                            |
| pattgen.[`INTR_ENABLE`](#intr_enable) | 0x4      |        4 | Interrupt Enable Register                           |
| pattgen.[`INTR_TEST`](#intr_test)     | 0x8      |        4 | Interrupt Test Register                             |
| pattgen.[`ALERT_TEST`](#alert_test)   | 0xc      |        4 | Alert Test Register                                 |
| pattgen.[`CTRL`](#ctrl)               | 0x10     |        4 | PATTGEN control register                            |
| pattgen.[`PREDIV_CH0`](#prediv_ch0)   | 0x14     |        4 | PATTGEN pre-divider register for Channel 0          |
| pattgen.[`PREDIV_CH1`](#prediv_ch1)   | 0x18     |        4 | PATTGEN pre-divider register for Channel 1          |
| pattgen.[`DATA_CH0_0`](#data_ch0)     | 0x1c     |        4 | PATTGEN seed pattern multi-registers for Channel 0. |
| pattgen.[`DATA_CH0_1`](#data_ch0)     | 0x20     |        4 | PATTGEN seed pattern multi-registers for Channel 0. |
| pattgen.[`DATA_CH1_0`](#data_ch1)     | 0x24     |        4 | PATTGEN seed pattern multi-registers for Channel 1. |
| pattgen.[`DATA_CH1_1`](#data_ch1)     | 0x28     |        4 | PATTGEN seed pattern multi-registers for Channel 1. |
| pattgen.[`SIZE`](#size)               | 0x2c     |        4 | PATTGEN pattern length                              |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "done_ch0", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "done_ch1", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                          |
|:------:|:------:|:-------:|:---------|:-----------------------------------------------------|
|  31:2  |        |         |          | Reserved                                             |
|   1    |  rw1c  |   0x0   | done_ch1 | raise if pattern generation on Channel 1 is complete |
|   0    |  rw1c  |   0x0   | done_ch0 | raise if pattern generation on Channel 0 is complete |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "done_ch0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "done_ch1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                        |
|:------:|:------:|:-------:|:---------|:-------------------------------------------------------------------|
|  31:2  |        |         |          | Reserved                                                           |
|   1    |   rw   |   0x0   | done_ch1 | Enable interrupt when [`INTR_STATE.done_ch1`](#intr_state) is set. |
|   0    |   rw   |   0x0   | done_ch0 | Enable interrupt when [`INTR_STATE.done_ch0`](#intr_state) is set. |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "done_ch0", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "done_ch1", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                 |
|:------:|:------:|:-------:|:---------|:------------------------------------------------------------|
|  31:2  |        |         |          | Reserved                                                    |
|   1    |   wo   |   0x0   | done_ch1 | Write 1 to force [`INTR_STATE.done_ch1`](#intr_state) to 1. |
|   0    |   wo   |   0x0   | done_ch0 | Write 1 to force [`INTR_STATE.done_ch0`](#intr_state) to 1. |

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

## CTRL
PATTGEN control register
- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "ENABLE_CH0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ENABLE_CH1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "POLARITY_CH0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "POLARITY_CH1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                                                                                                                                                                                                                     |
|:------:|:------:|:-------:|:-------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:4  |        |         |              | Reserved                                                                                                                                                                                                                                        |
|   3    |   rw   |   0x0   | POLARITY_CH1 | Clock (`pcl`) polarity for Channel 1.  If low, `pda` signal changes on falling edge of `pcl` signal, otherwise pda changes on rising edge. Note that writes to a channel's configuration registers have no effect while the channel is enabled. |
|   2    |   rw   |   0x0   | POLARITY_CH0 | Clock (`pcl`) polarity for Channel 0.  If low, `pda` signal changes on falling edge of pcl signal, otherwise pda changes on rising edge. Note that writes to a channel's configuration registers have no effect while the channel is enabled.   |
|   1    |   rw   |   0x0   | ENABLE_CH1   | Enable pattern generator functionality for Channel 1                                                                                                                                                                                            |
|   0    |   rw   |   0x0   | ENABLE_CH0   | Enable pattern generator functionality for Channel 0                                                                                                                                                                                            |

## PREDIV_CH0
PATTGEN pre-divider register for Channel 0
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "CLK_RATIO", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                                                                                                                     |
|:------:|:------:|:-------:|:----------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | CLK_RATIO | Clock divider ratio fpr Channel 0 (relative to I/O clock). Note that writes to a channel's configuration registers have no effect while the channel is enabled. |

## PREDIV_CH1
PATTGEN pre-divider register for Channel 1
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "CLK_RATIO", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                                                                                                                     |
|:------:|:------:|:-------:|:----------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | CLK_RATIO | Clock divider ratio for Channel 1 (relative to I/O clock). Note that writes to a channel's configuration registers have no effect while the channel is enabled. |

## DATA_CH0
PATTGEN seed pattern multi-registers for Channel 0.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name       | Offset   |
|:-----------|:---------|
| DATA_CH0_0 | 0x1c     |
| DATA_CH0_1 | 0x20     |


### Fields

```wavejson
{"reg": [{"name": "DATA", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                  |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | DATA   | Seed pattern for Channel 0 (1-64 bits). Note that writes to a channel's configuration registers have no effect while the channel is enabled. |

## DATA_CH1
PATTGEN seed pattern multi-registers for Channel 1.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name       | Offset   |
|:-----------|:---------|
| DATA_CH1_0 | 0x24     |
| DATA_CH1_1 | 0x28     |


### Fields

```wavejson
{"reg": [{"name": "DATA", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                  |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | DATA   | Seed pattern for Channel 1 (1-64 bits). Note that writes to a channel's configuration registers have no effect while the channel is enabled. |

## SIZE
PATTGEN pattern length
- Offset: `0x2c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "LEN_CH0", "bits": 6, "attr": ["rw"], "rotate": 0}, {"name": "REPS_CH0", "bits": 10, "attr": ["rw"], "rotate": 0}, {"name": "LEN_CH1", "bits": 6, "attr": ["rw"], "rotate": 0}, {"name": "REPS_CH1", "bits": 10, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                                                                                                                                       |
|:------:|:------:|:-------:|:---------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:22  |   rw   |   0x0   | REPS_CH1 | Number of pattern repetitions for Channel 1, minus 1. Valid values: 0..1023. Note that writes to a channel's configuration registers have no effect while the channel is enabled. |
| 21:16  |   rw   |   0x0   | LEN_CH1  | Length of the seed pattern for Channel 1, minus 1. Valid values: 0..63. Note that writes to a channel's configuration registers have no effect while the channel is enabled.      |
|  15:6  |   rw   |   0x0   | REPS_CH0 | Number of pattern repetitions for Channel 0, minus 1. Valid values: 0..1023. Note that writes to a channel's configuration registers have no effect while the channel is enabled. |
|  5:0   |   rw   |   0x0   | LEN_CH0  | Length of the seed pattern for Channel 0, minus 1. Valid values: 0..63. Note that writes to a channel's configuration registers have no effect while the channel is enabled.      |


<!-- END CMDGEN -->
