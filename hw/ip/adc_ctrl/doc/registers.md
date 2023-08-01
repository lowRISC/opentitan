# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/adc_ctrl/data/adc_ctrl.hjson -->
## Summary

| Name                                                     | Offset   |   Length | Description                               |
|:---------------------------------------------------------|:---------|---------:|:------------------------------------------|
| adc_ctrl.[`INTR_STATE`](#intr_state)                     | 0x0      |        4 | Interrupt State Register                  |
| adc_ctrl.[`INTR_ENABLE`](#intr_enable)                   | 0x4      |        4 | Interrupt Enable Register                 |
| adc_ctrl.[`INTR_TEST`](#intr_test)                       | 0x8      |        4 | Interrupt Test Register                   |
| adc_ctrl.[`ALERT_TEST`](#alert_test)                     | 0xc      |        4 | Alert Test Register                       |
| adc_ctrl.[`adc_en_ctl`](#adc_en_ctl)                     | 0x10     |        4 | ADC enable control register               |
| adc_ctrl.[`adc_pd_ctl`](#adc_pd_ctl)                     | 0x14     |        4 | ADC PowerDown(PD) control register        |
| adc_ctrl.[`adc_lp_sample_ctl`](#adc_lp_sample_ctl)       | 0x18     |        4 | ADC Low-Power(LP) sample control register |
| adc_ctrl.[`adc_sample_ctl`](#adc_sample_ctl)             | 0x1c     |        4 | ADC sample control register               |
| adc_ctrl.[`adc_fsm_rst`](#adc_fsm_rst)                   | 0x20     |        4 | ADC FSM reset control                     |
| adc_ctrl.[`adc_chn0_filter_ctl_0`](#adc_chn0_filter_ctl) | 0x24     |        4 | ADC channel0 filter range                 |
| adc_ctrl.[`adc_chn0_filter_ctl_1`](#adc_chn0_filter_ctl) | 0x28     |        4 | ADC channel0 filter range                 |
| adc_ctrl.[`adc_chn0_filter_ctl_2`](#adc_chn0_filter_ctl) | 0x2c     |        4 | ADC channel0 filter range                 |
| adc_ctrl.[`adc_chn0_filter_ctl_3`](#adc_chn0_filter_ctl) | 0x30     |        4 | ADC channel0 filter range                 |
| adc_ctrl.[`adc_chn0_filter_ctl_4`](#adc_chn0_filter_ctl) | 0x34     |        4 | ADC channel0 filter range                 |
| adc_ctrl.[`adc_chn0_filter_ctl_5`](#adc_chn0_filter_ctl) | 0x38     |        4 | ADC channel0 filter range                 |
| adc_ctrl.[`adc_chn0_filter_ctl_6`](#adc_chn0_filter_ctl) | 0x3c     |        4 | ADC channel0 filter range                 |
| adc_ctrl.[`adc_chn0_filter_ctl_7`](#adc_chn0_filter_ctl) | 0x40     |        4 | ADC channel0 filter range                 |
| adc_ctrl.[`adc_chn1_filter_ctl_0`](#adc_chn1_filter_ctl) | 0x44     |        4 | ADC channel1 filter range                 |
| adc_ctrl.[`adc_chn1_filter_ctl_1`](#adc_chn1_filter_ctl) | 0x48     |        4 | ADC channel1 filter range                 |
| adc_ctrl.[`adc_chn1_filter_ctl_2`](#adc_chn1_filter_ctl) | 0x4c     |        4 | ADC channel1 filter range                 |
| adc_ctrl.[`adc_chn1_filter_ctl_3`](#adc_chn1_filter_ctl) | 0x50     |        4 | ADC channel1 filter range                 |
| adc_ctrl.[`adc_chn1_filter_ctl_4`](#adc_chn1_filter_ctl) | 0x54     |        4 | ADC channel1 filter range                 |
| adc_ctrl.[`adc_chn1_filter_ctl_5`](#adc_chn1_filter_ctl) | 0x58     |        4 | ADC channel1 filter range                 |
| adc_ctrl.[`adc_chn1_filter_ctl_6`](#adc_chn1_filter_ctl) | 0x5c     |        4 | ADC channel1 filter range                 |
| adc_ctrl.[`adc_chn1_filter_ctl_7`](#adc_chn1_filter_ctl) | 0x60     |        4 | ADC channel1 filter range                 |
| adc_ctrl.[`adc_chn_val_0`](#adc_chn_val)                 | 0x64     |        4 | ADC value sampled on channel              |
| adc_ctrl.[`adc_chn_val_1`](#adc_chn_val)                 | 0x68     |        4 | ADC value sampled on channel              |
| adc_ctrl.[`adc_wakeup_ctl`](#adc_wakeup_ctl)             | 0x6c     |        4 | Enable filter matches as wakeups          |
| adc_ctrl.[`filter_status`](#filter_status)               | 0x70     |        4 | Adc filter match status                   |
| adc_ctrl.[`adc_intr_ctl`](#adc_intr_ctl)                 | 0x74     |        4 | Interrupt enable controls.                |
| adc_ctrl.[`adc_intr_status`](#adc_intr_status)           | 0x78     |        4 | Debug cable internal status               |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "match_done", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                         |
|:------:|:------:|:-------:|:-----------|:------------------------------------|
|  31:1  |        |         |            | Reserved                            |
|   0    |  rw1c  |   0x0   | match_done | ADC match or measurement event done |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "match_done", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                          |
|:------:|:------:|:-------:|:-----------|:---------------------------------------------------------------------|
|  31:1  |        |         |            | Reserved                                                             |
|   0    |   rw   |   0x0   | match_done | Enable interrupt when [`INTR_STATE.match_done`](#intr_state) is set. |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "match_done", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                   |
|:------:|:------:|:-------:|:-----------|:--------------------------------------------------------------|
|  31:1  |        |         |            | Reserved                                                      |
|   0    |   wo   |   0x0   | match_done | Write 1 to force [`INTR_STATE.match_done`](#intr_state) to 1. |

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

## adc_en_ctl
ADC enable control register
- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "adc_enable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "oneshot_mode", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                                                                                            |
|:------:|:------:|:-------:|:-------------|:-----------------------------------------------------------------------------------------------------------------------|
|  31:2  |        |         |              | Reserved                                                                                                               |
|   1    |   rw   |   0x0   | oneshot_mode | Oneshot mode does not care about the filter value. 1'b0: disable; 1'b1: enable                                         |
|   0    |   rw   |   0x0   | adc_enable   | 1'b0: to power down ADC and ADC_CTRL FSM will enter the reset state; 1'b1: to power up ADC and ADC_CTRL FSM will start |

## adc_pd_ctl
ADC PowerDown(PD) control register
- Offset: `0x14`
- Reset default: `0x64070`
- Reset mask: `0xfffffff1`

### Fields

```wavejson
{"reg": [{"name": "lp_mode", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 3}, {"name": "pwrup_time", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "wakeup_time", "bits": 24, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                                                                                                                                        |
|:------:|:------:|:-------:|:------------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:8  |   rw   |  0x640  | wakeup_time | How often FSM wakes up from ADC PD mode to take a sample, measured in always on clock cycles.                                                                                      |
|  7:4   |   rw   |   0x7   | pwrup_time  | ADC power up time, measured in always on clock cycles. After power up time is reached, the ADC controller needs one additional cycle before an ADC channel is selected for access. |
|  3:1   |        |         |             | Reserved                                                                                                                                                                           |
|   0    |   rw   |   0x0   | lp_mode     | 1'b0: adc_pd is disabled, use adc_sample_ctl. 1'b1: adc_pd is enabled, use both adc_lp_sample_ctl & adc_sample_ctl                                                                 |

## adc_lp_sample_ctl
ADC Low-Power(LP) sample control register
- Offset: `0x18`
- Reset default: `0x4`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "lp_sample_cnt", "bits": 8, "attr": ["rw"], "rotate": 0}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                                                                                                                                         |
|:------:|:------:|:-------:|:--------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:8  |        |         |               | Reserved                                                                                                                                                                            |
|  7:0   |   rw   |   0x4   | lp_sample_cnt | The number of samples in low-power mode when the low-power mode is enabled. After the programmed number is met, ADC won't be powered down any more. This value must be 1 or larger. |

## adc_sample_ctl
ADC sample control register
- Offset: `0x1c`
- Reset default: `0x9b`
- Reset mask: `0xffff`

### Fields

```wavejson
{"reg": [{"name": "np_sample_cnt", "bits": 16, "attr": ["rw"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                                                                                                                                       |
|:------:|:------:|:-------:|:--------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:16  |        |         |               | Reserved                                                                                                                                                                          |
|  15:0  |   rw   |  0x9b   | np_sample_cnt | The number of samples in normal-power mode to meet the debounce spec. Used after the low-power mode condition is met or in the normal power mode. This value must be 1 or larger. |

## adc_fsm_rst
ADC FSM reset control
- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "rst_en", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                             |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                |
|   0    |   rw   |   0x0   | rst_en | 1'b0: Normal functional mode. 1'b1: SW to reset all the FSMs and timers |

## adc_chn0_filter_ctl
ADC channel0 filter range

Up to 8 filters can be configured per channel and each filter has an associated [min, max] range.
The condition bit then defines whether the sample values of that channel need to lie within the range or outside to create a match.
The filter range bounds can be configured with a granularity of 2.148mV.
- Reset default: `0x0`
- Reset mask: `0x8ffc1ffc`

### Instances

| Name                  | Offset   |
|:----------------------|:---------|
| adc_chn0_filter_ctl_0 | 0x24     |
| adc_chn0_filter_ctl_1 | 0x28     |
| adc_chn0_filter_ctl_2 | 0x2c     |
| adc_chn0_filter_ctl_3 | 0x30     |
| adc_chn0_filter_ctl_4 | 0x34     |
| adc_chn0_filter_ctl_5 | 0x38     |
| adc_chn0_filter_ctl_6 | 0x3c     |
| adc_chn0_filter_ctl_7 | 0x40     |


### Fields

```wavejson
{"reg": [{"bits": 2}, {"name": "min_v", "bits": 10, "attr": ["rw"], "rotate": 0}, {"name": "cond", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 5}, {"name": "max_v", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 3}, {"name": "EN", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                      |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------|
|   31   |   rw   |   0x0   | EN     | Enable for filter                                                                |
| 30:28  |        |         |        | Reserved                                                                         |
| 27:18  |   rw   |   0x0   | max_v  | 10-bit for chn0 filter max value                                                 |
| 17:13  |        |         |        | Reserved                                                                         |
|   12   |   rw   |   0x0   | cond   | 1-bit for the condition; 1'b0 means min<=ADC<=max, 1'b1 means ADC>max or ADC<min |
|  11:2  |   rw   |   0x0   | min_v  | 10-bit for chn0 filter min value                                                 |
|  1:0   |        |         |        | Reserved                                                                         |

## adc_chn1_filter_ctl
ADC channel1 filter range

Up to 8 filters can be configured per channel and each filter has an associated [min, max] range.
The condition bit then defines whether the sample values of that channel need to lie within the range or outside to create a match.
The filter range bounds can be configured with a granularity of 2.148mV.
- Reset default: `0x0`
- Reset mask: `0x8ffc1ffc`

### Instances

| Name                  | Offset   |
|:----------------------|:---------|
| adc_chn1_filter_ctl_0 | 0x44     |
| adc_chn1_filter_ctl_1 | 0x48     |
| adc_chn1_filter_ctl_2 | 0x4c     |
| adc_chn1_filter_ctl_3 | 0x50     |
| adc_chn1_filter_ctl_4 | 0x54     |
| adc_chn1_filter_ctl_5 | 0x58     |
| adc_chn1_filter_ctl_6 | 0x5c     |
| adc_chn1_filter_ctl_7 | 0x60     |


### Fields

```wavejson
{"reg": [{"bits": 2}, {"name": "min_v", "bits": 10, "attr": ["rw"], "rotate": 0}, {"name": "cond", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 5}, {"name": "max_v", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 3}, {"name": "EN", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                      |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------|
|   31   |   rw   |   0x0   | EN     | Enable for filter                                                                |
| 30:28  |        |         |        | Reserved                                                                         |
| 27:18  |   rw   |   0x0   | max_v  | 10-bit for chn0 filter max value                                                 |
| 17:13  |        |         |        | Reserved                                                                         |
|   12   |   rw   |   0x0   | cond   | 1-bit for the condition; 1'b0 means min<=ADC<=max, 1'b1 means ADC>max or ADC<min |
|  11:2  |   rw   |   0x0   | min_v  | 10-bit for chn0 filter min value                                                 |
|  1:0   |        |         |        | Reserved                                                                         |

## adc_chn_val
ADC value sampled on channel
- Reset default: `0x0`
- Reset mask: `0xfff0fff`

### Instances

| Name          | Offset   |
|:--------------|:---------|
| adc_chn_val_0 | 0x64     |
| adc_chn_val_1 | 0x68     |


### Fields

```wavejson
{"reg": [{"name": "adc_chn_value_ext", "bits": 2, "attr": ["ro"], "rotate": -90}, {"name": "adc_chn_value", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "adc_chn_value_intr_ext", "bits": 2, "attr": ["ro"], "rotate": -90}, {"name": "adc_chn_value_intr", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 240}}
```

|  Bits  |  Type  |  Reset  | Name                   | Description                                                                                                              |
|:------:|:------:|:-------:|:-----------------------|:-------------------------------------------------------------------------------------------------------------------------|
| 31:28  |        |         |                        | Reserved                                                                                                                 |
| 27:18  |   ro   |   0x0   | adc_chn_value_intr     | ADC value sampled on channel when the interrupt is raised(debug cable is attached or disconnected), each step is 2.148mV |
| 17:16  |   ro   |   0x0   | adc_chn_value_intr_ext | 2-bit extension; RO 0                                                                                                    |
| 15:12  |        |         |                        | Reserved                                                                                                                 |
|  11:2  |   ro   |   0x0   | adc_chn_value          | Latest ADC value sampled on channel. each step is 2.148mV                                                                |
|  1:0   |   ro   |   0x0   | adc_chn_value_ext      | 2-bit extension; RO 0                                                                                                    |

## adc_wakeup_ctl
Enable filter matches as wakeups
- Offset: `0x6c`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 8, "attr": ["rw"], "rotate": 0}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                    |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------------------------------------|
|  31:8  |        |         |        | Reserved                                                                       |
|  7:0   |   rw   |   0x0   | EN     | 0: filter match wil not generate wakeupe; 1: filter match will generate wakeup |

## filter_status
Adc filter match status

Indicates whether a particular filter has matched on all channels.
- Offset: `0x70`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "COND", "bits": 8, "attr": ["rw1c"], "rotate": 0}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------|
|  31:8  |        |         |        | Reserved                                                   |
|  7:0   |  rw1c  |   0x0   | COND   | 0: filter condition is not met; 1: filter condition is met |

## adc_intr_ctl
Interrupt enable controls.

adc_ctrl sends out only 1 interrupt, so this register controls
which internal sources are actually registered.

This register uses the same bit enumeration as [`ADC_INTR_STATUS`](#adc_intr_status)
- Offset: `0x74`
- Reset default: `0x0`
- Reset mask: `0x1ff`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 9, "attr": ["rw"], "rotate": 0}, {"bits": 23}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                        |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------------------------|
|  31:9  |        |         |        | Reserved                                                           |
|  8:0   |   rw   |   0x0   | EN     | 0: interrupt source is not enabled; 1: interrupt source is enabled |

## adc_intr_status
Debug cable internal status
- Offset: `0x78`
- Reset default: `0x0`
- Reset mask: `0x1ff`

### Fields

```wavejson
{"reg": [{"name": "filter_match", "bits": 8, "attr": ["rw1c"], "rotate": 0}, {"name": "oneshot", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 23}], "config": {"lanes": 1, "fontsize": 10, "vspace": 90}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                                |
|:------:|:------:|:-------:|:-------------|:-----------------------------------------------------------|
|  31:9  |        |         |              | Reserved                                                   |
|   8    |  rw1c  |   0x0   | oneshot      | 0: oneshot sample is not done ; 1: oneshot sample is done  |
|  7:0   |  rw1c  |   0x0   | filter_match | 0: filter condition is not met; 1: filter condition is met |


<!-- END CMDGEN -->
