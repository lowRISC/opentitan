# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/sysrst_ctrl/data/sysrst_ctrl.hjson -->
## Summary

| Name                                                              | Offset   |   Length | Description                                                                    |
|:------------------------------------------------------------------|:---------|---------:|:-------------------------------------------------------------------------------|
| sysrst_ctrl.[`INTR_STATE`](#intr_state)                           | 0x0      |        4 | Interrupt State Register                                                       |
| sysrst_ctrl.[`INTR_ENABLE`](#intr_enable)                         | 0x4      |        4 | Interrupt Enable Register                                                      |
| sysrst_ctrl.[`INTR_TEST`](#intr_test)                             | 0x8      |        4 | Interrupt Test Register                                                        |
| sysrst_ctrl.[`ALERT_TEST`](#alert_test)                           | 0xc      |        4 | Alert Test Register                                                            |
| sysrst_ctrl.[`REGWEN`](#regwen)                                   | 0x10     |        4 | Configuration write enable control register                                    |
| sysrst_ctrl.[`EC_RST_CTL`](#ec_rst_ctl)                           | 0x14     |        4 | EC reset control register                                                      |
| sysrst_ctrl.[`ULP_AC_DEBOUNCE_CTL`](#ulp_ac_debounce_ctl)         | 0x18     |        4 | Ultra low power AC debounce control register                                   |
| sysrst_ctrl.[`ULP_LID_DEBOUNCE_CTL`](#ulp_lid_debounce_ctl)       | 0x1c     |        4 | Ultra low power lid debounce control register                                  |
| sysrst_ctrl.[`ULP_PWRB_DEBOUNCE_CTL`](#ulp_pwrb_debounce_ctl)     | 0x20     |        4 | Ultra low power pwrb debounce control register                                 |
| sysrst_ctrl.[`ULP_CTL`](#ulp_ctl)                                 | 0x24     |        4 | Ultra low power control register                                               |
| sysrst_ctrl.[`ULP_STATUS`](#ulp_status)                           | 0x28     |        4 | Ultra low power status                                                         |
| sysrst_ctrl.[`WKUP_STATUS`](#wkup_status)                         | 0x2c     |        4 | wakeup status                                                                  |
| sysrst_ctrl.[`KEY_INVERT_CTL`](#key_invert_ctl)                   | 0x30     |        4 | configure key input output invert property                                     |
| sysrst_ctrl.[`PIN_ALLOWED_CTL`](#pin_allowed_ctl)                 | 0x34     |        4 | This register determines which override values are allowed for a given output. |
| sysrst_ctrl.[`PIN_OUT_CTL`](#pin_out_ctl)                         | 0x38     |        4 | Enables the override function for a specific pin.                              |
| sysrst_ctrl.[`PIN_OUT_VALUE`](#pin_out_value)                     | 0x3c     |        4 | Sets the pin override value. Note that only the values                         |
| sysrst_ctrl.[`PIN_IN_VALUE`](#pin_in_value)                       | 0x40     |        4 | For SW to read the sysrst_ctrl inputs like GPIO                                |
| sysrst_ctrl.[`KEY_INTR_CTL`](#key_intr_ctl)                       | 0x44     |        4 | Define the keys or inputs that can trigger the interrupt                       |
| sysrst_ctrl.[`KEY_INTR_DEBOUNCE_CTL`](#key_intr_debounce_ctl)     | 0x48     |        4 | Debounce timer control register for key-triggered interrupt                    |
| sysrst_ctrl.[`AUTO_BLOCK_DEBOUNCE_CTL`](#auto_block_debounce_ctl) | 0x4c     |        4 | Debounce timer control register for pwrb_in H2L transition                     |
| sysrst_ctrl.[`AUTO_BLOCK_OUT_CTL`](#auto_block_out_ctl)           | 0x50     |        4 | configure the key outputs to auto-override and their value                     |
| sysrst_ctrl.[`COM_PRE_SEL_CTL_0`](#com_pre_sel_ctl)               | 0x54     |        4 | To define the keys that define the pre-condition of the combo                  |
| sysrst_ctrl.[`COM_PRE_SEL_CTL_1`](#com_pre_sel_ctl)               | 0x58     |        4 | To define the keys that define the pre-condition of the combo                  |
| sysrst_ctrl.[`COM_PRE_SEL_CTL_2`](#com_pre_sel_ctl)               | 0x5c     |        4 | To define the keys that define the pre-condition of the combo                  |
| sysrst_ctrl.[`COM_PRE_SEL_CTL_3`](#com_pre_sel_ctl)               | 0x60     |        4 | To define the keys that define the pre-condition of the combo                  |
| sysrst_ctrl.[`COM_PRE_DET_CTL_0`](#com_pre_det_ctl)               | 0x64     |        4 | To define the duration that the combo pre-condition should be pressed          |
| sysrst_ctrl.[`COM_PRE_DET_CTL_1`](#com_pre_det_ctl)               | 0x68     |        4 | To define the duration that the combo pre-condition should be pressed          |
| sysrst_ctrl.[`COM_PRE_DET_CTL_2`](#com_pre_det_ctl)               | 0x6c     |        4 | To define the duration that the combo pre-condition should be pressed          |
| sysrst_ctrl.[`COM_PRE_DET_CTL_3`](#com_pre_det_ctl)               | 0x70     |        4 | To define the duration that the combo pre-condition should be pressed          |
| sysrst_ctrl.[`COM_SEL_CTL_0`](#com_sel_ctl)                       | 0x74     |        4 | To define the keys that trigger the combo                                      |
| sysrst_ctrl.[`COM_SEL_CTL_1`](#com_sel_ctl)                       | 0x78     |        4 | To define the keys that trigger the combo                                      |
| sysrst_ctrl.[`COM_SEL_CTL_2`](#com_sel_ctl)                       | 0x7c     |        4 | To define the keys that trigger the combo                                      |
| sysrst_ctrl.[`COM_SEL_CTL_3`](#com_sel_ctl)                       | 0x80     |        4 | To define the keys that trigger the combo                                      |
| sysrst_ctrl.[`COM_DET_CTL_0`](#com_det_ctl)                       | 0x84     |        4 | To define the duration that the combo should be pressed                        |
| sysrst_ctrl.[`COM_DET_CTL_1`](#com_det_ctl)                       | 0x88     |        4 | To define the duration that the combo should be pressed                        |
| sysrst_ctrl.[`COM_DET_CTL_2`](#com_det_ctl)                       | 0x8c     |        4 | To define the duration that the combo should be pressed                        |
| sysrst_ctrl.[`COM_DET_CTL_3`](#com_det_ctl)                       | 0x90     |        4 | To define the duration that the combo should be pressed                        |
| sysrst_ctrl.[`COM_OUT_CTL_0`](#com_out_ctl)                       | 0x94     |        4 | To define the actions once the combo is detected                               |
| sysrst_ctrl.[`COM_OUT_CTL_1`](#com_out_ctl)                       | 0x98     |        4 | To define the actions once the combo is detected                               |
| sysrst_ctrl.[`COM_OUT_CTL_2`](#com_out_ctl)                       | 0x9c     |        4 | To define the actions once the combo is detected                               |
| sysrst_ctrl.[`COM_OUT_CTL_3`](#com_out_ctl)                       | 0xa0     |        4 | To define the actions once the combo is detected                               |
| sysrst_ctrl.[`COMBO_INTR_STATUS`](#combo_intr_status)             | 0xa4     |        4 | Combo interrupt source. These registers will only be set if the                |
| sysrst_ctrl.[`KEY_INTR_STATUS`](#key_intr_status)                 | 0xa8     |        4 | key interrupt source                                                           |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "event_detected", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                                             |
|:------:|:------:|:-------:|:---------------|:--------------------------------------------------------|
|  31:1  |        |         |                | Reserved                                                |
|   0    |  rw1c  |   0x0   | event_detected | Common interrupt triggered by combo or keyboard events. |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "event_detected", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                                                              |
|:------:|:------:|:-------:|:---------------|:-------------------------------------------------------------------------|
|  31:1  |        |         |                | Reserved                                                                 |
|   0    |   rw   |   0x0   | event_detected | Enable interrupt when [`INTR_STATE.event_detected`](#intr_state) is set. |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "event_detected", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                                                       |
|:------:|:------:|:-------:|:---------------|:------------------------------------------------------------------|
|  31:1  |        |         |                | Reserved                                                          |
|   0    |   wo   |   0x0   | event_detected | Write 1 to force [`INTR_STATE.event_detected`](#intr_state) to 1. |

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

## REGWEN
Configuration write enable control register
- Offset: `0x10`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "write_en", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                                         |
|:------:|:------:|:-------:|:---------|:------------------------------------------------------------------------------------|
|  31:1  |        |         |          | Reserved                                                                            |
|   0    |  rw0c  |   0x1   | write_en | config write enable. 0: cfg is locked(not writable); 1: cfg is not locked(writable) |

## EC_RST_CTL
EC reset control register
- Offset: `0x14`
- Reset default: `0x7d0`
- Reset mask: `0xffff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "ec_rst_pulse", "bits": 16, "attr": ["rw"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                                                                                                                                                         |
|:------:|:------:|:-------:|:-------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:16  |        |         |              | Reserved                                                                                                                                                                            |
|  15:0  |   rw   |  0x7d0  | ec_rst_pulse | Configure the debounce timer in number of clock cycles. Each step is 5 us for a 200 kHz clock. The signal must exceed the debounce time by at least one clock cycle to be detected. |

## ULP_AC_DEBOUNCE_CTL
Ultra low power AC debounce control register
- Offset: `0x18`
- Reset default: `0x1f40`
- Reset mask: `0xffff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "ulp_ac_debounce_timer", "bits": 16, "attr": ["rw"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                                                                                                                                                                          |
|:------:|:------:|:-------:|:----------------------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:16  |        |         |                       | Reserved                                                                                                                                                                                             |
|  15:0  |   rw   | 0x1f40  | ulp_ac_debounce_timer | Configure the debounce timer for the AC input in number of clock cycles. Each step is 5 us for a 200 kHz clock. The signal must exceed the debounce time by at least one clock cycle to be detected. |

## ULP_LID_DEBOUNCE_CTL
Ultra low power lid debounce control register
- Offset: `0x1c`
- Reset default: `0x1f40`
- Reset mask: `0xffff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "ulp_lid_debounce_timer", "bits": 16, "attr": ["rw"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                   | Description                                                                                                                                                                                     |
|:------:|:------:|:-------:|:-----------------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:16  |        |         |                        | Reserved                                                                                                                                                                                        |
|  15:0  |   rw   | 0x1f40  | ulp_lid_debounce_timer | Configure the debounce timer for the lid in number of clock cycles. Each step is 5 us for a 200 kHz clock. The signal must exceed the debounce time by at least one clock cycle to be detected. |

## ULP_PWRB_DEBOUNCE_CTL
Ultra low power pwrb debounce control register
- Offset: `0x20`
- Reset default: `0x1f40`
- Reset mask: `0xffff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "ulp_pwrb_debounce_timer", "bits": 16, "attr": ["rw"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                    | Description                                                                                                                                                                                              |
|:------:|:------:|:-------:|:------------------------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:16  |        |         |                         | Reserved                                                                                                                                                                                                 |
|  15:0  |   rw   | 0x1f40  | ulp_pwrb_debounce_timer | Configure the debounce timer for the power button in number of clock cycles. Each step is 5 us for a 200 kHz clock. The signal must exceed the debounce time by at least one clock cycle to be detected. |

## ULP_CTL
Ultra low power control register
- Offset: `0x24`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "ulp_enable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                                       |
|:------:|:------:|:-------:|:-----------|:----------------------------------------------------------------------------------|
|  31:1  |        |         |            | Reserved                                                                          |
|   0    |   rw   |   0x0   | ulp_enable | 0: disable ULP wakeup feature and reset the ULP FSM; 1: enable ULP wakeup feature |

## ULP_STATUS
Ultra low power status
- Offset: `0x28`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "ulp_wakeup", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                 |
|:------:|:------:|:-------:|:-----------|:------------------------------------------------------------|
|  31:1  |        |         |            | Reserved                                                    |
|   0    |  rw1c  |   0x0   | ulp_wakeup | 0: ULP wakeup not detected; 1: ULP wakeup event is detected |

## WKUP_STATUS
wakeup status
- Offset: `0x2c`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "wakeup_sts", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                               |
|:------:|:------:|:-------:|:-----------|:----------------------------------------------------------|
|  31:1  |        |         |            | Reserved                                                  |
|   0    |  rw1c  |   0x0   | wakeup_sts | 0: wakeup event not detected; 1: wakeup event is detected |

## KEY_INVERT_CTL
configure key input output invert property
- Offset: `0x30`
- Reset default: `0x0`
- Reset mask: `0xfff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "key0_in", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key0_out", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key1_in", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key1_out", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key2_in", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key2_out", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "pwrb_in", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "pwrb_out", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ac_present", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "bat_disable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "lid_open", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "z3_wakeup", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 20}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                |
|:------:|:------:|:-------:|:------------|:---------------------------|
| 31:12  |        |         |             | Reserved                   |
|   11   |   rw   |   0x0   | z3_wakeup   | 0: don't invert; 1: invert |
|   10   |   rw   |   0x0   | lid_open    | 0: don't invert; 1: invert |
|   9    |   rw   |   0x0   | bat_disable | 0: don't invert; 1: invert |
|   8    |   rw   |   0x0   | ac_present  | 0: don't invert; 1: invert |
|   7    |   rw   |   0x0   | pwrb_out    | 0: don't invert; 1: invert |
|   6    |   rw   |   0x0   | pwrb_in     | 0: don't invert; 1: invert |
|   5    |   rw   |   0x0   | key2_out    | 0: don't invert; 1: invert |
|   4    |   rw   |   0x0   | key2_in     | 0: don't invert; 1: invert |
|   3    |   rw   |   0x0   | key1_out    | 0: don't invert; 1: invert |
|   2    |   rw   |   0x0   | key1_in     | 0: don't invert; 1: invert |
|   1    |   rw   |   0x0   | key0_out    | 0: don't invert; 1: invert |
|   0    |   rw   |   0x0   | key0_in     | 0: don't invert; 1: invert |

## PIN_ALLOWED_CTL
This register determines which override values are allowed for a given output.
If an override value programmed via [`PIN_OUT_VALUE`](#pin_out_value) is not configured as an allowed value,
it will not have any effect.
- Offset: `0x34`
- Reset default: `0x82`
- Reset mask: `0xffff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "bat_disable_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ec_rst_l_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "pwrb_out_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key0_out_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key1_out_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key2_out_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "z3_wakeup_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "flash_wp_l_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "bat_disable_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ec_rst_l_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "pwrb_out_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key0_out_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key1_out_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key2_out_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "z3_wakeup_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "flash_wp_l_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                |
|:------:|:------:|:-------:|:--------------|:---------------------------|
| 31:16  |        |         |               | Reserved                   |
|   15   |   rw   |   0x0   | flash_wp_l_1  | 0: not allowed; 1: allowed |
|   14   |   rw   |   0x0   | z3_wakeup_1   | 0: not allowed; 1: allowed |
|   13   |   rw   |   0x0   | key2_out_1    | 0: not allowed; 1: allowed |
|   12   |   rw   |   0x0   | key1_out_1    | 0: not allowed; 1: allowed |
|   11   |   rw   |   0x0   | key0_out_1    | 0: not allowed; 1: allowed |
|   10   |   rw   |   0x0   | pwrb_out_1    | 0: not allowed; 1: allowed |
|   9    |   rw   |   0x0   | ec_rst_l_1    | 0: not allowed; 1: allowed |
|   8    |   rw   |   0x0   | bat_disable_1 | 0: not allowed; 1: allowed |
|   7    |   rw   |   0x1   | flash_wp_l_0  | 0: not allowed; 1: allowed |
|   6    |   rw   |   0x0   | z3_wakeup_0   | 0: not allowed; 1: allowed |
|   5    |   rw   |   0x0   | key2_out_0    | 0: not allowed; 1: allowed |
|   4    |   rw   |   0x0   | key1_out_0    | 0: not allowed; 1: allowed |
|   3    |   rw   |   0x0   | key0_out_0    | 0: not allowed; 1: allowed |
|   2    |   rw   |   0x0   | pwrb_out_0    | 0: not allowed; 1: allowed |
|   1    |   rw   |   0x1   | ec_rst_l_0    | 0: not allowed; 1: allowed |
|   0    |   rw   |   0x0   | bat_disable_0 | 0: not allowed; 1: allowed |

## PIN_OUT_CTL
Enables the override function for a specific pin.
- Offset: `0x38`
- Reset default: `0x82`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "bat_disable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ec_rst_l", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "pwrb_out", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key0_out", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key1_out", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key2_out", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "z3_wakeup", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "flash_wp_l", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                             |
|:------:|:------:|:-------:|:------------|:----------------------------------------|
|  31:8  |        |         |             | Reserved                                |
|   7    |   rw   |   0x1   | flash_wp_l  | 0: disable override; 1: enable override |
|   6    |   rw   |   0x0   | z3_wakeup   | 0: disable override; 1: enable override |
|   5    |   rw   |   0x0   | key2_out    | 0: disable override; 1: enable override |
|   4    |   rw   |   0x0   | key1_out    | 0: disable override; 1: enable override |
|   3    |   rw   |   0x0   | key0_out    | 0: disable override; 1: enable override |
|   2    |   rw   |   0x0   | pwrb_out    | 0: disable override; 1: enable override |
|   1    |   rw   |   0x1   | ec_rst_l    | 0: disable override; 1: enable override |
|   0    |   rw   |   0x0   | bat_disable | 0: disable override; 1: enable override |

## PIN_OUT_VALUE
Sets the pin override value. Note that only the values
configured as 'allowed' in [`PIN_ALLOWED_CTL`](#pin_allowed_ctl) will have
an effect. Otherwise the pin value will not be overridden.
- Offset: `0x3c`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "bat_disable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ec_rst_l", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "pwrb_out", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key0_out", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key1_out", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key2_out", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "z3_wakeup", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "flash_wp_l", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                            |
|:------:|:------:|:-------:|:------------|:---------------------------------------|
|  31:8  |        |         |             | Reserved                               |
|   7    |   rw   |   0x0   | flash_wp_l  | 0: override to 1b0; 1: override to 1b1 |
|   6    |   rw   |   0x0   | z3_wakeup   | 0: override to 1b0; 1: override to 1b1 |
|   5    |   rw   |   0x0   | key2_out    | 0: override to 1b0; 1: override to 1b1 |
|   4    |   rw   |   0x0   | key1_out    | 0: override to 1b0; 1: override to 1b1 |
|   3    |   rw   |   0x0   | key0_out    | 0: override to 1b0; 1: override to 1b1 |
|   2    |   rw   |   0x0   | pwrb_out    | 0: override to 1b0; 1: override to 1b1 |
|   1    |   rw   |   0x0   | ec_rst_l    | 0: override to 1b0; 1: override to 1b1 |
|   0    |   rw   |   0x0   | bat_disable | 0: override to 1b0; 1: override to 1b1 |

## PIN_IN_VALUE
For SW to read the sysrst_ctrl inputs like GPIO
- Offset: `0x40`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "pwrb_in", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "key0_in", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "key1_in", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "key2_in", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "lid_open", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ac_present", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ec_rst_l", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "flash_wp_l", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                   |
|:------:|:------:|:-------:|:-----------|:----------------------------------------------|
|  31:8  |        |         |            | Reserved                                      |
|   7    |   ro   |   0x0   | flash_wp_l | raw flash_wp_l value; before the invert logic |
|   6    |   ro   |   0x0   | ec_rst_l   | raw ec_rst_l value; before the invert logic   |
|   5    |   ro   |   0x0   | ac_present | raw ac_present value; before the invert logic |
|   4    |   ro   |   0x0   | lid_open   | raw lid_open value; before the invert logic   |
|   3    |   ro   |   0x0   | key2_in    | raw key2_in value; before the invert logic    |
|   2    |   ro   |   0x0   | key1_in    | raw key1_in value; before the invert logic    |
|   1    |   ro   |   0x0   | key0_in    | raw key0_in value; before the invert logic    |
|   0    |   ro   |   0x0   | pwrb_in    | raw pwrb_in value; before the invert logic    |

## KEY_INTR_CTL
Define the keys or inputs that can trigger the interrupt
- Offset: `0x44`
- Reset default: `0x0`
- Reset mask: `0x3fff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "pwrb_in_H2L", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key0_in_H2L", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key1_in_H2L", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key2_in_H2L", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ac_present_H2L", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ec_rst_l_H2L", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "flash_wp_l_H2L", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "pwrb_in_L2H", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key0_in_L2H", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key1_in_L2H", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key2_in_L2H", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ac_present_L2H", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ec_rst_l_L2H", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "flash_wp_l_L2H", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 18}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description           |
|:------:|:------:|:-------:|:---------------|:----------------------|
| 31:14  |        |         |                | Reserved              |
|   13   |   rw   |   0x0   | flash_wp_l_L2H | 0: disable, 1: enable |
|   12   |   rw   |   0x0   | ec_rst_l_L2H   | 0: disable, 1: enable |
|   11   |   rw   |   0x0   | ac_present_L2H | 0: disable, 1: enable |
|   10   |   rw   |   0x0   | key2_in_L2H    | 0: disable, 1: enable |
|   9    |   rw   |   0x0   | key1_in_L2H    | 0: disable, 1: enable |
|   8    |   rw   |   0x0   | key0_in_L2H    | 0: disable, 1: enable |
|   7    |   rw   |   0x0   | pwrb_in_L2H    | 0: disable, 1: enable |
|   6    |   rw   |   0x0   | flash_wp_l_H2L | 0: disable, 1: enable |
|   5    |   rw   |   0x0   | ec_rst_l_H2L   | 0: disable, 1: enable |
|   4    |   rw   |   0x0   | ac_present_H2L | 0: disable, 1: enable |
|   3    |   rw   |   0x0   | key2_in_H2L    | 0: disable, 1: enable |
|   2    |   rw   |   0x0   | key1_in_H2L    | 0: disable, 1: enable |
|   1    |   rw   |   0x0   | key0_in_H2L    | 0: disable, 1: enable |
|   0    |   rw   |   0x0   | pwrb_in_H2L    | 0: disable, 1: enable |

## KEY_INTR_DEBOUNCE_CTL
Debounce timer control register for key-triggered interrupt
- Offset: `0x48`
- Reset default: `0x7d0`
- Reset mask: `0xffff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "debounce_timer", "bits": 16, "attr": ["rw"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                                                                                                                                                                                                     |
|:------:|:------:|:-------:|:---------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:16  |        |         |                | Reserved                                                                                                                                                                                                        |
|  15:0  |   rw   |  0x7d0  | debounce_timer | Define the timer value so that the key or input is not oscillating in clock cycles. Each step is 5 us for a 200 kHz clock. The signal must exceed the debounce time by at least one clock cycle to be detected. |

## AUTO_BLOCK_DEBOUNCE_CTL
Debounce timer control register for pwrb_in H2L transition
- Offset: `0x4c`
- Reset default: `0x7d0`
- Reset mask: `0x1ffff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "debounce_timer", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "auto_block_enable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 15}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                                                                                                                                                                                                |
|:------:|:------:|:-------:|:------------------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:17  |        |         |                   | Reserved                                                                                                                                                                                                   |
|   16   |   rw   |   0x0   | auto_block_enable | 0: disable, 1: enable                                                                                                                                                                                      |
|  15:0  |   rw   |  0x7d0  | debounce_timer    | Define the timer value so that the pwrb_in is not oscillating in clock cycles. Each step is 5 us for a 200 kHz clock. The signal must exceed the debounce time by at least one clock cycle to be detected. |

## AUTO_BLOCK_OUT_CTL
configure the key outputs to auto-override and their value
- Offset: `0x50`
- Reset default: `0x0`
- Reset mask: `0x77`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "key0_out_sel", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key1_out_sel", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key2_out_sel", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 1}, {"name": "key0_out_value", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key1_out_value", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key2_out_value", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 25}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                                 |
|:------:|:------:|:-------:|:---------------|:--------------------------------------------|
|  31:7  |        |         |                | Reserved                                    |
|   6    |   rw   |   0x0   | key2_out_value | 0: override to 1'b0; 1: override to 1'b1    |
|   5    |   rw   |   0x0   | key1_out_value | 0: override to 1'b0; 1: override to 1'b1    |
|   4    |   rw   |   0x0   | key0_out_value | 0: override to 1'b0; 1: override to 1'b1    |
|   3    |        |         |                | Reserved                                    |
|   2    |   rw   |   0x0   | key2_out_sel   | 0: disable auto-block; 1: enable auto-block |
|   1    |   rw   |   0x0   | key1_out_sel   | 0: disable auto-block; 1: enable auto-block |
|   0    |   rw   |   0x0   | key0_out_sel   | 0: disable auto-block; 1: enable auto-block |

## COM_PRE_SEL_CTL
To define the keys that define the pre-condition of the combo
[0]: key0_in_sel
[1]: key1_in_sel
[2]: key2_in_sel
[3]: pwrb_in_sel
[4]: ac_present_sel
HW will start matching the combo as defined by [`COM_SEL_CTL`](#com_sel_ctl) if this precondition is fulfilled.

If no keys are configured for the pre-condition, the pre-condition always evaluates to true.

The debounce timing is defined via [`KEY_INTR_DEBOUNCE_CTL`](#key_intr_debounce_ctl) whereas the pre-condition pressed timing is defined via [`COM_PRE_DET_CTL.`](#com_pre_det_ctl)
- Reset default: `0x0`
- Reset mask: `0x1f`

### Instances

| Name              | Offset   |
|:------------------|:---------|
| COM_PRE_SEL_CTL_0 | 0x54     |
| COM_PRE_SEL_CTL_1 | 0x58     |
| COM_PRE_SEL_CTL_2 | 0x5c     |
| COM_PRE_SEL_CTL_3 | 0x60     |


### Fields

```wavejson
{"reg": [{"name": "key0_in_sel", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key1_in_sel", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key2_in_sel", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "pwrb_in_sel", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ac_present_sel", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description           |
|:------:|:------:|:-------:|:---------------|:----------------------|
|  31:5  |        |         |                | Reserved              |
|   4    |   rw   |   0x0   | ac_present_sel | 0: disable, 1: enable |
|   3    |   rw   |   0x0   | pwrb_in_sel    | 0: disable, 1: enable |
|   2    |   rw   |   0x0   | key2_in_sel    | 0: disable, 1: enable |
|   1    |   rw   |   0x0   | key1_in_sel    | 0: disable, 1: enable |
|   0    |   rw   |   0x0   | key0_in_sel    | 0: disable, 1: enable |

## COM_PRE_DET_CTL
To define the duration that the combo pre-condition should be pressed
0-60s, each step is 5us(200KHz clock)
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name              | Offset   |
|:------------------|:---------|
| COM_PRE_DET_CTL_0 | 0x64     |
| COM_PRE_DET_CTL_1 | 0x68     |
| COM_PRE_DET_CTL_2 | 0x6c     |
| COM_PRE_DET_CTL_3 | 0x70     |


### Fields

```wavejson
{"reg": [{"name": "precondition_timer", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                           |
|:------:|:------:|:-------:|:-------------------|:--------------------------------------|
|  31:0  |   rw   |   0x0   | precondition_timer | 0-60s, each step is 5us(200KHz clock) |

## COM_SEL_CTL
To define the keys that trigger the combo
[0]: key0_in_sel
[1]: key1_in_sel
[2]: key2_in_sel
[3]: pwrb_in_sel
[4]: ac_present_sel
HW will detect H2L transition in the combo use case.

Optionally, a pre-condition can be configured for the combo detection via [`COM_PRE_SEL_CTL.`](#com_pre_sel_ctl)

If no keys are configured for the combo, the combo detection is disabled.

The debounce timing is defined via [`KEY_INTR_DEBOUNCE_CTL`](#key_intr_debounce_ctl) whereas the key-pressed timing is defined via [`COM_DET_CTL.`](#com_det_ctl)
- Reset default: `0x0`
- Reset mask: `0x1f`

### Instances

| Name          | Offset   |
|:--------------|:---------|
| COM_SEL_CTL_0 | 0x74     |
| COM_SEL_CTL_1 | 0x78     |
| COM_SEL_CTL_2 | 0x7c     |
| COM_SEL_CTL_3 | 0x80     |


### Fields

```wavejson
{"reg": [{"name": "key0_in_sel", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key1_in_sel", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key2_in_sel", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "pwrb_in_sel", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ac_present_sel", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description           |
|:------:|:------:|:-------:|:---------------|:----------------------|
|  31:5  |        |         |                | Reserved              |
|   4    |   rw   |   0x0   | ac_present_sel | 0: disable, 1: enable |
|   3    |   rw   |   0x0   | pwrb_in_sel    | 0: disable, 1: enable |
|   2    |   rw   |   0x0   | key2_in_sel    | 0: disable, 1: enable |
|   1    |   rw   |   0x0   | key1_in_sel    | 0: disable, 1: enable |
|   0    |   rw   |   0x0   | key0_in_sel    | 0: disable, 1: enable |

## COM_DET_CTL
To define the duration that the combo should be pressed
0-60s, each step is 5us(200KHz clock)
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name          | Offset   |
|:--------------|:---------|
| COM_DET_CTL_0 | 0x84     |
| COM_DET_CTL_1 | 0x88     |
| COM_DET_CTL_2 | 0x8c     |
| COM_DET_CTL_3 | 0x90     |


### Fields

```wavejson
{"reg": [{"name": "detection_timer", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name            | Description                           |
|:------:|:------:|:-------:|:----------------|:--------------------------------------|
|  31:0  |   rw   |   0x0   | detection_timer | 0-60s, each step is 5us(200KHz clock) |

## COM_OUT_CTL
To define the actions once the combo is detected
[0]: bat_disable
[1]: interrupt (to OpenTitan processor)
[2]: ec_rst (for Embedded Controller)
[3]: rst_req (to OpenTitan reset manager)
- Reset default: `0x0`
- Reset mask: `0xf`

### Instances

| Name          | Offset   |
|:--------------|:---------|
| COM_OUT_CTL_0 | 0x94     |
| COM_OUT_CTL_1 | 0x98     |
| COM_OUT_CTL_2 | 0x9c     |
| COM_OUT_CTL_3 | 0xa0     |


### Fields

```wavejson
{"reg": [{"name": "bat_disable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "interrupt", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ec_rst", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rst_req", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description           |
|:------:|:------:|:-------:|:------------|:----------------------|
|  31:4  |        |         |             | Reserved              |
|   3    |   rw   |   0x0   | rst_req     | 0: disable, 1: enable |
|   2    |   rw   |   0x0   | ec_rst      | 0: disable, 1: enable |
|   1    |   rw   |   0x0   | interrupt   | 0: disable, 1: enable |
|   0    |   rw   |   0x0   | bat_disable | 0: disable, 1: enable |

## COMBO_INTR_STATUS
Combo interrupt source. These registers will only be set if the
interrupt action is configured in the corresponding [`COM_OUT_CTL`](#com_out_ctl) register.
- Offset: `0xa4`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "combo0_H2L", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "combo1_H2L", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "combo2_H2L", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "combo3_H2L", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                           |
|:------:|:------:|:-------:|:-----------|:--------------------------------------|
|  31:4  |        |         |            | Reserved                              |
|   3    |  rw1c  |   0x0   | combo3_H2L | 0: case not detected;1: case detected |
|   2    |  rw1c  |   0x0   | combo2_H2L | 0: case not detected;1: case detected |
|   1    |  rw1c  |   0x0   | combo1_H2L | 0: case not detected;1: case detected |
|   0    |  rw1c  |   0x0   | combo0_H2L | 0: case not detected;1: case detected |

## KEY_INTR_STATUS
key interrupt source
- Offset: `0xa8`
- Reset default: `0x0`
- Reset mask: `0x3fff`

### Fields

```wavejson
{"reg": [{"name": "pwrb_H2L", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "key0_in_H2L", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "key1_in_H2L", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "key2_in_H2L", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "ac_present_H2L", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "ec_rst_l_H2L", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "flash_wp_l_H2L", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "pwrb_L2H", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "key0_in_L2H", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "key1_in_L2H", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "key2_in_L2H", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "ac_present_L2H", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "ec_rst_l_L2H", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "flash_wp_l_L2H", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 18}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                           |
|:------:|:------:|:-------:|:---------------|:--------------------------------------|
| 31:14  |        |         |                | Reserved                              |
|   13   |  rw1c  |   0x0   | flash_wp_l_L2H | 0: case not detected;1: case detected |
|   12   |  rw1c  |   0x0   | ec_rst_l_L2H   | 0: case not detected;1: case detected |
|   11   |  rw1c  |   0x0   | ac_present_L2H | 0: case not detected;1: case detected |
|   10   |  rw1c  |   0x0   | key2_in_L2H    | 0: case not detected;1: case detected |
|   9    |  rw1c  |   0x0   | key1_in_L2H    | 0: case not detected;1: case detected |
|   8    |  rw1c  |   0x0   | key0_in_L2H    | 0: case not detected;1: case detected |
|   7    |  rw1c  |   0x0   | pwrb_L2H       | 0: case not detected;1: case detected |
|   6    |  rw1c  |   0x0   | flash_wp_l_H2L | 0: case not detected;1: case detected |
|   5    |  rw1c  |   0x0   | ec_rst_l_H2L   | 0: case not detected;1: case detected |
|   4    |  rw1c  |   0x0   | ac_present_H2L | 0: case not detected;1: case detected |
|   3    |  rw1c  |   0x0   | key2_in_H2L    | 0: case not detected;1: case detected |
|   2    |  rw1c  |   0x0   | key1_in_H2L    | 0: case not detected;1: case detected |
|   1    |  rw1c  |   0x0   | key0_in_H2L    | 0: case not detected;1: case detected |
|   0    |  rw1c  |   0x0   | pwrb_H2L       | 0: case not detected;1: case detected |


<!-- END CMDGEN -->
