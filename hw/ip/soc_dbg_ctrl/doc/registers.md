# Registers

The RoT shall define three registers and drive the debug policy bus from that.
These registers are updated by the RoT FW and are distributed by the debug policy bus to all consumers, e.g., HW TAPs in the system.
Depending on the configured debug category, a consumer might accept the debug command or not (if it is not part of the selected debug category).

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/soc_dbg_ctrl/data/soc_dbg_ctrl.hjson -->
## Summary of the **`core`** interface's registers

| Name                                                                                   | Offset   |   Length | Description                                                                                              |
|:---------------------------------------------------------------------------------------|:---------|---------:|:---------------------------------------------------------------------------------------------------------|
| soc_dbg_ctrl.[`ALERT_TEST`](#alert_test)                                               | 0x0      |        4 | Alert Test Register                                                                                      |
| soc_dbg_ctrl.[`DEBUG_POLICY_VALID_SHADOWED`](#debug_policy_valid_shadowed)             | 0x4      |        4 | Debug Policy Valid.                                                                                      |
| soc_dbg_ctrl.[`DEBUG_POLICY_CATEGORY_SHADOWED`](#debug_policy_category_shadowed)       | 0x8      |        4 | Debug Policy category                                                                                    |
| soc_dbg_ctrl.[`DEBUG_POLICY_RELOCKED`](#debug_policy_relocked)                         | 0xc      |        4 | Debug Policy relocked                                                                                    |
| soc_dbg_ctrl.[`TRACE_DEBUG_POLICY_CATEGORY`](#trace_debug_policy_category)             | 0x10     |        4 | Trace register to observe the debug category that is either determined by hardware or software.          |
| soc_dbg_ctrl.[`TRACE_DEBUG_POLICY_VALID_RELOCKED`](#trace_debug_policy_valid_relocked) | 0x14     |        4 | Trace register to observe the valid or relocked state that is either determined by hardware or software. |
| soc_dbg_ctrl.[`STATUS`](#status)                                                       | 0x18     |        4 | Debug Status Register                                                                                    |

## ALERT_TEST
Alert Test Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "fatal_fault", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "recov_ctrl_update_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                      |
|:------:|:------:|:-------:|:----------------------|:-------------------------------------------------|
|  31:2  |        |         |                       | Reserved                                         |
|   1    |   wo   |   0x0   | recov_ctrl_update_err | Write 1 to trigger one alert event of this kind. |
|   0    |   wo   |   0x0   | fatal_fault           | Write 1 to trigger one alert event of this kind. |

## DEBUG_POLICY_VALID_SHADOWED
Debug Policy Valid.
Once valid is set to Mubi4::True, the debug policy cannot be written anymore.
- Offset: `0x4`
- Reset default: `0x9`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "debug_policy_valid", "bits": 4, "attr": ["rw1s"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                          |
|:------:|:------:|:-------:|:-------------------|:-------------------------------------|
|  31:4  |        |         |                    | Reserved                             |
|  3:0   |  rw1s  |   0x9   | debug_policy_valid | The valid state of the debug policy. |

## DEBUG_POLICY_CATEGORY_SHADOWED
Debug Policy category
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x7f`

### Fields

```wavejson
{"reg": [{"name": "debug_policy_category", "bits": 7, "attr": ["rw"], "rotate": -90}, {"bits": 25}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                                                                                                                                     |
|:------:|:------:|:-------:|:----------------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:7  |        |         |                       | Reserved                                                                                                                                                        |
|  6:0   |   rw   |   0x0   | debug_policy_category | Debug Policy Control Setting. Indicates the current debug authorization policy that is distributed to the rest of the SoC to govern debug / DFT feature unlock. |

## DEBUG_POLICY_RELOCKED
Debug Policy relocked
- Offset: `0xc`
- Reset default: `0x9`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "debug_policy_relocked", "bits": 4, "attr": ["rw"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description         |
|:------:|:------:|:-------:|:----------------------|:--------------------|
|  31:4  |        |         |                       | Reserved            |
|  3:0   |   rw   |   0x9   | debug_policy_relocked | The relocked state. |

## TRACE_DEBUG_POLICY_CATEGORY
Trace register to observe the debug category that is either determined by hardware or software.
- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0x7f`

### Fields

```wavejson
{"reg": [{"name": "category", "bits": 7, "attr": ["ro"], "rotate": 0}, {"bits": 25}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                          |
|:------:|:------:|:-------:|:---------|:-----------------------------------------------------|
|  31:7  |        |         |          | Reserved                                             |
|  6:0   |   ro   |   0x0   | category | The debug policy determined by hardware or software. |

## TRACE_DEBUG_POLICY_VALID_RELOCKED
Trace register to observe the valid or relocked state that is either determined by hardware or software.
- Offset: `0x14`
- Reset default: `0x99`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "valid", "bits": 4, "attr": ["ro"], "rotate": 0}, {"name": "relocked", "bits": 4, "attr": ["ro"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                            |
|:------:|:------:|:-------:|:---------|:-------------------------------------------------------|
|  31:8  |        |         |          | Reserved                                               |
|  7:4   |   ro   |   0x9   | relocked | The relocked state determined by hardware or software. |
|  3:0   |   ro   |   0x9   | valid    | The valid state determined by hardware or software.    |

## STATUS
Debug Status Register
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0xf1`

### Fields

```wavejson
{"reg": [{"name": "auth_debug_intent_set", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 3}, {"name": "auth_window_open", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "auth_window_closed", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "auth_unlock_success", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "auth_unlock_failed", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                                                                                                                                                                                                                        |
|:------:|:------:|:-------:|:----------------------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:8  |        |         |                       | Reserved                                                                                                                                                                                                                                           |
|   7    |   rw   |   0x0   | auth_unlock_failed    | Status bit indicating whether the unlock protocol resulted in unlock failure at requested level.                                                                                                                                                   |
|   6    |   rw   |   0x0   | auth_unlock_success   | Status bit indicating whether the unlock protocol resulted in a successful unlock at requested level.                                                                                                                                              |
|   5    |   rw   |   0x0   | auth_window_closed    | Status bit that indicates that SoC reset sequence is unpaused SoC shall continue to boot and the debug authorization exchange cannot take place anymore until next reset. Note that the rest of the SoC reset sequence is triggered by the OT RoT. |
|   4    |   rw   |   0x0   | auth_window_open      | Status bit that tells whether debug authorization exchange can take place. This bit is set when auth_debug_intent_set is 1 and SoC reset sequence is paused to enable debug authorization exchange.                                                |
|  3:1   |        |         |                       | Reserved                                                                                                                                                                                                                                           |
|   0    |   rw   |   0x0   | auth_debug_intent_set | Status bit indicating whether the debug intent hardware strap was set. If set, SoC will be treated as under debug and authorized debug can be enabled to unlock the SoC at desired debug unlock level.                                             |

## Summary of the **`jtag`** interface's registers

| Name                                                                                             | Offset   |   Length | Description                                                                                              |
|:-------------------------------------------------------------------------------------------------|:---------|---------:|:---------------------------------------------------------------------------------------------------------|
| soc_dbg_ctrl.[`JTAG_TRACE_DEBUG_POLICY_CATEGORY`](#jtag_trace_debug_policy_category)             | 0x0      |        4 | Trace register to observe the debug category that is either determined by hardware or software.          |
| soc_dbg_ctrl.[`JTAG_TRACE_DEBUG_POLICY_VALID_RELOCKED`](#jtag_trace_debug_policy_valid_relocked) | 0x4      |        4 | Trace register to observe the valid or relocked state that is either determined by hardware or software. |
| soc_dbg_ctrl.[`JTAG_CONTROL`](#jtag_control)                                                     | 0x8      |        4 | JTAG control register to interact with the boot flow.                                                    |
| soc_dbg_ctrl.[`JTAG_STATUS`](#jtag_status)                                                       | 0xc      |        4 | Debug Status Register                                                                                    |
| soc_dbg_ctrl.[`JTAG_BOOT_STATUS`](#jtag_boot_status)                                             | 0x10     |        4 | Debug boot status register that tells important boot state information.                                  |
| soc_dbg_ctrl.[`JTAG_TRACE_SOC_DBG_STATE`](#jtag_trace_soc_dbg_state)                             | 0x14     |        4 | Tells the current debug state coming from OTP.                                                           |

## JTAG_TRACE_DEBUG_POLICY_CATEGORY
Trace register to observe the debug category that is either determined by hardware or software.
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x7f`

### Fields

```wavejson
{"reg": [{"name": "category", "bits": 7, "attr": ["ro"], "rotate": 0}, {"bits": 25}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                          |
|:------:|:------:|:-------:|:---------|:-----------------------------------------------------|
|  31:7  |        |         |          | Reserved                                             |
|  6:0   |   ro   |   0x0   | category | The debug policy determined by hardware or software. |

## JTAG_TRACE_DEBUG_POLICY_VALID_RELOCKED
Trace register to observe the valid or relocked state that is either determined by hardware or software.
- Offset: `0x4`
- Reset default: `0x99`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "valid", "bits": 4, "attr": ["ro"], "rotate": 0}, {"name": "relocked", "bits": 4, "attr": ["ro"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                            |
|:------:|:------:|:-------:|:---------|:-------------------------------------------------------|
|  31:8  |        |         |          | Reserved                                               |
|  7:4   |   ro   |   0x9   | relocked | The relocked state determined by hardware or software. |
|  3:0   |   ro   |   0x9   | valid    | The valid state determined by hardware or software.    |

## JTAG_CONTROL
JTAG control register to interact with the boot flow.
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "boot_continue", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                                                                                                   |
|:------:|:------:|:-------:|:--------------|:----------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |               | Reserved                                                                                                                                      |
|   0    |   rw   |   0x0   | boot_continue | JTAG bit to stop or continue the boot flow of Ibex. 1'b0: Stop and halt boot flow. 1'b1: Continue with the boot flow and let Ibex fetch code. |

## JTAG_STATUS
Debug Status Register
- Offset: `0xc`
- Reset default: `0x0`
- Reset mask: `0xf1`

### Fields

```wavejson
{"reg": [{"name": "auth_debug_intent_set", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 3}, {"name": "auth_window_open", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "auth_window_closed", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "auth_unlock_success", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "auth_unlock_failed", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                                                                                                                                                                                                                         |
|:------:|:------:|:-------:|:----------------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:8  |        |         |                       | Reserved                                                                                                                                                                                                                                            |
|   7    |   ro   |   0x0   | auth_unlock_failed    | Status bit indicating whether the unlock protocol resulted in unlock failure at requested level                                                                                                                                                     |
|   6    |   ro   |   0x0   | auth_unlock_success   | Status bit indicating whether the unlock protocol resulted in a successful unlock at requested level                                                                                                                                                |
|   5    |   ro   |   0x0   | auth_window_closed    | Status bit that indicates that SoC reset sequence is unpaused, SoC shall continue to boot and the debug authorization exchange cannot take place anymore until next reset. Note that the rest of the SoC reset sequence is triggered by the OT RoT" |
|   4    |   ro   |   0x0   | auth_window_open      | Status bit that tells whether debug authorization exchange can take place. This bit is set when auth_debug_intent_set is 1 and SoC reset sequence is paused to enable debug authorization exchange.                                                 |
|  3:1   |        |         |                       | Reserved                                                                                                                                                                                                                                            |
|   0    |   ro   |   0x0   | auth_debug_intent_set | Status bit indicating whether the debug intent hardware strap was set. If set, SoC will be treated as under debug and authorized debug can be enabled to unlock the SoC at desired debug unlock level.                                              |

## JTAG_BOOT_STATUS
Debug boot status register that tells important boot state information.
Note that this information is reflected only if the hw_dft_en signal is true.
- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0x1ffff`

### Fields

```wavejson
{"reg": [{"name": "main_clk_status", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "io_clk_status", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "otp_done", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "lc_done", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "cpu_fetch_en", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "halt_fsm_state", "bits": 6, "attr": ["ro"], "rotate": -90}, {"name": "boot_greenlight_done", "bits": 3, "attr": ["ro"], "rotate": -90}, {"name": "boot_greenlight_good", "bits": 3, "attr": ["ro"], "rotate": -90}, {"bits": 15}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                                                                                                                                                                       |
|:------:|:------:|:-------:|:---------------------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:17  |        |         |                      | Reserved                                                                                                                                                                                                                                          |
| 16:14  |   ro   |   0x0   | boot_greenlight_good | Green lights status for the boot process: _good_ indication coming from [0]: base ROM [1]: second ROM [2]: this module                                                                                                                            |
| 13:11  |   ro   |   0x0   | boot_greenlight_done | Green lights for the boot process: _done_ indication coming from [0]: base ROM [1]: second ROM [2]: this module Note that for the boot process to go through, all _done_ bits in this field and all _good_ bits in the next field need to be set. |
|  10:5  |   ro   |   0x0   | halt_fsm_state       | The state of the halt state FSM.                                                                                                                                                                                                                  |
|   4    |   ro   |   0x0   | cpu_fetch_en         | Indication from powermanger to IBEX to state code execution                                                                                                                                                                                       |
|   3    |   ro   |   0x0   | lc_done              | Lifecycle controller initialization done; LC policy is decoded and set                                                                                                                                                                            |
|   2    |   ro   |   0x0   | otp_done             | OTP controller initialization complete                                                                                                                                                                                                            |
|   1    |   ro   |   0x0   | io_clk_status        | Status of the IO Clock activation                                                                                                                                                                                                                 |
|   0    |   ro   |   0x0   | main_clk_status      | Status of the main clock activation                                                                                                                                                                                                               |

## JTAG_TRACE_SOC_DBG_STATE
Tells the current debug state coming from OTP.
Note that this information is reflected only if the hw_dft_en signal is true.
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "soc_dbg_state", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name          | Description              |
|:------:|:------:|:-------:|:--------------|:-------------------------|
|  31:0  |   ro   |   0x0   | soc_dbg_state | The current debug state. |


<!-- END CMDGEN -->
