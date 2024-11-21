# Registers

The RoT shall define three registers and drive the debug policy bus from that.
These registers are updated by the RoT FW and are distributed by the debug policy bus to all consumers, e.g., HW TAPs in the system.
Depending on the configured debug category, a consumer might accept the debug command or not (if it is not part of the selected debug category).

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/soc_dbg_ctrl/data/soc_dbg_ctrl.hjson -->
## Summary

| Name                                                                                   | Offset   |   Length | Description                                                                                              |
|:---------------------------------------------------------------------------------------|:---------|---------:|:---------------------------------------------------------------------------------------------------------|
| soc_dbg_ctrl.[`ALERT_TEST`](#alert_test)                                               | 0x0      |        4 | Alert Test Register                                                                                      |
| soc_dbg_ctrl.[`DEBUG_POLICY_VALID_SHADOWED`](#debug_policy_valid_shadowed)             | 0x4      |        4 | Debug Policy Valid.                                                                                      |
| soc_dbg_ctrl.[`DEBUG_POLICY_CATEGORY_SHADOWED`](#debug_policy_category_shadowed)       | 0x8      |        4 | Debug Policy category                                                                                    |
| soc_dbg_ctrl.[`DEBUG_POLICY_RELOCKED`](#debug_policy_relocked)                         | 0xc      |        4 | Debug Policy relocked                                                                                    |
| soc_dbg_ctrl.[`TRACE_DEBUG_POLICY_CATEGORY`](#trace_debug_policy_category)             | 0x10     |        4 | Trace register to observe the debug category that is either determined by hardware or software.          |
| soc_dbg_ctrl.[`TRACE_DEBUG_POLICY_VALID_RELOCKED`](#trace_debug_policy_valid_relocked) | 0x14     |        4 | Trace register to observe the valid or relocked state that is either determined by hardware or software. |

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


<!-- END CMDGEN -->
