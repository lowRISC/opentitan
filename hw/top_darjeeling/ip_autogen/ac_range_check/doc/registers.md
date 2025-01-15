# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/top_darjeeling/ip_autogen/ac_range_check/data/ac_range_check.hjson -->
## Summary

| Name                                                                          | Offset   |   Length | Description                                                                                                                                               |
|:------------------------------------------------------------------------------|:---------|---------:|:----------------------------------------------------------------------------------------------------------------------------------------------------------|
| ac_range_check.[`INTR_STATE`](#intr_state)                                    | 0x0      |        4 | Interrupt State Register                                                                                                                                  |
| ac_range_check.[`INTR_ENABLE`](#intr_enable)                                  | 0x4      |        4 | Interrupt Enable Register                                                                                                                                 |
| ac_range_check.[`INTR_TEST`](#intr_test)                                      | 0x8      |        4 | Interrupt Test Register                                                                                                                                   |
| ac_range_check.[`ALERT_TEST`](#alert_test)                                    | 0xc      |        4 | Alert Test Register                                                                                                                                       |
| ac_range_check.[`LOG_CONFIG`](#log_config)                                    | 0x10     |        4 |                                                                                                                                                           |
| ac_range_check.[`LOG_STATUS`](#log_status)                                    | 0x14     |        4 | The LOG_STATUS register stores the number of denied accesses and gives more detailed diagnostics to the first denied request.                             |
| ac_range_check.[`LOG_ADDRESS`](#log_address)                                  | 0x18     |        4 | First denied request address (if logging is enabled) gets written into that register.                                                                     |
| ac_range_check.[`RANGE_REGWEN_0`](#range_regwen)                              | 0x1c     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_PERM_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_1`](#range_regwen)                              | 0x20     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_PERM_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_2`](#range_regwen)                              | 0x24     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_PERM_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_3`](#range_regwen)                              | 0x28     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_PERM_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_4`](#range_regwen)                              | 0x2c     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_PERM_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_5`](#range_regwen)                              | 0x30     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_PERM_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_6`](#range_regwen)                              | 0x34     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_PERM_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_7`](#range_regwen)                              | 0x38     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_PERM_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_8`](#range_regwen)                              | 0x3c     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_PERM_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_9`](#range_regwen)                              | 0x40     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_PERM_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_10`](#range_regwen)                             | 0x44     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_PERM_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_11`](#range_regwen)                             | 0x48     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_PERM_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_12`](#range_regwen)                             | 0x4c     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_PERM_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_13`](#range_regwen)                             | 0x50     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_PERM_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_14`](#range_regwen)                             | 0x54     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_PERM_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_REGWEN_15`](#range_regwen)                             | 0x58     |        4 | This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_PERM_x, and RANGE_RACL_POLICY_SHADOWED_x register. |
| ac_range_check.[`RANGE_BASE_0`](#range_base)                                  | 0x5c     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_1`](#range_base)                                  | 0x60     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_2`](#range_base)                                  | 0x64     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_3`](#range_base)                                  | 0x68     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_4`](#range_base)                                  | 0x6c     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_5`](#range_base)                                  | 0x70     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_6`](#range_base)                                  | 0x74     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_7`](#range_base)                                  | 0x78     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_8`](#range_base)                                  | 0x7c     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_9`](#range_base)                                  | 0x80     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_10`](#range_base)                                 | 0x84     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_11`](#range_base)                                 | 0x88     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_12`](#range_base)                                 | 0x8c     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_13`](#range_base)                                 | 0x90     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_14`](#range_base)                                 | 0x94     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_BASE_15`](#range_base)                                 | 0x98     |        4 | Base address for the range check.                                                                                                                         |
| ac_range_check.[`RANGE_LIMIT_0`](#range_limit)                                | 0x9c     |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_1`](#range_limit)                                | 0xa0     |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_2`](#range_limit)                                | 0xa4     |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_3`](#range_limit)                                | 0xa8     |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_4`](#range_limit)                                | 0xac     |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_5`](#range_limit)                                | 0xb0     |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_6`](#range_limit)                                | 0xb4     |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_7`](#range_limit)                                | 0xb8     |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_8`](#range_limit)                                | 0xbc     |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_9`](#range_limit)                                | 0xc0     |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_10`](#range_limit)                               | 0xc4     |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_11`](#range_limit)                               | 0xc8     |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_12`](#range_limit)                               | 0xcc     |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_13`](#range_limit)                               | 0xd0     |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_14`](#range_limit)                               | 0xd4     |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_LIMIT_15`](#range_limit)                               | 0xd8     |        4 | The (exclusive) limit address register used for the address matching.                                                                                     |
| ac_range_check.[`RANGE_PERM_0`](#range_perm)                                  | 0xdc     |        4 | Permission configuration of the range.                                                                                                                    |
| ac_range_check.[`RANGE_PERM_1`](#range_perm)                                  | 0xe0     |        4 | Permission configuration of the range.                                                                                                                    |
| ac_range_check.[`RANGE_PERM_2`](#range_perm)                                  | 0xe4     |        4 | Permission configuration of the range.                                                                                                                    |
| ac_range_check.[`RANGE_PERM_3`](#range_perm)                                  | 0xe8     |        4 | Permission configuration of the range.                                                                                                                    |
| ac_range_check.[`RANGE_PERM_4`](#range_perm)                                  | 0xec     |        4 | Permission configuration of the range.                                                                                                                    |
| ac_range_check.[`RANGE_PERM_5`](#range_perm)                                  | 0xf0     |        4 | Permission configuration of the range.                                                                                                                    |
| ac_range_check.[`RANGE_PERM_6`](#range_perm)                                  | 0xf4     |        4 | Permission configuration of the range.                                                                                                                    |
| ac_range_check.[`RANGE_PERM_7`](#range_perm)                                  | 0xf8     |        4 | Permission configuration of the range.                                                                                                                    |
| ac_range_check.[`RANGE_PERM_8`](#range_perm)                                  | 0xfc     |        4 | Permission configuration of the range.                                                                                                                    |
| ac_range_check.[`RANGE_PERM_9`](#range_perm)                                  | 0x100    |        4 | Permission configuration of the range.                                                                                                                    |
| ac_range_check.[`RANGE_PERM_10`](#range_perm)                                 | 0x104    |        4 | Permission configuration of the range.                                                                                                                    |
| ac_range_check.[`RANGE_PERM_11`](#range_perm)                                 | 0x108    |        4 | Permission configuration of the range.                                                                                                                    |
| ac_range_check.[`RANGE_PERM_12`](#range_perm)                                 | 0x10c    |        4 | Permission configuration of the range.                                                                                                                    |
| ac_range_check.[`RANGE_PERM_13`](#range_perm)                                 | 0x110    |        4 | Permission configuration of the range.                                                                                                                    |
| ac_range_check.[`RANGE_PERM_14`](#range_perm)                                 | 0x114    |        4 | Permission configuration of the range.                                                                                                                    |
| ac_range_check.[`RANGE_PERM_15`](#range_perm)                                 | 0x118    |        4 | Permission configuration of the range.                                                                                                                    |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_0`](#range_racl_policy_shadowed)  | 0x11c    |        4 | The RACL policy register exists and allows the system to further restrict the access to specific source roles.                                            |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_1`](#range_racl_policy_shadowed)  | 0x120    |        4 | The RACL policy register exists and allows the system to further restrict the access to specific source roles.                                            |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_2`](#range_racl_policy_shadowed)  | 0x124    |        4 | The RACL policy register exists and allows the system to further restrict the access to specific source roles.                                            |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_3`](#range_racl_policy_shadowed)  | 0x128    |        4 | The RACL policy register exists and allows the system to further restrict the access to specific source roles.                                            |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_4`](#range_racl_policy_shadowed)  | 0x12c    |        4 | The RACL policy register exists and allows the system to further restrict the access to specific source roles.                                            |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_5`](#range_racl_policy_shadowed)  | 0x130    |        4 | The RACL policy register exists and allows the system to further restrict the access to specific source roles.                                            |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_6`](#range_racl_policy_shadowed)  | 0x134    |        4 | The RACL policy register exists and allows the system to further restrict the access to specific source roles.                                            |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_7`](#range_racl_policy_shadowed)  | 0x138    |        4 | The RACL policy register exists and allows the system to further restrict the access to specific source roles.                                            |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_8`](#range_racl_policy_shadowed)  | 0x13c    |        4 | The RACL policy register exists and allows the system to further restrict the access to specific source roles.                                            |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_9`](#range_racl_policy_shadowed)  | 0x140    |        4 | The RACL policy register exists and allows the system to further restrict the access to specific source roles.                                            |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_10`](#range_racl_policy_shadowed) | 0x144    |        4 | The RACL policy register exists and allows the system to further restrict the access to specific source roles.                                            |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_11`](#range_racl_policy_shadowed) | 0x148    |        4 | The RACL policy register exists and allows the system to further restrict the access to specific source roles.                                            |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_12`](#range_racl_policy_shadowed) | 0x14c    |        4 | The RACL policy register exists and allows the system to further restrict the access to specific source roles.                                            |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_13`](#range_racl_policy_shadowed) | 0x150    |        4 | The RACL policy register exists and allows the system to further restrict the access to specific source roles.                                            |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_14`](#range_racl_policy_shadowed) | 0x154    |        4 | The RACL policy register exists and allows the system to further restrict the access to specific source roles.                                            |
| ac_range_check.[`RANGE_RACL_POLICY_SHADOWED_15`](#range_racl_policy_shadowed) | 0x158    |        4 | The RACL policy register exists and allows the system to further restrict the access to specific source roles.                                            |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "deny_cnt_reached", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                         |
|:------:|:------:|:-------:|:-----------------|:------------------------------------|
|  31:1  |        |         |                  | Reserved                            |
|   0    |  rw1c  |   0x0   | deny_cnt_reached | Deny counter has reached threshold. |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "deny_cnt_reached", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                                |
|:------:|:------:|:-------:|:-----------------|:---------------------------------------------------------------------------|
|  31:1  |        |         |                  | Reserved                                                                   |
|   0    |   rw   |   0x0   | deny_cnt_reached | Enable interrupt when [`INTR_STATE.deny_cnt_reached`](#intr_state) is set. |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "deny_cnt_reached", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                         |
|:------:|:------:|:-------:|:-----------------|:--------------------------------------------------------------------|
|  31:1  |        |         |                  | Reserved                                                            |
|   0    |   wo   |   0x0   | deny_cnt_reached | Write 1 to force [`INTR_STATE.deny_cnt_reached`](#intr_state) to 1. |

## ALERT_TEST
Alert Test Register
- Offset: `0xc`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "recov_ctrl_update_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_fault", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                      |
|:------:|:------:|:-------:|:----------------------|:-------------------------------------------------|
|  31:2  |        |         |                       | Reserved                                         |
|   1    |   wo   |   0x0   | fatal_fault           | Write 1 to trigger one alert event of this kind. |
|   0    |   wo   |   0x0   | recov_ctrl_update_err | Write 1 to trigger one alert event of this kind. |

## LOG_CONFIG

- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0x3ff`

### Fields

```wavejson
{"reg": [{"name": "log_enable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "log_clear", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "deny_cnt_threshold", "bits": 8, "attr": ["rw"], "rotate": -90}, {"bits": 22}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                                                                    |
|:------:|:------:|:-------:|:-------------------|:-----------------------------------------------------------------------------------------------|
| 31:10  |        |         |                    | Reserved                                                                                       |
|  9:2   |   rw   |   0x0   | deny_cnt_threshold | An interrupt is raised (if enabled) when deny_cnt reaches the configured deny_cnt_threshold.   |
|   1    |   rw   |   0x0   | log_clear          | Clears all log information for the first denied access including:  - LOG_STATUS - LOG_ADDRESS. |
|   0    |   rw   |   0x0   | log_enable         | When set, blocked requests are logged by the deny counter.                                     |

## LOG_STATUS
The LOG_STATUS register stores the number of denied accesses and gives more detailed diagnostics to the first denied request. 
All fields of LOG_STATUS (other than deny_cnt) are only valid if deny_cnt > 0.
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0x7fffff`

### Fields

```wavejson
{"reg": [{"name": "deny_cnt", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "denied_read_access", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "denied_write_access", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "denied_execute_access", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "denied_no_match", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "denied_racl_read", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "denied_racl_write", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "denied_source_role", "bits": 4, "attr": ["ro"], "rotate": -90}, {"name": "deny_range_index", "bits": 5, "attr": ["ro"], "rotate": -90}, {"bits": 9}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                                                               |
|:------:|:------:|:-------:|:----------------------|:------------------------------------------------------------------------------------------|
| 31:23  |        |         |                       | Reserved                                                                                  |
| 22:18  |   ro   |   0x0   | deny_range_index      | Index of the range that caused the denied access.                                         |
| 17:14  |   ro   |   0x0   | denied_source_role    | Source RACL role that was denied access.                                                  |
|   13   |   ro   |   0x0   | denied_racl_write     | Indicates whether a write access was denied by RACL.                                      |
|   12   |   ro   |   0x0   | denied_racl_read      | Indicates whether a read access was denied by RACL.                                       |
|   11   |   ro   |   0x0   | denied_no_match       | Indicates whether the access was denied because no range matched.                         |
|   10   |   ro   |   0x0   | denied_execute_access | Indicates whether execution access was denied.                                            |
|   9    |   ro   |   0x0   | denied_write_access   | Indicates whether a write access was denied.                                              |
|   8    |   ro   |   0x0   | denied_read_access    | Indicates whether a read access was denied.                                               |
|  7:0   |   ro   |   0x0   | deny_cnt              | Software mirror of the internal deny counter. Gets incremented for every blocked request. |

## LOG_ADDRESS
First denied request address (if logging is enabled) gets written into that register.
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "log_address", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                   |
|:------:|:------:|:-------:|:------------|:------------------------------|
|  31:0  |   ro   |   0x0   | log_address | First denied request address. |

## RANGE_REGWEN
This register exists per range and provides a regwen signal for the RANGE_BASE_x, RANGE_LIMIT_x, RANGE_PERM_x, and RANGE_RACL_POLICY_SHADOWED_x register. 
When cleared to Mubi4::False, the corresponding range configuration registers are locked and cannot be changed until the next reset.
- Reset default: `0x6`
- Reset mask: `0xf`

### Instances

| Name            | Offset   |
|:----------------|:---------|
| RANGE_REGWEN_0  | 0x1c     |
| RANGE_REGWEN_1  | 0x20     |
| RANGE_REGWEN_2  | 0x24     |
| RANGE_REGWEN_3  | 0x28     |
| RANGE_REGWEN_4  | 0x2c     |
| RANGE_REGWEN_5  | 0x30     |
| RANGE_REGWEN_6  | 0x34     |
| RANGE_REGWEN_7  | 0x38     |
| RANGE_REGWEN_8  | 0x3c     |
| RANGE_REGWEN_9  | 0x40     |
| RANGE_REGWEN_10 | 0x44     |
| RANGE_REGWEN_11 | 0x48     |
| RANGE_REGWEN_12 | 0x4c     |
| RANGE_REGWEN_13 | 0x50     |
| RANGE_REGWEN_14 | 0x54     |
| RANGE_REGWEN_15 | 0x58     |


### Fields

```wavejson
{"reg": [{"name": "regwen", "bits": 4, "attr": ["rw0c"], "rotate": 0}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                    |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------------|
|  31:4  |        |         |        | Reserved                                                                                       |
|  3:0   |  rw0c  |   0x6   | regwen | Clearing this register, locks the confgiguration registers of that range until the next reset. |

## RANGE_BASE
Base address for the range check.
The range base register exists per range and holds the base address for the range check.
The minimum granularity of the range is 4 bytes.
Therefore, the lowest 2 bits of the 32-bit base and limit registers are tied to zero.
- Reset default: `0x0`
- Reset mask: `0xfffffffc`
- Register enable: [`RANGE_REGWEN`](#range_regwen)

### Instances

| Name          | Offset   |
|:--------------|:---------|
| RANGE_BASE_0  | 0x5c     |
| RANGE_BASE_1  | 0x60     |
| RANGE_BASE_2  | 0x64     |
| RANGE_BASE_3  | 0x68     |
| RANGE_BASE_4  | 0x6c     |
| RANGE_BASE_5  | 0x70     |
| RANGE_BASE_6  | 0x74     |
| RANGE_BASE_7  | 0x78     |
| RANGE_BASE_8  | 0x7c     |
| RANGE_BASE_9  | 0x80     |
| RANGE_BASE_10 | 0x84     |
| RANGE_BASE_11 | 0x88     |
| RANGE_BASE_12 | 0x8c     |
| RANGE_BASE_13 | 0x90     |
| RANGE_BASE_14 | 0x94     |
| RANGE_BASE_15 | 0x98     |


### Fields

```wavejson
{"reg": [{"bits": 2}, {"name": "base", "bits": 30, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:2  |   rw   |   0x0   | base   | Base address  |
|  1:0   |        |         |        | Reserved      |

## RANGE_LIMIT
The (exclusive) limit address register used for the address matching. 
- Reset default: `0x0`
- Reset mask: `0xfffffffc`
- Register enable: [`RANGE_REGWEN`](#range_regwen)

### Instances

| Name           | Offset   |
|:---------------|:---------|
| RANGE_LIMIT_0  | 0x9c     |
| RANGE_LIMIT_1  | 0xa0     |
| RANGE_LIMIT_2  | 0xa4     |
| RANGE_LIMIT_3  | 0xa8     |
| RANGE_LIMIT_4  | 0xac     |
| RANGE_LIMIT_5  | 0xb0     |
| RANGE_LIMIT_6  | 0xb4     |
| RANGE_LIMIT_7  | 0xb8     |
| RANGE_LIMIT_8  | 0xbc     |
| RANGE_LIMIT_9  | 0xc0     |
| RANGE_LIMIT_10 | 0xc4     |
| RANGE_LIMIT_11 | 0xc8     |
| RANGE_LIMIT_12 | 0xcc     |
| RANGE_LIMIT_13 | 0xd0     |
| RANGE_LIMIT_14 | 0xd4     |
| RANGE_LIMIT_15 | 0xd8     |


### Fields

```wavejson
{"reg": [{"bits": 2}, {"name": "limit", "bits": 30, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description              |
|:------:|:------:|:-------:|:-------|:-------------------------|
|  31:2  |   rw   |   0x0   | limit  | Exclusive limit address. |
|  1:0   |        |         |        | Reserved                 |

## RANGE_PERM
Permission configuration of the range.
The permission register exists per range and determines the access permissions of the particular range.
If it is not enabled, the range is not considered during the range check.
- Reset default: `0x69999`
- Reset mask: `0xfffff`
- Register enable: [`RANGE_REGWEN`](#range_regwen)

### Instances

| Name          | Offset   |
|:--------------|:---------|
| RANGE_PERM_0  | 0xdc     |
| RANGE_PERM_1  | 0xe0     |
| RANGE_PERM_2  | 0xe4     |
| RANGE_PERM_3  | 0xe8     |
| RANGE_PERM_4  | 0xec     |
| RANGE_PERM_5  | 0xf0     |
| RANGE_PERM_6  | 0xf4     |
| RANGE_PERM_7  | 0xf8     |
| RANGE_PERM_8  | 0xfc     |
| RANGE_PERM_9  | 0x100    |
| RANGE_PERM_10 | 0x104    |
| RANGE_PERM_11 | 0x108    |
| RANGE_PERM_12 | 0x10c    |
| RANGE_PERM_13 | 0x110    |
| RANGE_PERM_14 | 0x114    |
| RANGE_PERM_15 | 0x118    |


### Fields

```wavejson
{"reg": [{"name": "enable", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "read_access", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "write_access", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "execute_access", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "log_denied_access", "bits": 4, "attr": ["rw"], "rotate": -90}, {"bits": 12}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                                                                      |
|:------:|:------:|:-------:|:------------------|:---------------------------------------------------------------------------------|
| 31:20  |        |         |                   | Reserved                                                                         |
| 19:16  |   rw   |   0x6   | log_denied_access | When set to Mubi4::True, a denied access based on in this range is being logged. |
| 15:12  |   rw   |   0x9   | execute_access    | When set to Mubi4::True, code execution from this range is allowed.              |
|  11:8  |   rw   |   0x9   | write_access      | When set to Mubi4::True, write access to that range is allowed.                  |
|  7:4   |   rw   |   0x9   | read_access       | When set to Mubi4::True, read access from that range is allowed.                 |
|  3:0   |   rw   |   0x9   | enable            | When set to Mubi4::True, the range is considered in the range check.             |

## RANGE_RACL_POLICY_SHADOWED
The RACL policy register exists and allows the system to further restrict the access to specific source roles.
The default value for both the read and write permission bitmap is set to a value to allow the access from all roles.
This register is protected against fault attacks by using a shadow register implementation. 
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`RANGE_REGWEN`](#range_regwen)

### Instances

| Name                          | Offset   |
|:------------------------------|:---------|
| RANGE_RACL_POLICY_SHADOWED_0  | 0x11c    |
| RANGE_RACL_POLICY_SHADOWED_1  | 0x120    |
| RANGE_RACL_POLICY_SHADOWED_2  | 0x124    |
| RANGE_RACL_POLICY_SHADOWED_3  | 0x128    |
| RANGE_RACL_POLICY_SHADOWED_4  | 0x12c    |
| RANGE_RACL_POLICY_SHADOWED_5  | 0x130    |
| RANGE_RACL_POLICY_SHADOWED_6  | 0x134    |
| RANGE_RACL_POLICY_SHADOWED_7  | 0x138    |
| RANGE_RACL_POLICY_SHADOWED_8  | 0x13c    |
| RANGE_RACL_POLICY_SHADOWED_9  | 0x140    |
| RANGE_RACL_POLICY_SHADOWED_10 | 0x144    |
| RANGE_RACL_POLICY_SHADOWED_11 | 0x148    |
| RANGE_RACL_POLICY_SHADOWED_12 | 0x14c    |
| RANGE_RACL_POLICY_SHADOWED_13 | 0x150    |
| RANGE_RACL_POLICY_SHADOWED_14 | 0x154    |
| RANGE_RACL_POLICY_SHADOWED_15 | 0x158    |


### Fields

```wavejson
{"reg": [{"name": "read_perm", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "write_perm", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                     |
|:------:|:------:|:-------:|:-----------|:--------------------------------|
| 31:16  |   rw   |   0x0   | write_perm | Write permission policy bitmap. |
|  15:0  |   rw   |   0x0   | read_perm  | Read permission policy bitmap.  |


<!-- END CMDGEN -->
