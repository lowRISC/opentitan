# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/top_darjeeling/ip_autogen/racl_ctrl/data/racl_ctrl.hjson -->
## Summary

| Name                                                                    | Offset   |   Length | Description                                              |
|:------------------------------------------------------------------------|:---------|---------:|:---------------------------------------------------------|
| racl_ctrl.[`POLICY_ALL_RD_WR_SHADOWED`](#policy_all_rd_wr_shadowed)     | 0x0      |        4 | Read and write policy for ALL_RD_WR                      |
| racl_ctrl.[`POLICY_ROT_PRIVATE_SHADOWED`](#policy_rot_private_shadowed) | 0x8      |        4 | Read and write policy for ROT_PRIVATE                    |
| racl_ctrl.[`POLICY_SOC_ROT_SHADOWED`](#policy_soc_rot_shadowed)         | 0x10     |        4 | Read and write policy for SOC_ROT                        |
| racl_ctrl.[`INTR_STATE`](#intr_state)                                   | 0xe8     |        4 | Interrupt State Register                                 |
| racl_ctrl.[`INTR_ENABLE`](#intr_enable)                                 | 0xec     |        4 | Interrupt Enable Register                                |
| racl_ctrl.[`INTR_TEST`](#intr_test)                                     | 0xf0     |        4 | Interrupt Test Register                                  |
| racl_ctrl.[`ALERT_TEST`](#alert_test)                                   | 0xf4     |        4 | Alert Test Register.                                     |
| racl_ctrl.[`ERROR_LOG`](#error_log)                                     | 0xf8     |        4 | Error logging registers                                  |
| racl_ctrl.[`ERROR_LOG_ADDRESS`](#error_log_address)                     | 0xfc     |        4 | Contains the address on which a RACL violation occurred. |

## POLICY_ALL_RD_WR_SHADOWED
Read and write policy for ALL_RD_WR
- Offset: `0x0`
- Reset default: `0x70007`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "read_perm", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "write_perm", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                           |
|:------:|:------:|:-------:|:-----------|:--------------------------------------|
| 31:16  |   rw   |   0x7   | write_perm | Write permission for policy ALL_RD_WR |
|  15:0  |   rw   |   0x7   | read_perm  | Read permission for policy ALL_RD_WR  |

## POLICY_ROT_PRIVATE_SHADOWED
Read and write policy for ROT_PRIVATE
- Offset: `0x8`
- Reset default: `0x10001`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "read_perm", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "write_perm", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                             |
|:------:|:------:|:-------:|:-----------|:----------------------------------------|
| 31:16  |   rw   |   0x1   | write_perm | Write permission for policy ROT_PRIVATE |
|  15:0  |   rw   |   0x1   | read_perm  | Read permission for policy ROT_PRIVATE  |

## POLICY_SOC_ROT_SHADOWED
Read and write policy for SOC_ROT
- Offset: `0x10`
- Reset default: `0x50005`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "read_perm", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "write_perm", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                         |
|:------:|:------:|:-------:|:-----------|:------------------------------------|
| 31:16  |   rw   |   0x5   | write_perm | Write permission for policy SOC_ROT |
|  15:0  |   rw   |   0x5   | read_perm  | Read permission for policy SOC_ROT  |

## INTR_STATE
Interrupt State Register
- Offset: `0xe8`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "racl_error", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                                                                                                |
|:------:|:------:|:-------:|:-----------|:-------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |            | Reserved                                                                                                                                   |
|   0    |   ro   |   0x0   | racl_error | Interrupt status. The interrupt is raised when a RACL error occurs and cleared when error_log is cleared by writing 1 to error_log.valid." |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0xec`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "IE", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description      |
|:------:|:------:|:-------:|:-------|:-----------------|
|  31:1  |        |         |        | Reserved         |
|   0    |   rw   |   0x0   | IE     | Interrupt Enable |

## INTR_TEST
Interrupt Test Register
- Offset: `0xf0`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "racl_error", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                           |
|:------:|:------:|:-------:|:-----------|:--------------------------------------|
|  31:1  |        |         |            | Reserved                              |
|   0    |   wo   |    x    | racl_error | Write 1 to force racl_error interrupt |

## ALERT_TEST
Alert Test Register.
- Offset: `0xf4`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "fatal_fault", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "recov_ctrl_update_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                        |
|:------:|:------:|:-------:|:----------------------|:---------------------------------------------------|
|  31:2  |        |         |                       | Reserved                                           |
|   1    |   wo   |    x    | recov_ctrl_update_err | 'Write 1 to trigger one alert event of this kind.' |
|   0    |   wo   |    x    | fatal_fault           | 'Write 1 to trigger one alert event of this kind.' |

## ERROR_LOG
Error logging registers
- Offset: `0xf8`
- Reset default: `0x0`
- Reset mask: `0xfff`

### Fields

```wavejson
{"reg": [{"name": "valid", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "overflow", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "read_access", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "role", "bits": 4, "attr": ["ro"], "rotate": 0}, {"name": "ctn_uid", "bits": 5, "attr": ["ro"], "rotate": 0}, {"bits": 20}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                                                                                                                     |
|:------:|:------:|:-------:|:------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:12  |        |         |             | Reserved                                                                                                                                                        |
|  11:7  |   ro   |   0x0   | ctn_uid     | CTN UID causing the error.                                                                                                                                      |
|  6:3   |   ro   |   0x0   | role        | RACL role causing the error.                                                                                                                                    |
|   2    |   ro   |   0x0   | read_access | 0: Write transfer was denied. 1: Read transfer was denied.                                                                                                      |
|   1    |   ro   |   0x0   | overflow    | Indicates a RACL error overflow when a RACL error occurred while the log register was set.                                                                      |
|   0    |  rw1c  |   0x0   | valid       | Indicates a RACL error and the log register contains valid data. Writing a one clears this register and the [`ERROR_LOG_ADDRESS`](#error_log_address) register. |

## ERROR_LOG_ADDRESS
Contains the address on which a RACL violation occurred.
   This register is valid if and only if the `valid` field of [`ERROR_LOG`](#error_log) is true.
   Once valid, the address doesn't change (even if there are subsequent RACL violations) until the register gets cleared.
   This register gets cleared when SW writes `1` to the `valid` field of the [`ERROR_LOG`](#error_log) register.
- Offset: `0xfc`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "address", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name    | Description                                 |
|:------:|:------:|:-------:|:--------|:--------------------------------------------|
|  31:0  |   ro   |   0x0   | address | Address on which a RACL violation occurred. |


<!-- END CMDGEN -->
