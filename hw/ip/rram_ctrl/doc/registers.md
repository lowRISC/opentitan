# Registers

The RRAM controller maintains two separate access windows for the FIFOs.
It is implemented this way because the access window supports transaction back-pressure should the FIFO become full (in case of write) or empty (in case of read).

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/rram_ctrl/data/rram_ctrl.hjson -->
## Summary

| Name                                                      | Offset   |   Length | Description                                                         |
|:----------------------------------------------------------|:---------|---------:|:--------------------------------------------------------------------|
| rram_ctrl.[`INTR_STATE`](#intr_state)                     | 0x0      |        4 | Interrupt State Register                                            |
| rram_ctrl.[`INTR_ENABLE`](#intr_enable)                   | 0x4      |        4 | Interrupt Enable Register                                           |
| rram_ctrl.[`INTR_TEST`](#intr_test)                       | 0x8      |        4 | Interrupt Test Register                                             |
| rram_ctrl.[`ALERT_TEST`](#alert_test)                     | 0xc      |        4 | Alert Test Register                                                 |
| rram_ctrl.[`DIS`](#dis)                                   | 0x10     |        4 | Disable RRAM functionality                                          |
| rram_ctrl.[`EXEC`](#exec)                                 | 0x14     |        4 | Controls whether RRAM can be used for code execution fetches        |
| rram_ctrl.[`INIT`](#init)                                 | 0x18     |        4 | Controller init register                                            |
| rram_ctrl.[`CTRL_REGWEN`](#ctrl_regwen)                   | 0x1c     |        4 | Controls the configurability of the [`CONTROL`](#control) register. |
| rram_ctrl.[`CONTROL`](#control)                           | 0x20     |        4 | Control register                                                    |
| rram_ctrl.[`ADDR`](#addr)                                 | 0x24     |        4 | Address for RRAM operation                                          |
| rram_ctrl.[`REGION_CFG_REGWEN_0`](#region_cfg_regwen)     | 0x28     |        4 | Memory region registers configuration enable.                       |
| rram_ctrl.[`REGION_CFG_REGWEN_1`](#region_cfg_regwen)     | 0x2c     |        4 | Memory region registers configuration enable.                       |
| rram_ctrl.[`REGION_CFG_REGWEN_2`](#region_cfg_regwen)     | 0x30     |        4 | Memory region registers configuration enable.                       |
| rram_ctrl.[`REGION_CFG_REGWEN_3`](#region_cfg_regwen)     | 0x34     |        4 | Memory region registers configuration enable.                       |
| rram_ctrl.[`REGION_CFG_REGWEN_4`](#region_cfg_regwen)     | 0x38     |        4 | Memory region registers configuration enable.                       |
| rram_ctrl.[`REGION_CFG_REGWEN_5`](#region_cfg_regwen)     | 0x3c     |        4 | Memory region registers configuration enable.                       |
| rram_ctrl.[`REGION_CFG_REGWEN_6`](#region_cfg_regwen)     | 0x40     |        4 | Memory region registers configuration enable.                       |
| rram_ctrl.[`REGION_CFG_REGWEN_7`](#region_cfg_regwen)     | 0x44     |        4 | Memory region registers configuration enable.                       |
| rram_ctrl.[`MP_REGION_CFG_0`](#mp_region_cfg)             | 0x48     |        4 | Memory property configuration for data partition                    |
| rram_ctrl.[`MP_REGION_CFG_1`](#mp_region_cfg)             | 0x4c     |        4 | Memory property configuration for data partition                    |
| rram_ctrl.[`MP_REGION_CFG_2`](#mp_region_cfg)             | 0x50     |        4 | Memory property configuration for data partition                    |
| rram_ctrl.[`MP_REGION_CFG_3`](#mp_region_cfg)             | 0x54     |        4 | Memory property configuration for data partition                    |
| rram_ctrl.[`MP_REGION_CFG_4`](#mp_region_cfg)             | 0x58     |        4 | Memory property configuration for data partition                    |
| rram_ctrl.[`MP_REGION_CFG_5`](#mp_region_cfg)             | 0x5c     |        4 | Memory property configuration for data partition                    |
| rram_ctrl.[`MP_REGION_CFG_6`](#mp_region_cfg)             | 0x60     |        4 | Memory property configuration for data partition                    |
| rram_ctrl.[`MP_REGION_CFG_7`](#mp_region_cfg)             | 0x64     |        4 | Memory property configuration for data partition                    |
| rram_ctrl.[`MP_REGION_0`](#mp_region)                     | 0x68     |        4 | Memory base and size configuration for data partition               |
| rram_ctrl.[`MP_REGION_1`](#mp_region)                     | 0x6c     |        4 | Memory base and size configuration for data partition               |
| rram_ctrl.[`MP_REGION_2`](#mp_region)                     | 0x70     |        4 | Memory base and size configuration for data partition               |
| rram_ctrl.[`MP_REGION_3`](#mp_region)                     | 0x74     |        4 | Memory base and size configuration for data partition               |
| rram_ctrl.[`MP_REGION_4`](#mp_region)                     | 0x78     |        4 | Memory base and size configuration for data partition               |
| rram_ctrl.[`MP_REGION_5`](#mp_region)                     | 0x7c     |        4 | Memory base and size configuration for data partition               |
| rram_ctrl.[`MP_REGION_6`](#mp_region)                     | 0x80     |        4 | Memory base and size configuration for data partition               |
| rram_ctrl.[`MP_REGION_7`](#mp_region)                     | 0x84     |        4 | Memory base and size configuration for data partition               |
| rram_ctrl.[`DEFAULT_REGION`](#default_region)             | 0x88     |        4 | Default region properties                                           |
| rram_ctrl.[`INFO_REGWEN_0`](#info_regwen)                 | 0x8c     |        4 | Memory region registers configuration enable.                       |
| rram_ctrl.[`INFO_REGWEN_1`](#info_regwen)                 | 0x90     |        4 | Memory region registers configuration enable.                       |
| rram_ctrl.[`INFO_REGWEN_2`](#info_regwen)                 | 0x94     |        4 | Memory region registers configuration enable.                       |
| rram_ctrl.[`INFO_REGWEN_3`](#info_regwen)                 | 0x98     |        4 | Memory region registers configuration enable.                       |
| rram_ctrl.[`INFO_REGWEN_4`](#info_regwen)                 | 0x9c     |        4 | Memory region registers configuration enable.                       |
| rram_ctrl.[`INFO_REGWEN_5`](#info_regwen)                 | 0xa0     |        4 | Memory region registers configuration enable.                       |
| rram_ctrl.[`INFO_REGWEN_6`](#info_regwen)                 | 0xa4     |        4 | Memory region registers configuration enable.                       |
| rram_ctrl.[`INFO_REGWEN_7`](#info_regwen)                 | 0xa8     |        4 | Memory region registers configuration enable.                       |
| rram_ctrl.[`INFO_PAGE_CFG_0`](#info_page_cfg)             | 0xac     |        4 | Memory property configuration for info partition.                   |
| rram_ctrl.[`INFO_PAGE_CFG_1`](#info_page_cfg)             | 0xb0     |        4 | Memory property configuration for info partition.                   |
| rram_ctrl.[`INFO_PAGE_CFG_2`](#info_page_cfg)             | 0xb4     |        4 | Memory property configuration for info partition.                   |
| rram_ctrl.[`INFO_PAGE_CFG_3`](#info_page_cfg)             | 0xb8     |        4 | Memory property configuration for info partition.                   |
| rram_ctrl.[`INFO_PAGE_CFG_4`](#info_page_cfg)             | 0xbc     |        4 | Memory property configuration for info partition.                   |
| rram_ctrl.[`INFO_PAGE_CFG_5`](#info_page_cfg)             | 0xc0     |        4 | Memory property configuration for info partition.                   |
| rram_ctrl.[`INFO_PAGE_CFG_6`](#info_page_cfg)             | 0xc4     |        4 | Memory property configuration for info partition.                   |
| rram_ctrl.[`INFO_PAGE_CFG_7`](#info_page_cfg)             | 0xc8     |        4 | Memory property configuration for info partition.                   |
| rram_ctrl.[`HW_INFO_CFG_OVERRIDE`](#hw_info_cfg_override) | 0xcc     |        4 | HW interface info configuration rule overrides                      |
| rram_ctrl.[`OP_STATUS`](#op_status)                       | 0xd0     |        4 | RRAM Operation Status                                               |
| rram_ctrl.[`STATUS`](#status)                             | 0xd4     |        4 | RRAM Controller Status                                              |
| rram_ctrl.[`ERR_CODE`](#err_code)                         | 0xd8     |        4 | RRAM error code register.                                           |
| rram_ctrl.[`STD_FAULT_STATUS`](#std_fault_status)         | 0xdc     |        4 | This register tabulates standard fault status of the RRAM.          |
| rram_ctrl.[`FAULT_STATUS`](#fault_status)                 | 0xe0     |        4 | This register tabulates customized fault status of the RRAM.        |
| rram_ctrl.[`ERR_ADDR`](#err_addr)                         | 0xe4     |        4 | Synchronous error address                                           |
| rram_ctrl.[`CORR_ERR_CNT`](#corr_err_cnt)                 | 0xe8     |        4 | Count of correctable ECC errors                                     |
| rram_ctrl.[`CORR_ERR_LOC`](#corr_err_loc)                 | 0xec     |        4 | Last address that was successfully corrected                        |
| rram_ctrl.[`PHY_STATUS`](#phy_status)                     | 0xf0     |        4 | RRAM Phy Status                                                     |
| rram_ctrl.[`SCRATCH`](#scratch)                           | 0xf4     |        4 | RRAM Controller Scratch                                             |
| rram_ctrl.[`FIFO_LVL`](#fifo_lvl)                         | 0xf8     |        4 | Programmable depth where FIFOs should generate interrupts           |
| rram_ctrl.[`FIFO_CLR`](#fifo_clr)                         | 0xfc     |        4 | Clears RRAM controller FIFOs                                        |
| rram_ctrl.[`CURR_FIFO_LVL`](#curr_fifo_lvl)               | 0x100    |        4 | Current write and read fifo level                                   |
| rram_ctrl.[`wr_fifo`](#wr_fifo)                           | 0x104    |        4 | RRAM write FIFO.                                                    |
| rram_ctrl.[`rd_fifo`](#rd_fifo)                           | 0x108    |        4 | RRAM read FIFO.                                                     |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x3`
- Reset mask: `0x3f`

### Fields

```wavejson
{"reg": [{"name": "wr_empty", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "wr_lvl", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "rd_full", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "rd_lvl", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "op_done", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "corr_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 26}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                   |
|:------:|:------:|:-------:|:---------|:------------------------------|
|  31:6  |        |         |          | Reserved                      |
|   5    |  rw1c  |   0x0   | corr_err | Correctable error encountered |
|   4    |  rw1c  |   0x0   | op_done  | Operation complete            |
|   3    |   ro   |   0x0   | rd_lvl   | Read FIFO filled to level     |
|   2    |   ro   |   0x0   | rd_full  | Read FIFO full                |
|   1    |   ro   |   0x1   | wr_lvl   | Write FIFO drained to level   |
|   0    |   ro   |   0x1   | wr_empty | Write FIFO empty              |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x3f`

### Fields

```wavejson
{"reg": [{"name": "wr_empty", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "wr_lvl", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rd_full", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rd_lvl", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "op_done", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "corr_err", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 26}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                        |
|:------:|:------:|:-------:|:---------|:-------------------------------------------------------------------|
|  31:6  |        |         |          | Reserved                                                           |
|   5    |   rw   |   0x0   | corr_err | Enable interrupt when [`INTR_STATE.corr_err`](#intr_state) is set. |
|   4    |   rw   |   0x0   | op_done  | Enable interrupt when [`INTR_STATE.op_done`](#intr_state) is set.  |
|   3    |   rw   |   0x0   | rd_lvl   | Enable interrupt when [`INTR_STATE.rd_lvl`](#intr_state) is set.   |
|   2    |   rw   |   0x0   | rd_full  | Enable interrupt when [`INTR_STATE.rd_full`](#intr_state) is set.  |
|   1    |   rw   |   0x0   | wr_lvl   | Enable interrupt when [`INTR_STATE.wr_lvl`](#intr_state) is set.   |
|   0    |   rw   |   0x0   | wr_empty | Enable interrupt when [`INTR_STATE.wr_empty`](#intr_state) is set. |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x3f`

### Fields

```wavejson
{"reg": [{"name": "wr_empty", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "wr_lvl", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rd_full", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rd_lvl", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "op_done", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "corr_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 26}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                 |
|:------:|:------:|:-------:|:---------|:------------------------------------------------------------|
|  31:6  |        |         |          | Reserved                                                    |
|   5    |   wo   |   0x0   | corr_err | Write 1 to force [`INTR_STATE.corr_err`](#intr_state) to 1. |
|   4    |   wo   |   0x0   | op_done  | Write 1 to force [`INTR_STATE.op_done`](#intr_state) to 1.  |
|   3    |   wo   |   0x0   | rd_lvl   | Write 1 to force [`INTR_STATE.rd_lvl`](#intr_state) to 1.   |
|   2    |   wo   |   0x0   | rd_full  | Write 1 to force [`INTR_STATE.rd_full`](#intr_state) to 1.  |
|   1    |   wo   |   0x0   | wr_lvl   | Write 1 to force [`INTR_STATE.wr_lvl`](#intr_state) to 1.   |
|   0    |   wo   |   0x0   | wr_empty | Write 1 to force [`INTR_STATE.wr_empty`](#intr_state) to 1. |

## ALERT_TEST
Alert Test Register
- Offset: `0xc`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "recov_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_std_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_macro_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "recov_macro_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name            | Description                                      |
|:------:|:------:|:-------:|:----------------|:-------------------------------------------------|
|  31:5  |        |         |                 | Reserved                                         |
|   4    |   wo   |   0x0   | recov_macro_err | Write 1 to trigger one alert event of this kind. |
|   3    |   wo   |   0x0   | fatal_macro_err | Write 1 to trigger one alert event of this kind. |
|   2    |   wo   |   0x0   | fatal_err       | Write 1 to trigger one alert event of this kind. |
|   1    |   wo   |   0x0   | fatal_std_err   | Write 1 to trigger one alert event of this kind. |
|   0    |   wo   |   0x0   | recov_err       | Write 1 to trigger one alert event of this kind. |

## DIS
Disable RRAM functionality
- Offset: `0x10`
- Reset default: `0x99`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "SW_DIS", "bits": 4, "attr": ["rw1s"], "rotate": 0}, {"name": "RELBL_ERR_FATAL", "bits": 4, "attr": ["rw1s"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name                                     |
|:------:|:------:|:-------:|:-----------------------------------------|
|  31:8  |        |         | Reserved                                 |
|  7:4   |  rw1s  |   0x9   | [RELBL_ERR_FATAL](#dis--relbl_err_fatal) |
|  3:0   |  rw1s  |   0x9   | [SW_DIS](#dis--sw_dis)                   |

### DIS . RELBL_ERR_FATAL
Configuration bit for reliablity error.
Once this config bit is set to MuBi4True, every fault in [`FAULT_STATUS`](#fault_status) will disable the RRAM immediately.
Otherwise [`FAULT_STATUS.PHY_RELBL_ERR`](#fault_status) is excluded for the local escalation to deal with firmware selection during the boot process.
Since this register is rw1s instead of rw this configuration cannot be reverted.

### DIS . SW_DIS
Disables RRAM functionality completely.
This is a shortcut mechanism used by the software to completely kill RRAM in case of emergency.
Since this register is rw1s instead of rw, to disable, write the value MuBi4True to the register to disable the RRAM.

## EXEC
Controls whether RRAM can be used for code execution fetches
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                               |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | EN     | A value of 0xa26a38f7 allows RRAM to be used for code execution. Any other value prevents code execution. |

## INIT
Controller init register
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 1, "attr": ["rw1s"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                                                         |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                                                                                                                                                            |
|   0    |  rw1s  |   0x0   | VAL    | Initializes the RRAM controller. During the initialization process, the RRAM controller requests the address and data scramble keys and reads out the root seeds stored in RRAM before allowing other usage of the RRAM controller. |

## CTRL_REGWEN
Controls the configurability of the [`CONTROL`](#control) register.
This register ensures the contents of [`CONTROL`](#control) cannot be changed by software once a RRAM operation has begun.
It unlocks whenever the existing RRAM operation completes, regardless of success or error.
- Offset: `0x1c`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                                                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                                                                                                                                                                         |
|   0    |   ro   |   0x1   | EN     | Configuration enable. This bit defaults to 1 and is set to 0 by hardware when RRAM operation is initiated. When the controller completes the RRAM operation, this bit is set back to 1 to allow software configuration of [`CONTROL.`](#control) |

## CONTROL
Control register
- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0x3ff0131`
- Register enable: [`CTRL_REGWEN`](#ctrl_regwen)

### Fields

```wavejson
{"reg": [{"name": "START", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 3}, {"name": "OP", "bits": 2, "attr": ["rw"], "rotate": 0}, {"bits": 2}, {"name": "PARTITION", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 7}, {"name": "NUM", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name                             |
|:------:|:------:|:-------:|:---------------------------------|
| 31:26  |        |         | Reserved                         |
| 25:16  |   rw   |   0x0   | [NUM](#control--num)             |
|  15:9  |        |         | Reserved                         |
|   8    |   rw   |   0x0   | [PARTITION](#control--partition) |
|  7:6   |        |         | Reserved                         |
|  5:4   |   rw   |   0x0   | [OP](#control--op)               |
|  3:1   |        |         | Reserved                         |
|   0    |   rw   |   0x0   | [START](#control--start)         |

### CONTROL . NUM
One fewer than the number of bus words the RRAM operation should read or write.
For write operations, the number of bus words must be a multiple of 4.
For example, to read 10 words, software should program this field with the value 9.
To write 16 words, the software should program this field to 15.

### CONTROL . PARTITION
When doing a read or write operation, selects either info or data partition for operation.
When 0, select data partition - this is the portion of RRAM that is accessible both by the host and by the controller.
When 1, select info partition - this is the portion of RRAM that is only accessible by the controller.

### CONTROL . OP
RRAM operation selection

| Value   | Name    | Description                                                                                                                                  |
|:--------|:--------|:---------------------------------------------------------------------------------------------------------------------------------------------|
| 0x0     | Read    | RRAM Read. Read desired number of RRAM words.                                                                                                |
| 0x1     | Write   | RRAM write. Write desired number of RRAM words.                                                                                              |
| 0x2     | Rewrite | This operation reads a specific location and writes it back to the RRAM with the intention to fix errors that occured in the RRAM over time. |

Other values are reserved.

### CONTROL . START
Start RRAM transaction.
This bit shall only be set at the same time or after the other fields of the [`CONTROL`](#control) register and [`ADDR`](#addr) have been programmed.

## ADDR
Address for RRAM operation
- Offset: `0x24`
- Reset default: `0x0`
- Reset mask: `0x1fffff`
- Register enable: [`CTRL_REGWEN`](#ctrl_regwen)

### Fields

```wavejson
{"reg": [{"name": "START", "bits": 21, "attr": ["rw"], "rotate": 0}, {"bits": 11}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                  |
|:------:|:------:|:-------:|:----------------------|
| 31:21  |        |         | Reserved              |
|  20:0  |   rw   |   0x0   | [START](#addr--start) |

### ADDR . START
Start address of a RRAM transaction.
This is a byte address relative to the RRAM only.
I.e., an address of 0 will access address 0 of the requested partition.

For read operations, the RRAM controller will truncate to the closest, lower word aligned address.
For example, if 0x13 is supplied, the controller will perform a read at address 0x10.

For write operations, the RRAM controller will truncate to the closest, lower RRAM-word (128b).
For example, if 0x2F is supplied, the controller will perform a write at address 0x20.

## REGION_CFG_REGWEN
Memory region registers configuration enable.
- Reset default: `0x1`
- Reset mask: `0x1`

### Instances

| Name                | Offset   |
|:--------------------|:---------|
| REGION_CFG_REGWEN_0 | 0x28     |
| REGION_CFG_REGWEN_1 | 0x2c     |
| REGION_CFG_REGWEN_2 | 0x30     |
| REGION_CFG_REGWEN_3 | 0x34     |
| REGION_CFG_REGWEN_4 | 0x38     |
| REGION_CFG_REGWEN_5 | 0x3c     |
| REGION_CFG_REGWEN_6 | 0x40     |
| REGION_CFG_REGWEN_7 | 0x44     |


### Fields

```wavejson
{"reg": [{"name": "REGION", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                 |
|:------:|:------:|:-------:|:-------------------------------------|
|  31:1  |        |         | Reserved                             |
|   0    |  rw0c  |   0x1   | [REGION](#region_cfg_regwen--region) |

### REGION_CFG_REGWEN . REGION
Region register write enable.  Once set to 0, it can longer be configured to 1

| Value   | Name           | Description                                          |
|:--------|:---------------|:-----------------------------------------------------|
| 0x0     | Region locked  | Region can no longer be configured until next reset. |
| 0x1     | Region enabled | Region can be configured.                            |


## MP_REGION_CFG
Memory property configuration for data partition
- Reset default: `0x99999`
- Reset mask: `0xfffff`
- Register enable: [`REGION_CFG_REGWEN`](#region_cfg_regwen)

### Instances

| Name            | Offset   |
|:----------------|:---------|
| MP_REGION_CFG_0 | 0x48     |
| MP_REGION_CFG_1 | 0x4c     |
| MP_REGION_CFG_2 | 0x50     |
| MP_REGION_CFG_3 | 0x54     |
| MP_REGION_CFG_4 | 0x58     |
| MP_REGION_CFG_5 | 0x5c     |
| MP_REGION_CFG_6 | 0x60     |
| MP_REGION_CFG_7 | 0x64     |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "RD_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "WR_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "SCRAMBLE_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ECC_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 12}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                                                                        |
|:------:|:------:|:-------:|:------------|:-------------------------------------------------------------------------------------------------------------------|
| 31:20  |        |         |             | Reserved                                                                                                           |
| 19:16  |   rw   |   0x9   | ECC_EN      | Region is integrity checked and reliability ECC enabled.                                                           |
| 15:12  |   rw   |   0x9   | SCRAMBLE_EN | Region is scramble enabled.                                                                                        |
|  11:8  |   rw   |   0x9   | WR_EN       | Region can be written.                                                                                             |
|  7:4   |   rw   |   0x9   | RD_EN       | Region can be read.                                                                                                |
|  3:0   |   rw   |   0x9   | EN          | Region enabled, following fields apply. If region is disabled, it is not matched against any incoming transaction. |

## MP_REGION
Memory base and size configuration for data partition
- Reset default: `0x0`
- Reset mask: `0xffffff`
- Register enable: [`REGION_CFG_REGWEN`](#region_cfg_regwen)

### Instances

| Name        | Offset   |
|:------------|:---------|
| MP_REGION_0 | 0x68     |
| MP_REGION_1 | 0x6c     |
| MP_REGION_2 | 0x70     |
| MP_REGION_3 | 0x74     |
| MP_REGION_4 | 0x78     |
| MP_REGION_5 | 0x7c     |
| MP_REGION_6 | 0x80     |
| MP_REGION_7 | 0x84     |


### Fields

```wavejson
{"reg": [{"name": "BASE", "bits": 12, "attr": ["rw"], "rotate": 0}, {"name": "SIZE", "bits": 12, "attr": ["rw"], "rotate": 0}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                             |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:24  |        |         |        | Reserved                                                                                                                                                                                |
| 23:12  |   rw   |   0x0   | SIZE   | Region size in number of pages. For example, if base is 0 and size is 1, then the region is defined by page 0. If base is 0 and size is 2, then the region is defined by pages 0 and 1. |
|  11:0  |   rw   |   0x0   | BASE   | Region base page. Note the granularity is page, not byte or word.                                                                                                                       |

## DEFAULT_REGION
Default region properties
- Offset: `0x88`
- Reset default: `0x9999`
- Reset mask: `0xffff`

### Fields

```wavejson
{"reg": [{"name": "RD_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "WR_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "SCRAMBLE_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ECC_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                 |
|:------:|:------:|:-------:|:------------|:------------------------------------------------------------|
| 31:16  |        |         |             | Reserved                                                    |
| 15:12  |   rw   |   0x9   | ECC_EN      | Region is ECC enabled (both integrity and reliability ECC). |
|  11:8  |   rw   |   0x9   | SCRAMBLE_EN | Region is scramble enabled.                                 |
|  7:4   |   rw   |   0x9   | WR_EN       | Region can be written                                       |
|  3:0   |   rw   |   0x9   | RD_EN       | Region can be read                                          |

## INFO_REGWEN
Memory region registers configuration enable.
- Reset default: `0x1`
- Reset mask: `0x1`

### Instances

| Name          | Offset   |
|:--------------|:---------|
| INFO_REGWEN_0 | 0x8c     |
| INFO_REGWEN_1 | 0x90     |
| INFO_REGWEN_2 | 0x94     |
| INFO_REGWEN_3 | 0x98     |
| INFO_REGWEN_4 | 0x9c     |
| INFO_REGWEN_5 | 0xa0     |
| INFO_REGWEN_6 | 0xa4     |
| INFO_REGWEN_7 | 0xa8     |


### Fields

```wavejson
{"reg": [{"name": "REGION", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                           |
|:------:|:------:|:-------:|:-------------------------------|
|  31:1  |        |         | Reserved                       |
|   0    |  rw0c  |   0x1   | [REGION](#info_regwen--region) |

### INFO_REGWEN . REGION
Info page write enable.
Once set to 0, it can longer be configured to 1.

| Value   | Name         | Description                                          |
|:--------|:-------------|:-----------------------------------------------------|
| 0x0     | Page locked  | Region can no longer be configured until next reset. |
| 0x1     | Page enabled | Region can be configured.                            |


## INFO_PAGE_CFG
Memory property configuration for info partition.
Unlike data partition, each page is individually configured.
- Reset default: `0x99999`
- Reset mask: `0xfffff`
- Register enable: [`INFO_REGWEN`](#info_regwen)

### Instances

| Name            | Offset   |
|:----------------|:---------|
| INFO_PAGE_CFG_0 | 0xac     |
| INFO_PAGE_CFG_1 | 0xb0     |
| INFO_PAGE_CFG_2 | 0xb4     |
| INFO_PAGE_CFG_3 | 0xb8     |
| INFO_PAGE_CFG_4 | 0xbc     |
| INFO_PAGE_CFG_5 | 0xc0     |
| INFO_PAGE_CFG_6 | 0xc4     |
| INFO_PAGE_CFG_7 | 0xc8     |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "RD_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "WR_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "SCRAMBLE_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ECC_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 12}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                 |
|:------:|:------:|:-------:|:------------|:------------------------------------------------------------|
| 31:20  |        |         |             | Reserved                                                    |
| 19:16  |   rw   |   0x9   | ECC_EN      | Region is ECC enabled (both integrity and reliability ECC). |
| 15:12  |   rw   |   0x9   | SCRAMBLE_EN | Region is scramble enabled.                                 |
|  11:8  |   rw   |   0x9   | WR_EN       | Region can be written.                                      |
|  7:4   |   rw   |   0x9   | RD_EN       | Region can be read.                                         |
|  3:0   |   rw   |   0x9   | EN          | Region is enabled, the following fields apply.              |

## HW_INFO_CFG_OVERRIDE
HW interface info configuration rule overrides
- Offset: `0xcc`
- Reset default: `0x99`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "SCRAMBLE_DIS", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ECC_DIS", "bits": 4, "attr": ["rw"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                                                                                                                                                                                                         |
|:------:|:------:|:-------:|:-------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:8  |        |         |              | Reserved                                                                                                                                                                                                                            |
|  7:4   |   rw   |   0x9   | ECC_DIS      | The hardwired hardware info configuration rules for ECC enable are logically AND'd with this field. If the hardware rules hardwires ECC to enable, we can disable via software if needed. By default this field is false.           |
|  3:0   |   rw   |   0x9   | SCRAMBLE_DIS | The hardwired hardware info configuration rules for scramble enable are logically AND'd with this field. If the hardware rules hardwires scramble to enable, we can disable via software if needed. By default this field is false. |

## OP_STATUS
RRAM Operation Status
- Offset: `0xd0`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "done", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "err", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                   |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------------|
|  31:2  |        |         |        | Reserved                                                                                      |
|   1    |   rw   |   0x0   | err    | RRAM operation error. Set by HW, cleared by SW. See [`ERR_CODE`](#err_code) for more details. |
|   0    |   rw   |   0x0   | done   | RRAM operation done. Set by HW, cleared by SW                                                 |

## STATUS
RRAM Controller Status
- Offset: `0xd4`
- Reset default: `0xa`
- Reset mask: `0x3f`

### Fields

```wavejson
{"reg": [{"name": "rd_full", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "rd_empty", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "wr_full", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "wr_empty", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "init_done", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "keys_valid", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 26}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                       |
|:------:|:------:|:-------:|:-----------|:--------------------------------------------------|
|  31:6  |        |         |            | Reserved                                          |
|   5    |   ro   |   0x0   | keys_valid | RRAM controller scrambling keys are loaded        |
|   4    |   ro   |   0x0   | init_done  | RRAM controller is initilized                     |
|   3    |   ro   |   0x1   | wr_empty   | RRAM write FIFO empty, software must provide data |
|   2    |   ro   |   0x0   | wr_full    | RRAM write FIFO full                              |
|   1    |   ro   |   0x1   | rd_empty   | RRAM read FIFO empty                              |
|   0    |   ro   |   0x0   | rd_full    | RRAM read FIFO full, software must consume data   |

## ERR_CODE
RRAM error code register.
This register tabulates detailed error status of the RRAM.
This is separate from [`OP_STATUS`](#op_status), which is used to indicate the current state of the software initiated RRAM operation.

Note, all errors in this register are considered recoverable errors, i.e., errors that could have been generated by software.
- Offset: `0xd8`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "op_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "mp_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "rd_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "wr_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                                                                                     |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:4  |        |         |        | Reserved                                                                                                                                                                                                                                                        |
|   3    |  rw1c  |   0x0   | wr_err | RRAM write has an error. This could be a write integrity error, see [`STD_FAULT_STATUS.`](#std_fault_status) This is a synchronous error.                                                                                                                       |
|   2    |  rw1c  |   0x0   | rd_err | RRAM read has an error. This could be a reliability ECC error or integrity error encountered during a software issued controller read, see [`STD_FAULT_STATUS.`](#std_fault_status) See [`ERR_ADDR`](#err_addr) for exact address. This is a synchronous error. |
|   1    |  rw1c  |   0x0   | mp_err | RRAM access has encountered an access permission error. Please see [`ERR_ADDR`](#err_addr) for exact address. This is a synchronous error.                                                                                                                      |
|   0    |  rw1c  |   0x0   | op_err | Software has supplied an undefined operation. See [`CONTROL.OP`](#control) for list of valid operations.                                                                                                                                                        |

## STD_FAULT_STATUS
This register tabulates standard fault status of the RRAM.

These represent errors that occur in the standard structures of the design.
For example fsm integrity, counter integrity and tlul integrity.
- Offset: `0xdc`
- Reset default: `0x0`
- Reset mask: `0x1fff`

### Fields

```wavejson
{"reg": [{"name": "reg_intg_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "lcmgr_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "lcmgr_intg_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "otp_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "otp_intg_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "phy_wr_intg_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "phy_fifo_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "phy_fsm_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "phy_cnt_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "phy_arb_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ctrl_fsm_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ctrl_cnt_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ctrl_fifo_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 19}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name            | Description                                                                                                                                                                              |
|:------:|:------:|:-------:|:----------------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:13  |        |         |                 | Reserved                                                                                                                                                                                 |
|   12   |   ro   |   0x0   | ctrl_fifo_err   | RRAM controller write fifo has encountered an error.                                                                                                                                     |
|   11   |   ro   |   0x0   | ctrl_cnt_err    | RRAM controller read/write has encountered a count error.                                                                                                                                |
|   10   |   ro   |   0x0   | ctrl_fsm_err    | Any of the arbiter or rd/wr control FSMs have encountered a sparse encoding error.                                                                                                       |
|   9    |   ro   |   0x0   | phy_arb_err     | A RRAM phy arbiter has encountered an error.                                                                                                                                             |
|   8    |   ro   |   0x0   | phy_cnt_err     | A RRAM phy wr/read has encountered a count error.                                                                                                                                        |
|   7    |   ro   |   0x0   | phy_fsm_err     | A RRAM phy fsm has encountered a sparse encoding error.                                                                                                                                  |
|   6    |   ro   |   0x0   | phy_fifo_err    | A RRAM phy fifo has encountered a count error.                                                                                                                                           |
|   5    |   ro   |   0x0   | phy_wr_intg_err | The RRAM phy controller encountered a write data transmission integrity error.                                                                                                           |
|   4    |   ro   |   0x0   | otp_intg_err    | The otp interface has encountered a transmission integrity error. This is an integrity error on the generated integrity during an OTP read.                                              |
|   3    |   ro   |   0x0   | otp_err         | The otp interface has encountered a fatal error. The error is either an FSM sparse encoding error or a count error.                                                                      |
|   2    |   ro   |   0x0   | lcmgr_intg_err  | The life cycle management interface has encountered a transmission integrity error. This is an integrity error on the generated integrity during a life cycle management interface read. |
|   1    |   ro   |   0x0   | lcmgr_err       | The life cycle management interface has encountered a fatal error. The error is either an FSM sparse encoding error or a count error.                                                    |
|   0    |   ro   |   0x0   | reg_intg_err    | The RRAM controller encountered a register integrity error.                                                                                                                              |

## FAULT_STATUS
This register tabulates customized fault status of the RRAM.

These are errors that are impossible to have been caused by software or unrecoverable in nature.

All errors except for multi-bit ECC errors ([`FAULT_STATUS.PHY_RELBL_ERR`](#fault_status)).
Once set, they remain set until reset.
- Offset: `0xe0`
- Reset default: `0x0`
- Reset mask: `0x3fff`

### Fields

```wavejson
{"reg": [{"name": "lcmgr_op_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "lcmgr_mp_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "lcmgr_rd_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "lcmgr_wr_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "otp_op_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "otp_mp_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "otp_rd_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "otp_wr_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "seed_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "phy_relbl_err", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "phy_rd_intg_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "phy_rd_ctrl_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "spurious_done", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "host_gnt_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 18}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name                                              |
|:------:|:------:|:-------:|:--------------------------------------------------|
| 31:14  |        |         | Reserved                                          |
|   13   |   ro   |   0x0   | [host_gnt_err](#fault_status--host_gnt_err)       |
|   12   |   ro   |   0x0   | [spurious_done](#fault_status--spurious_done)     |
|   11   |   ro   |   0x0   | [phy_rd_ctrl_err](#fault_status--phy_rd_ctrl_err) |
|   10   |   ro   |   0x0   | [phy_rd_intg_err](#fault_status--phy_rd_intg_err) |
|   9    |  rw0c  |   0x0   | [phy_relbl_err](#fault_status--phy_relbl_err)     |
|   8    |   ro   |   0x0   | [seed_err](#fault_status--seed_err)               |
|   7    |   ro   |   0x0   | [otp_wr_err](#fault_status--otp_wr_err)           |
|   6    |   ro   |   0x0   | [otp_rd_err](#fault_status--otp_rd_err)           |
|   5    |   ro   |   0x0   | [otp_mp_err](#fault_status--otp_mp_err)           |
|   4    |   ro   |   0x0   | [otp_op_err](#fault_status--otp_op_err)           |
|   3    |   ro   |   0x0   | [lcmgr_wr_err](#fault_status--lcmgr_wr_err)       |
|   2    |   ro   |   0x0   | [lcmgr_rd_err](#fault_status--lcmgr_rd_err)       |
|   1    |   ro   |   0x0   | [lcmgr_mp_err](#fault_status--lcmgr_mp_err)       |
|   0    |   ro   |   0x0   | [lcmgr_op_err](#fault_status--lcmgr_op_err)       |

### FAULT_STATUS . host_gnt_err
A host transaction was granted with illegal properties.

### FAULT_STATUS . spurious_done
The RRAM emitted an unexpected acknowledgement.

### FAULT_STATUS . phy_rd_ctrl_err
The RRAM phy controller detected one of the following errors:
- a mismatch of command request integrity and command response integrity.
- a spurious valid.
- a spurious rram read request.

### FAULT_STATUS . phy_rd_intg_err
The RRAM phy controller encountered an integrity error. The shadow response was not identical to the original response.

### FAULT_STATUS . phy_relbl_err
The RRAM macro encountered a reliability ECC error that cannot be corrected.

Note that this error bit can be cleared to allow firmware dealing with multi-bit ECC errors during firmware selection and verification.
After passing this stage, it is recommended that firmware classifies the corresponding alert as fatal on the receiver end, i.e, inside the alert handler.

### FAULT_STATUS . seed_err
The seed reading process encountered an unexpected error.

### FAULT_STATUS . otp_wr_err
The RRAM OTP interface encountered a write error.
This could be a write integrity error, see [`STD_FAULT_STATUS`](#std_fault_status) for more details.

### FAULT_STATUS . otp_rd_err
The RRAM OTP interface encountered a read error.
This could be a reliability ECC error or an integrity ECC error encountered during a read, see [`STD_FAULT_STATUS`](#std_fault_status) for more details.

### FAULT_STATUS . otp_mp_err
The RRAM OTP interface encountered a memory permission error.

### FAULT_STATUS . otp_op_err
The RRAM OTP interface has supplied an undefined operation.
See [`CONTROL.OP`](#control) for list of valid operations.

### FAULT_STATUS . lcmgr_wr_err
The RRAM life cycle management interface encountered a write error.
This could be a write integrity error, see [`STD_FAULT_STATUS`](#std_fault_status) for more details.

### FAULT_STATUS . lcmgr_rd_err
The RRAM life cycle management interface encountered a read error.
This could be a reliability ECC error or an integrity ECC error encountered during a read, see [`STD_FAULT_STATUS`](#std_fault_status) for more details.

### FAULT_STATUS . lcmgr_mp_err
The RRAM life cycle management interface encountered a memory permission error.

### FAULT_STATUS . lcmgr_op_err
The RRAM life cycle management interface has supplied an undefined operation.
See [`CONTROL.OP`](#control) for list of valid operations.

## ERR_ADDR
Synchronous error address
- Offset: `0xe4`
- Reset default: `0x0`
- Reset mask: `0x1fffff`

### Fields

```wavejson
{"reg": [{"name": "ERR_ADDR", "bits": 21, "attr": ["ro"], "rotate": 0}, {"bits": 11}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description   |
|:------:|:------:|:-------:|:---------|:--------------|
| 31:21  |        |         |          | Reserved      |
|  20:0  |   ro   |   0x0   | ERR_ADDR |               |

## CORR_ERR_CNT
Count of correctable ECC errors
- Offset: `0xe8`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "val", "bits": 8, "attr": ["rw"], "rotate": 0}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                             |
|:------:|:------:|:-------:|:-------|:----------------------------------------|
|  31:8  |        |         |        | Reserved                                |
|  7:0   |   rw   |   0x0   | val    | This count will not wrap when saturated |

## CORR_ERR_LOC
Last address that was successfully corrected
- Offset: `0xec`
- Reset default: `0x0`
- Reset mask: `0x11fffff`

### Fields

```wavejson
{"reg": [{"name": "addr", "bits": 21, "attr": ["ro"], "rotate": 0}, {"bits": 3}, {"name": "part", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 7}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                           |
|:------:|:------:|:-------:|:-------|:--------------------------------------|
| 31:25  |        |         |        | Reserved                              |
|   24   |   ro   |   0x0   | part   | Last successfully corrected partition |
| 23:21  |        |         |        | Reserved                              |
|  20:0  |   ro   |   0x0   | addr   | Last successfully corrected address   |

## PHY_STATUS
RRAM Phy Status
- Offset: `0xf0`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "wr_busy", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "init_done", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                         |
|:------:|:------:|:-------:|:----------|:----------------------------------------------------|
|  31:2  |        |         |           | Reserved                                            |
|   1    |   ro   |   0x0   | init_done | RRAM phy controller is initialized (including RRAM) |
|   0    |   ro   |   0x0   | wr_busy   | RRAM phy is currently writing to RRAM               |

## SCRATCH
RRAM Controller Scratch
- Offset: `0xf4`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "data", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                      |
|:------:|:------:|:-------:|:-------|:---------------------------------|
|  31:0  |   rw   |   0x0   | data   | RRAM controller scratch register |

## FIFO_LVL
Programmable depth where FIFOs should generate interrupts
- Offset: `0xf8`
- Reset default: `0xf0f`
- Reset mask: `0x1f1f`

### Fields

```wavejson
{"reg": [{"name": "WR", "bits": 5, "attr": ["rw"], "rotate": 0}, {"bits": 3}, {"name": "RD", "bits": 5, "attr": ["rw"], "rotate": 0}, {"bits": 19}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                         |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------------------------------------------------------------------------------|
| 31:13  |        |         |        | Reserved                                                                                                                            |
|  12:8  |   rw   |   0xf   | RD     | When the read FIFO fills to this level, trigger an interrupt. Default value is set such that interrupt does not trigger at reset.   |
|  7:5   |        |         |        | Reserved                                                                                                                            |
|  4:0   |   rw   |   0xf   | WR     | When the write FIFO drains to this level, trigger an interrupt. Default value is set such that interrupt does not trigger at reset. |

## FIFO_CLR
Clears RRAM controller FIFOs
- Offset: `0xfc`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "WR", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "RD", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                               |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------|
|  31:2  |        |         |        | Reserved                                                  |
|   1    |   wo   |   0x0   | RD     | This will clear the content of the controller read fifo.  |
|   0    |   wo   |   0x0   | WR     | This will clear the content of the controller write fifo. |

## CURR_FIFO_LVL
Current write and read fifo level
- Offset: `0x100`
- Reset default: `0x0`
- Reset mask: `0x1f1f`

### Fields

```wavejson
{"reg": [{"name": "WR", "bits": 5, "attr": ["ro"], "rotate": 0}, {"bits": 3}, {"name": "RD", "bits": 5, "attr": ["ro"], "rotate": 0}, {"bits": 19}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description               |
|:------:|:------:|:-------:|:-------|:--------------------------|
| 31:13  |        |         |        | Reserved                  |
|  12:8  |   ro   |   0x0   | RD     | Current read fifo level.  |
|  7:5   |        |         |        | Reserved                  |
|  4:0   |   ro   |   0x0   | WR     | Current write fifo level. |

## wr_fifo
RRAM write FIFO.

The FIFO is 4 entries of 4B words. This FIFO can only be programmed by software after a write operation has been initiated via the [`CONTROL`](#control) register.
This ensures accidental programming of the write FIFO cannot lock up the system.

- Word Aligned Offset Range: `0x104`to`0x104`
- Size (words): `1`
- Access: `wo`
- Byte writes are *not* supported.

## rd_fifo
RRAM read FIFO.

The FIFO is 16 entries of 4B words.

- Word Aligned Offset Range: `0x108`to`0x108`
- Size (words): `1`
- Access: `ro`
- Byte writes are *not* supported.


<!-- END CMDGEN -->
