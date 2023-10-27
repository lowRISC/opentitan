# Registers

The flash protocol controller maintains two separate access windows for the FIFO.
It is implemented this way because the access window supports transaction back-pressure should the FIFO become full (in case of write) or empty (in case of read).

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/flash_ctrl/data/flash_ctrl.hjson -->
## Summary of the **`core`** interface's registers

| Name                                                         | Offset   |   Length | Description                                                   |
|:-------------------------------------------------------------|:---------|---------:|:--------------------------------------------------------------|
| flash_ctrl.[`INTR_STATE`](#intr_state)                       | 0x0      |        4 | Interrupt State Register                                      |
| flash_ctrl.[`INTR_ENABLE`](#intr_enable)                     | 0x4      |        4 | Interrupt Enable Register                                     |
| flash_ctrl.[`INTR_TEST`](#intr_test)                         | 0x8      |        4 | Interrupt Test Register                                       |
| flash_ctrl.[`ALERT_TEST`](#alert_test)                       | 0xc      |        4 | Alert Test Register                                           |
| flash_ctrl.[`DIS`](#dis)                                     | 0x10     |        4 | Disable flash functionality                                   |
| flash_ctrl.[`EXEC`](#exec)                                   | 0x14     |        4 | Controls whether flash can be used for code execution fetches |
| flash_ctrl.[`INIT`](#init)                                   | 0x18     |        4 | Controller init register                                      |
| flash_ctrl.[`CTRL_REGWEN`](#ctrl_regwen)                     | 0x1c     |        4 | Controls the configurability of the !!CONTROL register.       |
| flash_ctrl.[`CONTROL`](#control)                             | 0x20     |        4 | Control register                                              |
| flash_ctrl.[`ADDR`](#addr)                                   | 0x24     |        4 | Address for flash operation                                   |
| flash_ctrl.[`PROG_TYPE_EN`](#prog_type_en)                   | 0x28     |        4 | Enable different program types                                |
| flash_ctrl.[`ERASE_SUSPEND`](#erase_suspend)                 | 0x2c     |        4 | Suspend erase                                                 |
| flash_ctrl.[`REGION_CFG_REGWEN_0`](#region_cfg_regwen)       | 0x30     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`REGION_CFG_REGWEN_1`](#region_cfg_regwen)       | 0x34     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`REGION_CFG_REGWEN_2`](#region_cfg_regwen)       | 0x38     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`REGION_CFG_REGWEN_3`](#region_cfg_regwen)       | 0x3c     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`REGION_CFG_REGWEN_4`](#region_cfg_regwen)       | 0x40     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`REGION_CFG_REGWEN_5`](#region_cfg_regwen)       | 0x44     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`REGION_CFG_REGWEN_6`](#region_cfg_regwen)       | 0x48     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`REGION_CFG_REGWEN_7`](#region_cfg_regwen)       | 0x4c     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`MP_REGION_CFG_0`](#mp_region_cfg)               | 0x50     |        4 | Memory property configuration for data partition              |
| flash_ctrl.[`MP_REGION_CFG_1`](#mp_region_cfg)               | 0x54     |        4 | Memory property configuration for data partition              |
| flash_ctrl.[`MP_REGION_CFG_2`](#mp_region_cfg)               | 0x58     |        4 | Memory property configuration for data partition              |
| flash_ctrl.[`MP_REGION_CFG_3`](#mp_region_cfg)               | 0x5c     |        4 | Memory property configuration for data partition              |
| flash_ctrl.[`MP_REGION_CFG_4`](#mp_region_cfg)               | 0x60     |        4 | Memory property configuration for data partition              |
| flash_ctrl.[`MP_REGION_CFG_5`](#mp_region_cfg)               | 0x64     |        4 | Memory property configuration for data partition              |
| flash_ctrl.[`MP_REGION_CFG_6`](#mp_region_cfg)               | 0x68     |        4 | Memory property configuration for data partition              |
| flash_ctrl.[`MP_REGION_CFG_7`](#mp_region_cfg)               | 0x6c     |        4 | Memory property configuration for data partition              |
| flash_ctrl.[`MP_REGION_0`](#mp_region)                       | 0x70     |        4 | Memory base and size configuration for data partition         |
| flash_ctrl.[`MP_REGION_1`](#mp_region)                       | 0x74     |        4 | Memory base and size configuration for data partition         |
| flash_ctrl.[`MP_REGION_2`](#mp_region)                       | 0x78     |        4 | Memory base and size configuration for data partition         |
| flash_ctrl.[`MP_REGION_3`](#mp_region)                       | 0x7c     |        4 | Memory base and size configuration for data partition         |
| flash_ctrl.[`MP_REGION_4`](#mp_region)                       | 0x80     |        4 | Memory base and size configuration for data partition         |
| flash_ctrl.[`MP_REGION_5`](#mp_region)                       | 0x84     |        4 | Memory base and size configuration for data partition         |
| flash_ctrl.[`MP_REGION_6`](#mp_region)                       | 0x88     |        4 | Memory base and size configuration for data partition         |
| flash_ctrl.[`MP_REGION_7`](#mp_region)                       | 0x8c     |        4 | Memory base and size configuration for data partition         |
| flash_ctrl.[`DEFAULT_REGION`](#default_region)               | 0x90     |        4 | Default region properties                                     |
| flash_ctrl.[`BANK0_INFO0_REGWEN_0`](#bank0_info0_regwen)     | 0x94     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK0_INFO0_REGWEN_1`](#bank0_info0_regwen)     | 0x98     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK0_INFO0_REGWEN_2`](#bank0_info0_regwen)     | 0x9c     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK0_INFO0_REGWEN_3`](#bank0_info0_regwen)     | 0xa0     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK0_INFO0_REGWEN_4`](#bank0_info0_regwen)     | 0xa4     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK0_INFO0_REGWEN_5`](#bank0_info0_regwen)     | 0xa8     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK0_INFO0_REGWEN_6`](#bank0_info0_regwen)     | 0xac     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK0_INFO0_REGWEN_7`](#bank0_info0_regwen)     | 0xb0     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK0_INFO0_REGWEN_8`](#bank0_info0_regwen)     | 0xb4     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK0_INFO0_REGWEN_9`](#bank0_info0_regwen)     | 0xb8     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK0_INFO0_PAGE_CFG_0`](#bank0_info0_page_cfg) | 0xbc     |        4 | Memory property configuration for info partition in bank0,    |
| flash_ctrl.[`BANK0_INFO0_PAGE_CFG_1`](#bank0_info0_page_cfg) | 0xc0     |        4 | Memory property configuration for info partition in bank0,    |
| flash_ctrl.[`BANK0_INFO0_PAGE_CFG_2`](#bank0_info0_page_cfg) | 0xc4     |        4 | Memory property configuration for info partition in bank0,    |
| flash_ctrl.[`BANK0_INFO0_PAGE_CFG_3`](#bank0_info0_page_cfg) | 0xc8     |        4 | Memory property configuration for info partition in bank0,    |
| flash_ctrl.[`BANK0_INFO0_PAGE_CFG_4`](#bank0_info0_page_cfg) | 0xcc     |        4 | Memory property configuration for info partition in bank0,    |
| flash_ctrl.[`BANK0_INFO0_PAGE_CFG_5`](#bank0_info0_page_cfg) | 0xd0     |        4 | Memory property configuration for info partition in bank0,    |
| flash_ctrl.[`BANK0_INFO0_PAGE_CFG_6`](#bank0_info0_page_cfg) | 0xd4     |        4 | Memory property configuration for info partition in bank0,    |
| flash_ctrl.[`BANK0_INFO0_PAGE_CFG_7`](#bank0_info0_page_cfg) | 0xd8     |        4 | Memory property configuration for info partition in bank0,    |
| flash_ctrl.[`BANK0_INFO0_PAGE_CFG_8`](#bank0_info0_page_cfg) | 0xdc     |        4 | Memory property configuration for info partition in bank0,    |
| flash_ctrl.[`BANK0_INFO0_PAGE_CFG_9`](#bank0_info0_page_cfg) | 0xe0     |        4 | Memory property configuration for info partition in bank0,    |
| flash_ctrl.[`BANK0_INFO1_REGWEN`](#bank0_info1_regwen)       | 0xe4     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK0_INFO1_PAGE_CFG`](#bank0_info1_page_cfg)   | 0xe8     |        4 | Memory property configuration for info partition in bank0,    |
| flash_ctrl.[`BANK0_INFO2_REGWEN_0`](#bank0_info2_regwen)     | 0xec     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK0_INFO2_REGWEN_1`](#bank0_info2_regwen)     | 0xf0     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK0_INFO2_PAGE_CFG_0`](#bank0_info2_page_cfg) | 0xf4     |        4 | Memory property configuration for info partition in bank0,    |
| flash_ctrl.[`BANK0_INFO2_PAGE_CFG_1`](#bank0_info2_page_cfg) | 0xf8     |        4 | Memory property configuration for info partition in bank0,    |
| flash_ctrl.[`BANK1_INFO0_REGWEN_0`](#bank1_info0_regwen)     | 0xfc     |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK1_INFO0_REGWEN_1`](#bank1_info0_regwen)     | 0x100    |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK1_INFO0_REGWEN_2`](#bank1_info0_regwen)     | 0x104    |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK1_INFO0_REGWEN_3`](#bank1_info0_regwen)     | 0x108    |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK1_INFO0_REGWEN_4`](#bank1_info0_regwen)     | 0x10c    |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK1_INFO0_REGWEN_5`](#bank1_info0_regwen)     | 0x110    |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK1_INFO0_REGWEN_6`](#bank1_info0_regwen)     | 0x114    |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK1_INFO0_REGWEN_7`](#bank1_info0_regwen)     | 0x118    |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK1_INFO0_REGWEN_8`](#bank1_info0_regwen)     | 0x11c    |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK1_INFO0_REGWEN_9`](#bank1_info0_regwen)     | 0x120    |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK1_INFO0_PAGE_CFG_0`](#bank1_info0_page_cfg) | 0x124    |        4 | Memory property configuration for info partition in bank1,    |
| flash_ctrl.[`BANK1_INFO0_PAGE_CFG_1`](#bank1_info0_page_cfg) | 0x128    |        4 | Memory property configuration for info partition in bank1,    |
| flash_ctrl.[`BANK1_INFO0_PAGE_CFG_2`](#bank1_info0_page_cfg) | 0x12c    |        4 | Memory property configuration for info partition in bank1,    |
| flash_ctrl.[`BANK1_INFO0_PAGE_CFG_3`](#bank1_info0_page_cfg) | 0x130    |        4 | Memory property configuration for info partition in bank1,    |
| flash_ctrl.[`BANK1_INFO0_PAGE_CFG_4`](#bank1_info0_page_cfg) | 0x134    |        4 | Memory property configuration for info partition in bank1,    |
| flash_ctrl.[`BANK1_INFO0_PAGE_CFG_5`](#bank1_info0_page_cfg) | 0x138    |        4 | Memory property configuration for info partition in bank1,    |
| flash_ctrl.[`BANK1_INFO0_PAGE_CFG_6`](#bank1_info0_page_cfg) | 0x13c    |        4 | Memory property configuration for info partition in bank1,    |
| flash_ctrl.[`BANK1_INFO0_PAGE_CFG_7`](#bank1_info0_page_cfg) | 0x140    |        4 | Memory property configuration for info partition in bank1,    |
| flash_ctrl.[`BANK1_INFO0_PAGE_CFG_8`](#bank1_info0_page_cfg) | 0x144    |        4 | Memory property configuration for info partition in bank1,    |
| flash_ctrl.[`BANK1_INFO0_PAGE_CFG_9`](#bank1_info0_page_cfg) | 0x148    |        4 | Memory property configuration for info partition in bank1,    |
| flash_ctrl.[`BANK1_INFO1_REGWEN`](#bank1_info1_regwen)       | 0x14c    |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK1_INFO1_PAGE_CFG`](#bank1_info1_page_cfg)   | 0x150    |        4 | Memory property configuration for info partition in bank1,    |
| flash_ctrl.[`BANK1_INFO2_REGWEN_0`](#bank1_info2_regwen)     | 0x154    |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK1_INFO2_REGWEN_1`](#bank1_info2_regwen)     | 0x158    |        4 | Memory region registers configuration enable.                 |
| flash_ctrl.[`BANK1_INFO2_PAGE_CFG_0`](#bank1_info2_page_cfg) | 0x15c    |        4 | Memory property configuration for info partition in bank1,    |
| flash_ctrl.[`BANK1_INFO2_PAGE_CFG_1`](#bank1_info2_page_cfg) | 0x160    |        4 | Memory property configuration for info partition in bank1,    |
| flash_ctrl.[`HW_INFO_CFG_OVERRIDE`](#hw_info_cfg_override)   | 0x164    |        4 | HW interface info configuration rule overrides                |
| flash_ctrl.[`BANK_CFG_REGWEN`](#bank_cfg_regwen)             | 0x168    |        4 | Bank configuration registers configuration enable.            |
| flash_ctrl.[`MP_BANK_CFG_SHADOWED`](#MP_BANK_CFG_SHADOWED)   | 0x16c    |        4 | Memory properties bank configuration                          |
| flash_ctrl.[`OP_STATUS`](#op_status)                         | 0x170    |        4 | Flash Operation Status                                        |
| flash_ctrl.[`STATUS`](#status)                               | 0x174    |        4 | Flash Controller Status                                       |
| flash_ctrl.[`DEBUG_STATE`](#debug_state)                     | 0x178    |        4 | Current flash fsm state                                       |
| flash_ctrl.[`ERR_CODE`](#err_code)                           | 0x17c    |        4 | Flash error code register.                                    |
| flash_ctrl.[`STD_FAULT_STATUS`](#std_fault_status)           | 0x180    |        4 | This register tabulates standard fault status of the flash.   |
| flash_ctrl.[`FAULT_STATUS`](#fault_status)                   | 0x184    |        4 | This register tabulates customized fault status of the flash. |
| flash_ctrl.[`ERR_ADDR`](#err_addr)                           | 0x188    |        4 | Synchronous error address                                     |
| flash_ctrl.[`ECC_SINGLE_ERR_CNT`](#ECC_SINGLE_ERR_CNT)       | 0x18c    |        4 | Total number of single bit ECC error count                    |
| flash_ctrl.[`ECC_SINGLE_ERR_ADDR_0`](#ecc_single_err_addr)   | 0x190    |        4 | Latest address of ECC single err                              |
| flash_ctrl.[`ECC_SINGLE_ERR_ADDR_1`](#ecc_single_err_addr)   | 0x194    |        4 | Latest address of ECC single err                              |
| flash_ctrl.[`PHY_ALERT_CFG`](#phy_alert_cfg)                 | 0x198    |        4 | Phy alert configuration                                       |
| flash_ctrl.[`PHY_STATUS`](#phy_status)                       | 0x19c    |        4 | Flash Phy Status                                              |
| flash_ctrl.[`Scratch`](#scratch)                             | 0x1a0    |        4 | Flash Controller Scratch                                      |
| flash_ctrl.[`FIFO_LVL`](#fifo_lvl)                           | 0x1a4    |        4 | Programmable depth where FIFOs should generate interrupts     |
| flash_ctrl.[`FIFO_RST`](#fifo_rst)                           | 0x1a8    |        4 | Reset for flash controller FIFOs                              |
| flash_ctrl.[`CURR_FIFO_LVL`](#curr_fifo_lvl)                 | 0x1ac    |        4 | Current program and read fifo depth                           |
| flash_ctrl.[`prog_fifo`](#prog_fifo)                         | 0x1b0    |        4 | Flash program FIFO.                                           |
| flash_ctrl.[`rd_fifo`](#rd_fifo)                             | 0x1b4    |        4 | Flash read FIFO.                                              |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x3f`

### Fields

```wavejson
{"reg": [{"name": "prog_empty", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "prog_lvl", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "rd_full", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "rd_lvl", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "op_done", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "corr_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 26}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                   |
|:------:|:------:|:-------:|:-----------|:------------------------------|
|  31:6  |        |         |            | Reserved                      |
|   5    |  rw1c  |   0x0   | corr_err   | Correctable error encountered |
|   4    |  rw1c  |   0x0   | op_done    | Operation complete            |
|   3    |  rw1c  |   0x0   | rd_lvl     | Read FIFO filled to level     |
|   2    |  rw1c  |   0x0   | rd_full    | Read FIFO full                |
|   1    |  rw1c  |   0x0   | prog_lvl   | Program FIFO drained to level |
|   0    |  rw1c  |   0x0   | prog_empty | Program FIFO empty            |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x3f`

### Fields

```wavejson
{"reg": [{"name": "prog_empty", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "prog_lvl", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rd_full", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rd_lvl", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "op_done", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "corr_err", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 26}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                          |
|:------:|:------:|:-------:|:-----------|:---------------------------------------------------------------------|
|  31:6  |        |         |            | Reserved                                                             |
|   5    |   rw   |   0x0   | corr_err   | Enable interrupt when [`INTR_STATE.corr_err`](#intr_state) is set.   |
|   4    |   rw   |   0x0   | op_done    | Enable interrupt when [`INTR_STATE.op_done`](#intr_state) is set.    |
|   3    |   rw   |   0x0   | rd_lvl     | Enable interrupt when [`INTR_STATE.rd_lvl`](#intr_state) is set.     |
|   2    |   rw   |   0x0   | rd_full    | Enable interrupt when [`INTR_STATE.rd_full`](#intr_state) is set.    |
|   1    |   rw   |   0x0   | prog_lvl   | Enable interrupt when [`INTR_STATE.prog_lvl`](#intr_state) is set.   |
|   0    |   rw   |   0x0   | prog_empty | Enable interrupt when [`INTR_STATE.prog_empty`](#intr_state) is set. |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x3f`

### Fields

```wavejson
{"reg": [{"name": "prog_empty", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "prog_lvl", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rd_full", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rd_lvl", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "op_done", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "corr_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 26}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                   |
|:------:|:------:|:-------:|:-----------|:--------------------------------------------------------------|
|  31:6  |        |         |            | Reserved                                                      |
|   5    |   wo   |   0x0   | corr_err   | Write 1 to force [`INTR_STATE.corr_err`](#intr_state) to 1.   |
|   4    |   wo   |   0x0   | op_done    | Write 1 to force [`INTR_STATE.op_done`](#intr_state) to 1.    |
|   3    |   wo   |   0x0   | rd_lvl     | Write 1 to force [`INTR_STATE.rd_lvl`](#intr_state) to 1.     |
|   2    |   wo   |   0x0   | rd_full    | Write 1 to force [`INTR_STATE.rd_full`](#intr_state) to 1.    |
|   1    |   wo   |   0x0   | prog_lvl   | Write 1 to force [`INTR_STATE.prog_lvl`](#intr_state) to 1.   |
|   0    |   wo   |   0x0   | prog_empty | Write 1 to force [`INTR_STATE.prog_empty`](#intr_state) to 1. |

## ALERT_TEST
Alert Test Register
- Offset: `0xc`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "recov_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_std_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_prim_flash_alert", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "recov_prim_flash_alert", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 240}}
```

|  Bits  |  Type  |  Reset  | Name                   | Description                                      |
|:------:|:------:|:-------:|:-----------------------|:-------------------------------------------------|
|  31:5  |        |         |                        | Reserved                                         |
|   4    |   wo   |   0x0   | recov_prim_flash_alert | Write 1 to trigger one alert event of this kind. |
|   3    |   wo   |   0x0   | fatal_prim_flash_alert | Write 1 to trigger one alert event of this kind. |
|   2    |   wo   |   0x0   | fatal_err              | Write 1 to trigger one alert event of this kind. |
|   1    |   wo   |   0x0   | fatal_std_err          | Write 1 to trigger one alert event of this kind. |
|   0    |   wo   |   0x0   | recov_err              | Write 1 to trigger one alert event of this kind. |

## DIS
Disable flash functionality
- Offset: `0x10`
- Reset default: `0x9`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 4, "attr": ["rw0c"], "rotate": 0}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name             |
|:------:|:------:|:-------:|:-----------------|
|  31:4  |        |         | Reserved         |
|  3:0   |  rw0c  |   0x9   | [VAL](#dis--val) |

### DIS . VAL
Disables flash functionality completely.
This is a shortcut mechanism used by the software to completely
kill flash in case of emergency.

Since this register is rw0c instead of rw, to disable, write any value in the form of
0xxx or xxx0, where x could be either 0 or 1.


## EXEC
Controls whether flash can be used for code execution fetches
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | EN     | A value of 0xa26a38f7 allows flash to be used for code execution. Any other value prevents code execution. |

## INIT
Controller init register
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 1, "attr": ["rw1s"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name              |
|:------:|:------:|:-------:|:------------------|
|  31:1  |        |         | Reserved          |
|   0    |  rw1s  |   0x0   | [VAL](#init--val) |

### INIT . VAL
Initializes the flash controller.

During the initialization process, the flash controller requests the address and data
scramble keys and reads out the root seeds stored in flash before allowing other usage
of the flash controller.

When the initialization sequence is complete, the flash read buffers are enabled
and turned on.

## CTRL_REGWEN
Controls the configurability of the [`CONTROL`](#control) register.

This register ensures the contents of [`CONTROL`](#control) cannot be changed by software once a flash
operation has begun.

It unlocks whenever the existing flash operation completes, regardless of success or error.
- Offset: `0x1c`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                                                                        |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                                                                                                                                                                           |
|   0    |   ro   |   0x1   | EN     | Configuration enable.  This bit defaults to 1 and is set to 0 by hardware when flash operation is initiated. When the controller completes the flash operation, this bit is set back to 1 to allow software configuration of [`CONTROL`](#control) |

## CONTROL
Control register
- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0xfff07f1`
- Register enable: [`CTRL_REGWEN`](#ctrl_regwen)

### Fields

```wavejson
{"reg": [{"name": "START", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 3}, {"name": "OP", "bits": 2, "attr": ["rw"], "rotate": 0}, {"name": "PROG_SEL", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ERASE_SEL", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "PARTITION_SEL", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "INFO_SEL", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 5}, {"name": "NUM", "bits": 12, "attr": ["rw"], "rotate": 0}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name                                     |
|:------:|:------:|:-------:|:-----------------------------------------|
| 31:28  |        |         | Reserved                                 |
| 27:16  |   rw   |   0x0   | [NUM](#control--num)                     |
| 15:11  |        |         | Reserved                                 |
|  10:9  |   rw   |   0x0   | [INFO_SEL](#control--info_sel)           |
|   8    |   rw   |   0x0   | [PARTITION_SEL](#control--partition_sel) |
|   7    |   rw   |   0x0   | [ERASE_SEL](#control--erase_sel)         |
|   6    |   rw   |   0x0   | [PROG_SEL](#control--prog_sel)           |
|  5:4   |   rw   |   0x0   | [OP](#control--op)                       |
|  3:1   |        |         | Reserved                                 |
|   0    |   rw   |   0x0   | [START](#control--start)                 |

### CONTROL . NUM
One fewer than the number of bus words the flash operation should read or program.
For example, to read 10 words, software should program this field with the value 9.

### CONTROL . INFO_SEL
Informational partions can have multiple types.

This field selects the info type to be accessed.

### CONTROL . PARTITION_SEL
When doing a read, program or page erase operation, selects either info or data partition for operation.
When 0, select data partition - this is the portion of flash that is accessible both by the host and by the controller.
When 1, select info partition - this is the portion of flash that is only accessible by the controller.

When doing a bank erase operation, selects info partition also for erase.
When 0, bank erase only erases data partition.
When 1, bank erase erases data partition and info partition.

### CONTROL . ERASE_SEL
Flash erase operation type selection

| Value   | Name       | Description           |
|:--------|:-----------|:----------------------|
| 0x0     | Page Erase | Erase 1 page of flash |
| 0x1     | Bank Erase | Erase 1 bank of flash |


### CONTROL . PROG_SEL
Flash program operation type selection

| Value   | Name           | Description                                                                                                        |
|:--------|:---------------|:-------------------------------------------------------------------------------------------------------------------|
| 0x0     | Normal program | Normal program operation to the flash                                                                              |
| 0x1     | Program repair | Repair program operation to the flash.  Whether this is actually supported depends on the underlying flash memory. |


### CONTROL . OP
Flash operation selection

| Value   | Name   | Description                                                          |
|:--------|:-------|:---------------------------------------------------------------------|
| 0x0     | Read   | Flash Read.  Read desired number of flash words                      |
| 0x1     | Prog   | Flash Program.  Program desired number of flash words                |
| 0x2     | Erase  | Flash Erase Operation.  See ERASE_SEL for details on erase operation |

Other values are reserved.

### CONTROL . START
Start flash transaction.  This bit shall only be set at the same time or after the other
fields of the [`CONTROL`](#control) register and [`ADDR`](#addr) have been programmed.

## ADDR
Address for flash operation
- Offset: `0x24`
- Reset default: `0x0`
- Reset mask: `0xfffff`
- Register enable: [`CTRL_REGWEN`](#ctrl_regwen)

### Fields

```wavejson
{"reg": [{"name": "START", "bits": 20, "attr": ["rw"], "rotate": 0}, {"bits": 12}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                  |
|:------:|:------:|:-------:|:----------------------|
| 31:20  |        |         | Reserved              |
|  19:0  |   rw   |   0x0   | [START](#addr--start) |

### ADDR . START
Start address of a flash transaction.  This is a byte address relative to the flash
only.  Ie, an address of 0 will access address 0 of the requested partition.

For read operations, the flash controller will truncate to the closest, lower word
aligned address.  For example, if 0x13 is supplied, the controller will perform a
read at address 0x10.

Program operations behave similarly, the controller does not have read modified write
support.

For page erases, the controller will truncate to the closest lower page aligned
address.  Similarly for bank erases, the controller will truncate to the closest
lower bank aligned address.

## PROG_TYPE_EN
Enable different program types
- Offset: `0x28`
- Reset default: `0x3`
- Reset mask: `0x3`
- Register enable: [`CTRL_REGWEN`](#ctrl_regwen)

### Fields

```wavejson
{"reg": [{"name": "NORMAL", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "REPAIR", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                |
|:------:|:------:|:-------:|:-------|:---------------------------|
|  31:2  |        |         |        | Reserved                   |
|   1    |  rw0c  |   0x1   | REPAIR | Repair prog type available |
|   0    |  rw0c  |   0x1   | NORMAL | Normal prog type available |

## ERASE_SUSPEND
Suspend erase
- Offset: `0x2c`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "REQ", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                       |
|:------:|:------:|:-------:|:-------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                                                                                                                          |
|   0    |   rw   |   0x0   | REQ    | When 1, request erase suspend. If no erase ongoing, the request is immediately cleared by hardware If erase ongoing, the request is fed to the flash_phy and cleared when the suspend is handled. |

## REGION_CFG_REGWEN
Memory region registers configuration enable.
- Reset default: `0x1`
- Reset mask: `0x1`

### Instances

| Name                | Offset   |
|:--------------------|:---------|
| REGION_CFG_REGWEN_0 | 0x30     |
| REGION_CFG_REGWEN_1 | 0x34     |
| REGION_CFG_REGWEN_2 | 0x38     |
| REGION_CFG_REGWEN_3 | 0x3c     |
| REGION_CFG_REGWEN_4 | 0x40     |
| REGION_CFG_REGWEN_5 | 0x44     |
| REGION_CFG_REGWEN_6 | 0x48     |
| REGION_CFG_REGWEN_7 | 0x4c     |


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

| Value   | Name           | Description                                         |
|:--------|:---------------|:----------------------------------------------------|
| 0x0     | Region locked  | Region can no longer be configured until next reset |
| 0x1     | Region enabled | Region can be configured                            |


## MP_REGION_CFG
Memory property configuration for data partition
- Reset default: `0x9999999`
- Reset mask: `0xfffffff`

### Instances

| Name            | Offset   |
|:----------------|:---------|
| MP_REGION_CFG_0 | 0x50     |
| MP_REGION_CFG_1 | 0x54     |
| MP_REGION_CFG_2 | 0x58     |
| MP_REGION_CFG_3 | 0x5c     |
| MP_REGION_CFG_4 | 0x60     |
| MP_REGION_CFG_5 | 0x64     |
| MP_REGION_CFG_6 | 0x68     |
| MP_REGION_CFG_7 | 0x6c     |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "RD_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "PROG_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ERASE_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "SCRAMBLE_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ECC_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "HE_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                                                                        |
|:------:|:------:|:-------:|:------------|:-------------------------------------------------------------------------------------------------------------------|
| 31:28  |        |         |             | Reserved                                                                                                           |
| 27:24  |   rw   |   0x9   | HE_EN       | Region is high endurance enabled.                                                                                  |
| 23:20  |   rw   |   0x9   | ECC_EN      | Region is integrity checked and reliability ECC enabled.                                                           |
| 19:16  |   rw   |   0x9   | SCRAMBLE_EN | Region is scramble enabled.                                                                                        |
| 15:12  |   rw   |   0x9   | ERASE_EN    | Region can be erased                                                                                               |
|  11:8  |   rw   |   0x9   | PROG_EN     | Region can be programmed                                                                                           |
|  7:4   |   rw   |   0x9   | RD_EN       | Region can be read                                                                                                 |
|  3:0   |   rw   |   0x9   | EN          | Region enabled, following fields apply. If region is disabled, it is not matched against any incoming transaction. |

## MP_REGION
Memory base and size configuration for data partition
- Reset default: `0x0`
- Reset mask: `0x7ffff`

### Instances

| Name        | Offset   |
|:------------|:---------|
| MP_REGION_0 | 0x70     |
| MP_REGION_1 | 0x74     |
| MP_REGION_2 | 0x78     |
| MP_REGION_3 | 0x7c     |
| MP_REGION_4 | 0x80     |
| MP_REGION_5 | 0x84     |
| MP_REGION_6 | 0x88     |
| MP_REGION_7 | 0x8c     |


### Fields

```wavejson
{"reg": [{"name": "BASE", "bits": 9, "attr": ["rw"], "rotate": 0}, {"name": "SIZE", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 13}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                             |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:19  |        |         |        | Reserved                                                                                                                                                                                |
|  18:9  |   rw   |   0x0   | SIZE   | Region size in number of pages. For example, if base is 0 and size is 1, then the region is defined by page 0. If base is 0 and size is 2, then the region is defined by pages 0 and 1. |
|  8:0   |   rw   |   0x0   | BASE   | Region base page. Note the granularity is page, not byte or word                                                                                                                        |

## DEFAULT_REGION
Default region properties
- Offset: `0x90`
- Reset default: `0x999999`
- Reset mask: `0xffffff`

### Fields

```wavejson
{"reg": [{"name": "RD_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "PROG_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ERASE_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "SCRAMBLE_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ECC_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "HE_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                 |
|:------:|:------:|:-------:|:------------|:------------------------------------------------------------|
| 31:24  |        |         |             | Reserved                                                    |
| 23:20  |   rw   |   0x9   | HE_EN       | Region is high endurance enabled.                           |
| 19:16  |   rw   |   0x9   | ECC_EN      | Region is ECC enabled (both integrity and reliability ECC). |
| 15:12  |   rw   |   0x9   | SCRAMBLE_EN | Region is scramble enabled.                                 |
|  11:8  |   rw   |   0x9   | ERASE_EN    | Region can be erased                                        |
|  7:4   |   rw   |   0x9   | PROG_EN     | Region can be programmed                                    |
|  3:0   |   rw   |   0x9   | RD_EN       | Region can be read                                          |

## BANK0_INFO0_REGWEN
Memory region registers configuration enable.
- Reset default: `0x1`
- Reset mask: `0x1`

### Instances

| Name                 | Offset   |
|:---------------------|:---------|
| BANK0_INFO0_REGWEN_0 | 0x94     |
| BANK0_INFO0_REGWEN_1 | 0x98     |
| BANK0_INFO0_REGWEN_2 | 0x9c     |
| BANK0_INFO0_REGWEN_3 | 0xa0     |
| BANK0_INFO0_REGWEN_4 | 0xa4     |
| BANK0_INFO0_REGWEN_5 | 0xa8     |
| BANK0_INFO0_REGWEN_6 | 0xac     |
| BANK0_INFO0_REGWEN_7 | 0xb0     |
| BANK0_INFO0_REGWEN_8 | 0xb4     |
| BANK0_INFO0_REGWEN_9 | 0xb8     |


### Fields

```wavejson
{"reg": [{"name": "REGION", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                  |
|:------:|:------:|:-------:|:--------------------------------------|
|  31:1  |        |         | Reserved                              |
|   0    |  rw0c  |   0x1   | [REGION](#bank0_info0_regwen--region) |

### BANK0_INFO0_REGWEN . REGION
Info0 page write enable.  Once set to 0, it can longer be configured to 1

| Value   | Name         | Description                                         |
|:--------|:-------------|:----------------------------------------------------|
| 0x0     | Page locked  | Region can no longer be configured until next reset |
| 0x1     | Page enabled | Region can be configured                            |


## BANK0_INFO0_PAGE_CFG
  Memory property configuration for info partition in bank0,
  Unlike data partition, each page is individually configured.
- Reset default: `0x9999999`
- Reset mask: `0xfffffff`

### Instances

| Name                   | Offset   |
|:-----------------------|:---------|
| BANK0_INFO0_PAGE_CFG_0 | 0xbc     |
| BANK0_INFO0_PAGE_CFG_1 | 0xc0     |
| BANK0_INFO0_PAGE_CFG_2 | 0xc4     |
| BANK0_INFO0_PAGE_CFG_3 | 0xc8     |
| BANK0_INFO0_PAGE_CFG_4 | 0xcc     |
| BANK0_INFO0_PAGE_CFG_5 | 0xd0     |
| BANK0_INFO0_PAGE_CFG_6 | 0xd4     |
| BANK0_INFO0_PAGE_CFG_7 | 0xd8     |
| BANK0_INFO0_PAGE_CFG_8 | 0xdc     |
| BANK0_INFO0_PAGE_CFG_9 | 0xe0     |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "RD_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "PROG_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ERASE_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "SCRAMBLE_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ECC_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "HE_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                 |
|:------:|:------:|:-------:|:------------|:------------------------------------------------------------|
| 31:28  |        |         |             | Reserved                                                    |
| 27:24  |   rw   |   0x9   | HE_EN       | Region is high endurance enabled.                           |
| 23:20  |   rw   |   0x9   | ECC_EN      | Region is ECC enabled (both integrity and reliability ECC). |
| 19:16  |   rw   |   0x9   | SCRAMBLE_EN | Region is scramble enabled.                                 |
| 15:12  |   rw   |   0x9   | ERASE_EN    | Region can be erased                                        |
|  11:8  |   rw   |   0x9   | PROG_EN     | Region can be programmed                                    |
|  7:4   |   rw   |   0x9   | RD_EN       | Region can be read                                          |
|  3:0   |   rw   |   0x9   | EN          | Region enabled, following fields apply                      |

## BANK0_INFO1_REGWEN
Memory region registers configuration enable.
- Reset default: `0x1`
- Reset mask: `0x1`

### Instances

| Name               | Offset   |
|:-------------------|:---------|
| BANK0_INFO1_REGWEN | 0xe4     |


### Fields

```wavejson
{"reg": [{"name": "REGION", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                  |
|:------:|:------:|:-------:|:--------------------------------------|
|  31:1  |        |         | Reserved                              |
|   0    |  rw0c  |   0x1   | [REGION](#bank0_info1_regwen--region) |

### BANK0_INFO1_REGWEN . REGION
Info1 page write enable.  Once set to 0, it can longer be configured to 1

| Value   | Name         | Description                                         |
|:--------|:-------------|:----------------------------------------------------|
| 0x0     | Page locked  | Region can no longer be configured until next reset |
| 0x1     | Page enabled | Region can be configured                            |


## BANK0_INFO1_PAGE_CFG
  Memory property configuration for info partition in bank0,
  Unlike data partition, each page is individually configured.
- Reset default: `0x9999999`
- Reset mask: `0xfffffff`

### Instances

| Name                 | Offset   |
|:---------------------|:---------|
| BANK0_INFO1_PAGE_CFG | 0xe8     |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "RD_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "PROG_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ERASE_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "SCRAMBLE_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ECC_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "HE_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                 |
|:------:|:------:|:-------:|:------------|:------------------------------------------------------------|
| 31:28  |        |         |             | Reserved                                                    |
| 27:24  |   rw   |   0x9   | HE_EN       | Region is high endurance enabled.                           |
| 23:20  |   rw   |   0x9   | ECC_EN      | Region is ECC enabled (both integrity and reliability ECC). |
| 19:16  |   rw   |   0x9   | SCRAMBLE_EN | Region is scramble enabled.                                 |
| 15:12  |   rw   |   0x9   | ERASE_EN    | Region can be erased                                        |
|  11:8  |   rw   |   0x9   | PROG_EN     | Region can be programmed                                    |
|  7:4   |   rw   |   0x9   | RD_EN       | Region can be read                                          |
|  3:0   |   rw   |   0x9   | EN          | Region enabled, following fields apply                      |

## BANK0_INFO2_REGWEN
Memory region registers configuration enable.
- Reset default: `0x1`
- Reset mask: `0x1`

### Instances

| Name                 | Offset   |
|:---------------------|:---------|
| BANK0_INFO2_REGWEN_0 | 0xec     |
| BANK0_INFO2_REGWEN_1 | 0xf0     |


### Fields

```wavejson
{"reg": [{"name": "REGION", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                  |
|:------:|:------:|:-------:|:--------------------------------------|
|  31:1  |        |         | Reserved                              |
|   0    |  rw0c  |   0x1   | [REGION](#bank0_info2_regwen--region) |

### BANK0_INFO2_REGWEN . REGION
Info2 page write enable.  Once set to 0, it can longer be configured to 1

| Value   | Name         | Description                                         |
|:--------|:-------------|:----------------------------------------------------|
| 0x0     | Page locked  | Region can no longer be configured until next reset |
| 0x1     | Page enabled | Region can be configured                            |


## BANK0_INFO2_PAGE_CFG
  Memory property configuration for info partition in bank0,
  Unlike data partition, each page is individually configured.
- Reset default: `0x9999999`
- Reset mask: `0xfffffff`

### Instances

| Name                   | Offset   |
|:-----------------------|:---------|
| BANK0_INFO2_PAGE_CFG_0 | 0xf4     |
| BANK0_INFO2_PAGE_CFG_1 | 0xf8     |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "RD_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "PROG_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ERASE_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "SCRAMBLE_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ECC_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "HE_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                 |
|:------:|:------:|:-------:|:------------|:------------------------------------------------------------|
| 31:28  |        |         |             | Reserved                                                    |
| 27:24  |   rw   |   0x9   | HE_EN       | Region is high endurance enabled.                           |
| 23:20  |   rw   |   0x9   | ECC_EN      | Region is ECC enabled (both integrity and reliability ECC). |
| 19:16  |   rw   |   0x9   | SCRAMBLE_EN | Region is scramble enabled.                                 |
| 15:12  |   rw   |   0x9   | ERASE_EN    | Region can be erased                                        |
|  11:8  |   rw   |   0x9   | PROG_EN     | Region can be programmed                                    |
|  7:4   |   rw   |   0x9   | RD_EN       | Region can be read                                          |
|  3:0   |   rw   |   0x9   | EN          | Region enabled, following fields apply                      |

## BANK1_INFO0_REGWEN
Memory region registers configuration enable.
- Reset default: `0x1`
- Reset mask: `0x1`

### Instances

| Name                 | Offset   |
|:---------------------|:---------|
| BANK1_INFO0_REGWEN_0 | 0xfc     |
| BANK1_INFO0_REGWEN_1 | 0x100    |
| BANK1_INFO0_REGWEN_2 | 0x104    |
| BANK1_INFO0_REGWEN_3 | 0x108    |
| BANK1_INFO0_REGWEN_4 | 0x10c    |
| BANK1_INFO0_REGWEN_5 | 0x110    |
| BANK1_INFO0_REGWEN_6 | 0x114    |
| BANK1_INFO0_REGWEN_7 | 0x118    |
| BANK1_INFO0_REGWEN_8 | 0x11c    |
| BANK1_INFO0_REGWEN_9 | 0x120    |


### Fields

```wavejson
{"reg": [{"name": "REGION", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                  |
|:------:|:------:|:-------:|:--------------------------------------|
|  31:1  |        |         | Reserved                              |
|   0    |  rw0c  |   0x1   | [REGION](#bank1_info0_regwen--region) |

### BANK1_INFO0_REGWEN . REGION
Info0 page write enable.  Once set to 0, it can longer be configured to 1

| Value   | Name         | Description                                         |
|:--------|:-------------|:----------------------------------------------------|
| 0x0     | Page locked  | Region can no longer be configured until next reset |
| 0x1     | Page enabled | Region can be configured                            |


## BANK1_INFO0_PAGE_CFG
  Memory property configuration for info partition in bank1,
  Unlike data partition, each page is individually configured.
- Reset default: `0x9999999`
- Reset mask: `0xfffffff`

### Instances

| Name                   | Offset   |
|:-----------------------|:---------|
| BANK1_INFO0_PAGE_CFG_0 | 0x124    |
| BANK1_INFO0_PAGE_CFG_1 | 0x128    |
| BANK1_INFO0_PAGE_CFG_2 | 0x12c    |
| BANK1_INFO0_PAGE_CFG_3 | 0x130    |
| BANK1_INFO0_PAGE_CFG_4 | 0x134    |
| BANK1_INFO0_PAGE_CFG_5 | 0x138    |
| BANK1_INFO0_PAGE_CFG_6 | 0x13c    |
| BANK1_INFO0_PAGE_CFG_7 | 0x140    |
| BANK1_INFO0_PAGE_CFG_8 | 0x144    |
| BANK1_INFO0_PAGE_CFG_9 | 0x148    |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "RD_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "PROG_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ERASE_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "SCRAMBLE_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ECC_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "HE_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                 |
|:------:|:------:|:-------:|:------------|:------------------------------------------------------------|
| 31:28  |        |         |             | Reserved                                                    |
| 27:24  |   rw   |   0x9   | HE_EN       | Region is high endurance enabled.                           |
| 23:20  |   rw   |   0x9   | ECC_EN      | Region is ECC enabled (both integrity and reliability ECC). |
| 19:16  |   rw   |   0x9   | SCRAMBLE_EN | Region is scramble enabled.                                 |
| 15:12  |   rw   |   0x9   | ERASE_EN    | Region can be erased                                        |
|  11:8  |   rw   |   0x9   | PROG_EN     | Region can be programmed                                    |
|  7:4   |   rw   |   0x9   | RD_EN       | Region can be read                                          |
|  3:0   |   rw   |   0x9   | EN          | Region enabled, following fields apply                      |

## BANK1_INFO1_REGWEN
Memory region registers configuration enable.
- Reset default: `0x1`
- Reset mask: `0x1`

### Instances

| Name               | Offset   |
|:-------------------|:---------|
| BANK1_INFO1_REGWEN | 0x14c    |


### Fields

```wavejson
{"reg": [{"name": "REGION", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                  |
|:------:|:------:|:-------:|:--------------------------------------|
|  31:1  |        |         | Reserved                              |
|   0    |  rw0c  |   0x1   | [REGION](#bank1_info1_regwen--region) |

### BANK1_INFO1_REGWEN . REGION
Info1 page write enable.  Once set to 0, it can longer be configured to 1

| Value   | Name         | Description                                         |
|:--------|:-------------|:----------------------------------------------------|
| 0x0     | Page locked  | Region can no longer be configured until next reset |
| 0x1     | Page enabled | Region can be configured                            |


## BANK1_INFO1_PAGE_CFG
  Memory property configuration for info partition in bank1,
  Unlike data partition, each page is individually configured.
- Reset default: `0x9999999`
- Reset mask: `0xfffffff`

### Instances

| Name                 | Offset   |
|:---------------------|:---------|
| BANK1_INFO1_PAGE_CFG | 0x150    |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "RD_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "PROG_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ERASE_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "SCRAMBLE_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ECC_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "HE_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                 |
|:------:|:------:|:-------:|:------------|:------------------------------------------------------------|
| 31:28  |        |         |             | Reserved                                                    |
| 27:24  |   rw   |   0x9   | HE_EN       | Region is high endurance enabled.                           |
| 23:20  |   rw   |   0x9   | ECC_EN      | Region is ECC enabled (both integrity and reliability ECC). |
| 19:16  |   rw   |   0x9   | SCRAMBLE_EN | Region is scramble enabled.                                 |
| 15:12  |   rw   |   0x9   | ERASE_EN    | Region can be erased                                        |
|  11:8  |   rw   |   0x9   | PROG_EN     | Region can be programmed                                    |
|  7:4   |   rw   |   0x9   | RD_EN       | Region can be read                                          |
|  3:0   |   rw   |   0x9   | EN          | Region enabled, following fields apply                      |

## BANK1_INFO2_REGWEN
Memory region registers configuration enable.
- Reset default: `0x1`
- Reset mask: `0x1`

### Instances

| Name                 | Offset   |
|:---------------------|:---------|
| BANK1_INFO2_REGWEN_0 | 0x154    |
| BANK1_INFO2_REGWEN_1 | 0x158    |


### Fields

```wavejson
{"reg": [{"name": "REGION", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                  |
|:------:|:------:|:-------:|:--------------------------------------|
|  31:1  |        |         | Reserved                              |
|   0    |  rw0c  |   0x1   | [REGION](#bank1_info2_regwen--region) |

### BANK1_INFO2_REGWEN . REGION
Info2 page write enable.  Once set to 0, it can longer be configured to 1

| Value   | Name         | Description                                         |
|:--------|:-------------|:----------------------------------------------------|
| 0x0     | Page locked  | Region can no longer be configured until next reset |
| 0x1     | Page enabled | Region can be configured                            |


## BANK1_INFO2_PAGE_CFG
  Memory property configuration for info partition in bank1,
  Unlike data partition, each page is individually configured.
- Reset default: `0x9999999`
- Reset mask: `0xfffffff`

### Instances

| Name                   | Offset   |
|:-----------------------|:---------|
| BANK1_INFO2_PAGE_CFG_0 | 0x15c    |
| BANK1_INFO2_PAGE_CFG_1 | 0x160    |


### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "RD_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "PROG_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ERASE_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "SCRAMBLE_EN", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ECC_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "HE_EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                 |
|:------:|:------:|:-------:|:------------|:------------------------------------------------------------|
| 31:28  |        |         |             | Reserved                                                    |
| 27:24  |   rw   |   0x9   | HE_EN       | Region is high endurance enabled.                           |
| 23:20  |   rw   |   0x9   | ECC_EN      | Region is ECC enabled (both integrity and reliability ECC). |
| 19:16  |   rw   |   0x9   | SCRAMBLE_EN | Region is scramble enabled.                                 |
| 15:12  |   rw   |   0x9   | ERASE_EN    | Region can be erased                                        |
|  11:8  |   rw   |   0x9   | PROG_EN     | Region can be programmed                                    |
|  7:4   |   rw   |   0x9   | RD_EN       | Region can be read                                          |
|  3:0   |   rw   |   0x9   | EN          | Region enabled, following fields apply                      |

## HW_INFO_CFG_OVERRIDE
HW interface info configuration rule overrides
- Offset: `0x164`
- Reset default: `0x99`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "SCRAMBLE_DIS", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ECC_DIS", "bits": 4, "attr": ["rw"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                                                                                                                                                                                                          |
|:------:|:------:|:-------:|:-------------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:8  |        |         |              | Reserved                                                                                                                                                                                                                             |
|  7:4   |   rw   |   0x9   | ECC_DIS      | The hardwired hardware info configuration rules for ECC enable are logically AND'd with this field. If the hardware rules hardwires ECC to enable, we can disable via software if needed.  By default this field is false.           |
|  3:0   |   rw   |   0x9   | SCRAMBLE_DIS | The hardwired hardware info configuration rules for scramble enable are logically AND'd with this field. If the hardware rules hardwires scramble to enable, we can disable via software if needed.  By default this field is false. |

## BANK_CFG_REGWEN
Bank configuration registers configuration enable.
- Offset: `0x168`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "BANK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                           |
|:------:|:------:|:-------:|:-------------------------------|
|  31:1  |        |         | Reserved                       |
|   0    |  rw0c  |   0x1   | [BANK](#bank_cfg_regwen--bank) |

### BANK_CFG_REGWEN . BANK
Bank register write enable.  Once set to 0, it can longer be configured to 1

| Value   | Name         | Description                                       |
|:--------|:-------------|:--------------------------------------------------|
| 0x0     | Bank locked  | Bank can no longer be configured until next reset |
| 0x1     | Bank enabled | Bank can be configured                            |


## MP_BANK_CFG_SHADOWED
Memory properties bank configuration
- Offset: `0x16c`
- Reset default: `0x0`
- Reset mask: `0x3`
- Register enable: [`BANK_CFG_REGWEN`](#bank_cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "ERASE_EN_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ERASE_EN_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description            |
|:------:|:------:|:-------:|:-----------|:-----------------------|
|  31:2  |        |         |            | Reserved               |
|   1    |   rw   |   0x0   | ERASE_EN_1 | Bank wide erase enable |
|   0    |   rw   |   0x0   | ERASE_EN_0 | Bank wide erase enable |

## OP_STATUS
Flash Operation Status
- Offset: `0x170`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "done", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "err", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                    |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------------|
|  31:2  |        |         |        | Reserved                                                                                       |
|   1    |   rw   |   0x0   | err    | Flash operation error. Set by HW, cleared by SW. See [`ERR_CODE`](#err_code) for more details. |
|   0    |   rw   |   0x0   | done   | Flash operation done. Set by HW, cleared by SW                                                 |

## STATUS
Flash Controller Status
- Offset: `0x174`
- Reset default: `0xa`
- Reset mask: `0x3f`

### Fields

```wavejson
{"reg": [{"name": "rd_full", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "rd_empty", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "prog_full", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "prog_empty", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "init_wip", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "initialized", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 26}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                             |
|:------:|:------:|:-------:|:------------|:--------------------------------------------------------|
|  31:6  |        |         |             | Reserved                                                |
|   5    |   ro   |   0x0   | initialized | Flash controller initialized                            |
|   4    |   ro   |   0x0   | init_wip    | Flash controller undergoing init, inclusive of phy init |
|   3    |   ro   |   0x1   | prog_empty  | Flash program FIFO empty, software must provide data    |
|   2    |   ro   |   0x0   | prog_full   | Flash program FIFO full                                 |
|   1    |   ro   |   0x1   | rd_empty    | Flash read FIFO empty                                   |
|   0    |   ro   |   0x0   | rd_full     | Flash read FIFO full, software must consume data        |

## DEBUG_STATE
Current flash fsm state
- Offset: `0x178`
- Reset default: `0x0`
- Reset mask: `0x7ff`

### Fields

```wavejson
{"reg": [{"name": "lcmgr_state", "bits": 11, "attr": ["ro"], "rotate": 0}, {"bits": 21}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                   |
|:------:|:------:|:-------:|:------------|:------------------------------|
| 31:11  |        |         |             | Reserved                      |
|  10:0  |   ro   |    x    | lcmgr_state | Current lcmgr interface staet |

## ERR_CODE
Flash error code register.
This register tabulates detailed error status of the flash.
This is separate from [`OP_STATUS`](#op_status), which is used to indicate the current state of the software initiated
flash operation.

Note, all errors in this register are considered recoverable errors, ie, errors that could have been
generated by software.
- Offset: `0x17c`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "op_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "mp_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "rd_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "prog_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "prog_win_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "prog_type_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "update_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "macro_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                                                                                                                                                                                                                                 |
|:------:|:------:|:-------:|:--------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:8  |        |         |               | Reserved                                                                                                                                                                                                                                                                    |
|   7    |  rw1c  |   0x0   | macro_err     | A recoverable error has been encountered in the flash macro. Please read the flash macro status registers for more details.                                                                                                                                                 |
|   6    |  rw1c  |   0x0   | update_err    | A shadow register encountered an update error. This is an asynchronous error.                                                                                                                                                                                               |
|   5    |  rw1c  |   0x0   | prog_type_err | Flash program selected unavailable type, see [`PROG_TYPE_EN.`](#prog_type_en) This is a synchronous error.                                                                                                                                                                  |
|   4    |  rw1c  |   0x0   | prog_win_err  | Flash program has a window resolution error.  Ie, the start of program and end of program are in different windows.  Please check [`ERR_ADDR.`](#err_addr) This is a synchronous error.                                                                                     |
|   3    |  rw1c  |   0x0   | prog_err      | Flash program has an error. This could be a program integrity error, see [`STD_FAULT_STATUS.`](#std_fault_status) This is a synchronous error.                                                                                                                              |
|   2    |  rw1c  |   0x0   | rd_err        | Flash read has an error. This could be a reliability ECC error or an storage integrity error encountered during a software issued controller read, see [`STD_FAULT_STATUS.`](#std_fault_status) See [`ERR_ADDR`](#err_addr) for exact address. This is a synchronous error. |
|   1    |  rw1c  |   0x0   | mp_err        | Flash access has encountered an access permission error. Please see [`ERR_ADDR`](#err_addr) for exact address. This is a synchronous error.                                                                                                                                 |
|   0    |  rw1c  |   0x0   | op_err        | Software has supplied an undefined operation. See [`CONTROL.OP`](#control) for list of valid operations.                                                                                                                                                                    |

## STD_FAULT_STATUS
This register tabulates standard fault status of the flash.

These represent errors that occur in the standard structures of the design.
For example fsm integrity, counter integrity and tlul integrity.
- Offset: `0x180`
- Reset default: `0x0`
- Reset mask: `0x1ff`

### Fields

```wavejson
{"reg": [{"name": "reg_intg_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "prog_intg_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "lcmgr_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "lcmgr_intg_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "arb_fsm_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "storage_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "phy_fsm_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ctrl_cnt_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "fifo_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 23}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                                                                                                                                                                               |
|:------:|:------:|:-------:|:---------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:9  |        |         |                | Reserved                                                                                                                                                                                  |
|   8    |   ro   |   0x0   | fifo_err       | Flash primitive fifo's have encountered a count error.                                                                                                                                    |
|   7    |   ro   |   0x0   | ctrl_cnt_err   | Flash ctrl read/prog has encountered a count error.                                                                                                                                       |
|   6    |   ro   |   0x0   | phy_fsm_err    | A flash phy fsm has encountered a sparse encoding error.                                                                                                                                  |
|   5    |   ro   |   0x0   | storage_err    | A shadow register encountered a storage error.                                                                                                                                            |
|   4    |   ro   |   0x0   | arb_fsm_err    | The arbiter fsm has encountered a sparse encoding error.                                                                                                                                  |
|   3    |   ro   |   0x0   | lcmgr_intg_err | The life cycle management interface has encountered a transmission integrity error.  This is an integrity error on the generated integrity during a life cycle management interface read. |
|   2    |   ro   |   0x0   | lcmgr_err      | The life cycle management interface has encountered a fatal error. The error is either an FSM sparse encoding error or a count error.                                                     |
|   1    |   ro   |   0x0   | prog_intg_err  | The flash controller encountered a program data transmission integrity error.                                                                                                             |
|   0    |   ro   |   0x0   | reg_intg_err   | The flash controller encountered a register integrity error.                                                                                                                              |

## FAULT_STATUS
This register tabulates customized fault status of the flash.

These are errors that are impossible to have been caused by software or unrecoverable
in nature.
- Offset: `0x184`
- Reset default: `0x0`
- Reset mask: `0xfff`

### Fields

```wavejson
{"reg": [{"name": "op_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "mp_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "rd_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "prog_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "prog_win_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "prog_type_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "seed_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "phy_relbl_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "phy_storage_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "spurious_ack", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "arb_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "host_gnt_err", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 20}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name            | Description                                                                                                                                                                                                                  |
|:------:|:------:|:-------:|:----------------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:12  |        |         |                 | Reserved                                                                                                                                                                                                                     |
|   11   |   ro   |   0x0   | host_gnt_err    | A host transaction was granted with illegal properties.                                                                                                                                                                      |
|   10   |   ro   |   0x0   | arb_err         | The phy arbiter encountered inconsistent results.                                                                                                                                                                            |
|   9    |   ro   |   0x0   | spurious_ack    | The flash emitted an unexpected acknowledgement.                                                                                                                                                                             |
|   8    |   ro   |   0x0   | phy_storage_err | The flash macro encountered a storage integrity ECC error.                                                                                                                                                                   |
|   7    |   ro   |   0x0   | phy_relbl_err   | The flash macro encountered a storage reliability ECC error.                                                                                                                                                                 |
|   6    |   ro   |   0x0   | seed_err        | The seed reading process encountered an unexpected error.                                                                                                                                                                    |
|   5    |   ro   |   0x0   | prog_type_err   | The flash life cycle management interface encountered a program type error. A program type not supported by the flash macro was issued.                                                                                      |
|   4    |   ro   |   0x0   | prog_win_err    | The flash life cycle management interface encountered a program resolution error.                                                                                                                                            |
|   3    |   ro   |   0x0   | prog_err        | The flash life cycle management interface encountered a program error. This could be a program integirty eror, see [`STD_FAULT_STATUS`](#std_fault_status) for more details.                                                 |
|   2    |   ro   |   0x0   | rd_err          | The flash life cycle management interface encountered a read error. This could be a reliability ECC error or an integrity ECC error encountered during a read, see [`STD_FAULT_STATUS`](#std_fault_status) for more details. |
|   1    |   ro   |   0x0   | mp_err          | The flash life cycle management interface encountered a memory permission error.                                                                                                                                             |
|   0    |   ro   |   0x0   | op_err          | The flash life cycle management interface has supplied an undefined operation. See [`CONTROL.OP`](#control) for list of valid operations.                                                                                    |

## ERR_ADDR
Synchronous error address
- Offset: `0x188`
- Reset default: `0x0`
- Reset mask: `0xfffff`

### Fields

```wavejson
{"reg": [{"name": "ERR_ADDR", "bits": 20, "attr": ["ro"], "rotate": 0}, {"bits": 12}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description   |
|:------:|:------:|:-------:|:---------|:--------------|
| 31:20  |        |         |          | Reserved      |
|  19:0  |   ro   |   0x0   | ERR_ADDR |               |

## ECC_SINGLE_ERR_CNT
Total number of single bit ECC error count
- Offset: `0x18c`
- Reset default: `0x0`
- Reset mask: `0xffff`

### Fields

```wavejson
{"reg": [{"name": "ECC_SINGLE_ERR_CNT_0", "bits": 8, "attr": ["rw"], "rotate": -90}, {"name": "ECC_SINGLE_ERR_CNT_1", "bits": 8, "attr": ["rw"], "rotate": -90}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                             |
|:------:|:------:|:-------:|:---------------------|:----------------------------------------|
| 31:16  |        |         |                      | Reserved                                |
|  15:8  |   rw   |   0x0   | ECC_SINGLE_ERR_CNT_1 | This count will not wrap when saturated |
|  7:0   |   rw   |   0x0   | ECC_SINGLE_ERR_CNT_0 | This count will not wrap when saturated |

## ECC_SINGLE_ERR_ADDR
Latest address of ECC single err
- Reset default: `0x0`
- Reset mask: `0xfffff`

### Instances

| Name                  | Offset   |
|:----------------------|:---------|
| ECC_SINGLE_ERR_ADDR_0 | 0x190    |
| ECC_SINGLE_ERR_ADDR_1 | 0x194    |


### Fields

```wavejson
{"reg": [{"name": "ECC_SINGLE_ERR_ADDR", "bits": 20, "attr": ["ro"], "rotate": 0}, {"bits": 12}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                | Description                               |
|:------:|:------:|:-------:|:--------------------|:------------------------------------------|
| 31:20  |        |         |                     | Reserved                                  |
|  19:0  |   ro   |   0x0   | ECC_SINGLE_ERR_ADDR | Latest single error address for this bank |

## PHY_ALERT_CFG
Phy alert configuration
- Offset: `0x198`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "alert_ack", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "alert_trig", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                 |
|:------:|:------:|:-------:|:-----------|:----------------------------|
|  31:2  |        |         |            | Reserved                    |
|   1    |   rw   |   0x0   | alert_trig | Trigger flash phy alert     |
|   0    |   rw   |   0x0   | alert_ack  | Acknowledge flash phy alert |

## PHY_STATUS
Flash Phy Status
- Offset: `0x19c`
- Reset default: `0x6`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "init_wip", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "prog_normal_avail", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "prog_repair_avail", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                       |
|:------:|:------:|:-------:|:------------------|:----------------------------------|
|  31:3  |        |         |                   | Reserved                          |
|   2    |   ro   |   0x1   | prog_repair_avail | Program repair supported          |
|   1    |   ro   |   0x1   | prog_normal_avail | Normal program supported          |
|   0    |   ro   |   0x0   | init_wip          | Flash phy controller initializing |

## Scratch
Flash Controller Scratch
- Offset: `0x1a0`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "data", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                 |
|:------:|:------:|:-------:|:-------|:----------------------------|
|  31:0  |   rw   |   0x0   | data   | Flash ctrl scratch register |

## FIFO_LVL
Programmable depth where FIFOs should generate interrupts
- Offset: `0x1a4`
- Reset default: `0xf0f`
- Reset mask: `0x1f1f`

### Fields

```wavejson
{"reg": [{"name": "PROG", "bits": 5, "attr": ["rw"], "rotate": 0}, {"bits": 3}, {"name": "RD", "bits": 5, "attr": ["rw"], "rotate": 0}, {"bits": 19}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                           |
|:------:|:------:|:-------:|:-------|:--------------------------------------------------------------------------------------------------------------------------------------|
| 31:13  |        |         |        | Reserved                                                                                                                              |
|  12:8  |   rw   |   0xf   | RD     | When the read FIFO fills to this level, trigger an interrupt. Default value is set such that interrupt does not trigger at reset.     |
|  7:5   |        |         |        | Reserved                                                                                                                              |
|  4:0   |   rw   |   0xf   | PROG   | When the program FIFO drains to this level, trigger an interrupt. Default value is set such that interrupt does not trigger at reset. |

## FIFO_RST
Reset for flash controller FIFOs
- Offset: `0x1a8`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                                                                                                                         |
|   0    |   rw   |   0x0   | EN     | Active high resets for both program and read FIFOs.  This is especially useful after the controller encounters an error of some kind. This bit will hold the FIFO in reset as long as it is set. |

## CURR_FIFO_LVL
Current program and read fifo depth
- Offset: `0x1ac`
- Reset default: `0x0`
- Reset mask: `0x1f1f`

### Fields

```wavejson
{"reg": [{"name": "PROG", "bits": 5, "attr": ["ro"], "rotate": 0}, {"bits": 3}, {"name": "RD", "bits": 5, "attr": ["ro"], "rotate": 0}, {"bits": 19}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                |
|:------:|:------:|:-------:|:-------|:---------------------------|
| 31:13  |        |         |        | Reserved                   |
|  12:8  |   ro   |   0x0   | RD     | Current read fifo depth    |
|  7:5   |        |         |        | Reserved                   |
|  4:0   |   ro   |   0x0   | PROG   | Current program fifo depth |

## prog_fifo
Flash program FIFO.

The FIFO is 16 entries of 4B flash words. This FIFO can only be programmed
by software after a program operation has been initiated via the !!CONTROL register.
This ensures accidental programming of the program FIFO cannot lock up the system.

- Word Aligned Offset Range: `0x1b0`to`0x1b0`
- Size (words): `1`
- Access: `wo`
- Byte writes are *not* supported.

## rd_fifo
Flash read FIFO.

The FIFO is 16 entries of 4B flash words

- Word Aligned Offset Range: `0x1b4`to`0x1b4`
- Size (words): `1`
- Access: `ro`
- Byte writes are *not* supported.

## Summary of the **`prim`** interface's registers

| Name                                     | Offset   |   Length | Description   |
|:-----------------------------------------|:---------|---------:|:--------------|
| flash_ctrl.[`CSR0_REGWEN`](#csr0_regwen) | 0x0      |        4 |               |
| flash_ctrl.[`CSR1`](#csr1)               | 0x4      |        4 |               |
| flash_ctrl.[`CSR2`](#csr2)               | 0x8      |        4 |               |
| flash_ctrl.[`CSR3`](#csr3)               | 0xc      |        4 |               |
| flash_ctrl.[`CSR4`](#csr4)               | 0x10     |        4 |               |
| flash_ctrl.[`CSR5`](#csr5)               | 0x14     |        4 |               |
| flash_ctrl.[`CSR6`](#csr6)               | 0x18     |        4 |               |
| flash_ctrl.[`CSR7`](#csr7)               | 0x1c     |        4 |               |
| flash_ctrl.[`CSR8`](#csr8)               | 0x20     |        4 |               |
| flash_ctrl.[`CSR9`](#csr9)               | 0x24     |        4 |               |
| flash_ctrl.[`CSR10`](#csr10)             | 0x28     |        4 |               |
| flash_ctrl.[`CSR11`](#csr11)             | 0x2c     |        4 |               |
| flash_ctrl.[`CSR12`](#csr12)             | 0x30     |        4 |               |
| flash_ctrl.[`CSR13`](#csr13)             | 0x34     |        4 |               |
| flash_ctrl.[`CSR14`](#csr14)             | 0x38     |        4 |               |
| flash_ctrl.[`CSR15`](#csr15)             | 0x3c     |        4 |               |
| flash_ctrl.[`CSR16`](#csr16)             | 0x40     |        4 |               |
| flash_ctrl.[`CSR17`](#csr17)             | 0x44     |        4 |               |
| flash_ctrl.[`CSR18`](#csr18)             | 0x48     |        4 |               |
| flash_ctrl.[`CSR19`](#csr19)             | 0x4c     |        4 |               |
| flash_ctrl.[`CSR20`](#csr20)             | 0x50     |        4 |               |

## CSR0_REGWEN

- Offset: `0x0`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                           |
|:------:|:------:|:-------:|:-------------------------------|
|  31:1  |        |         | Reserved                       |
|   0    |  rw0c  |   0x1   | [field0](#csr0_regwen--field0) |

### CSR0_REGWEN . field0

All values are reserved.

## CSR1

- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x1fff`
- Register enable: [`CSR0_REGWEN`](#csr0_regwen)

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "field1", "bits": 5, "attr": ["rw"], "rotate": 0}, {"bits": 19}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                    |
|:------:|:------:|:-------:|:------------------------|
| 31:13  |        |         | Reserved                |
|  12:8  |   rw   |   0x0   | [field1](#csr1--field1) |
|  7:0   |   rw   |   0x0   | [field0](#csr1--field0) |

### CSR1 . field1

All values are reserved.

### CSR1 . field0

All values are reserved.

## CSR2

- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "field1", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "field2", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "field3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "field4", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "field5", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "field6", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "field7", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                    |
|:------:|:------:|:-------:|:------------------------|
|  31:8  |        |         | Reserved                |
|   7    |   rw   |   0x0   | [field7](#csr2--field7) |
|   6    |  rw1c  |   0x0   | [field6](#csr2--field6) |
|   5    |  rw1c  |   0x0   | [field5](#csr2--field5) |
|   4    |  rw1c  |   0x0   | [field4](#csr2--field4) |
|   3    |   rw   |   0x0   | [field3](#csr2--field3) |
|   2    |  rw1c  |   0x0   | [field2](#csr2--field2) |
|   1    |  rw1c  |   0x0   | [field1](#csr2--field1) |
|   0    |  rw1c  |   0x0   | [field0](#csr2--field0) |

### CSR2 . field7

All values are reserved.

### CSR2 . field6

All values are reserved.

### CSR2 . field5

All values are reserved.

### CSR2 . field4

All values are reserved.

### CSR2 . field3

All values are reserved.

### CSR2 . field2

All values are reserved.

### CSR2 . field1

All values are reserved.

### CSR2 . field0

All values are reserved.

## CSR3

- Offset: `0xc`
- Reset default: `0x0`
- Reset mask: `0xfffffff`
- Register enable: [`CSR0_REGWEN`](#csr0_regwen)

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "field1", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "field2", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "field3", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "field4", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "field5", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "field6", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "field7", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "field8", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "field9", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                    |
|:------:|:------:|:-------:|:------------------------|
| 31:28  |        |         | Reserved                |
| 27:26  |   rw   |   0x0   | [field9](#csr3--field9) |
| 25:24  |   rw   |   0x0   | [field8](#csr3--field8) |
| 23:21  |   rw   |   0x0   | [field7](#csr3--field7) |
|   20   |   rw   |   0x0   | [field6](#csr3--field6) |
| 19:17  |   rw   |   0x0   | [field5](#csr3--field5) |
| 16:14  |   rw   |   0x0   | [field4](#csr3--field4) |
| 13:11  |   rw   |   0x0   | [field3](#csr3--field3) |
|  10:8  |   rw   |   0x0   | [field2](#csr3--field2) |
|  7:4   |   rw   |   0x0   | [field1](#csr3--field1) |
|  3:0   |   rw   |   0x0   | [field0](#csr3--field0) |

### CSR3 . field9

All values are reserved.

### CSR3 . field8

All values are reserved.

### CSR3 . field7

All values are reserved.

### CSR3 . field6

All values are reserved.

### CSR3 . field5

All values are reserved.

### CSR3 . field4

All values are reserved.

### CSR3 . field3

All values are reserved.

### CSR3 . field2

All values are reserved.

### CSR3 . field1

All values are reserved.

### CSR3 . field0

All values are reserved.

## CSR4

- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0xfff`
- Register enable: [`CSR0_REGWEN`](#csr0_regwen)

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "field1", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "field2", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "field3", "bits": 3, "attr": ["rw"], "rotate": -90}, {"bits": 20}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                    |
|:------:|:------:|:-------:|:------------------------|
| 31:12  |        |         | Reserved                |
|  11:9  |   rw   |   0x0   | [field3](#csr4--field3) |
|  8:6   |   rw   |   0x0   | [field2](#csr4--field2) |
|  5:3   |   rw   |   0x0   | [field1](#csr4--field1) |
|  2:0   |   rw   |   0x0   | [field0](#csr4--field0) |

### CSR4 . field3

All values are reserved.

### CSR4 . field2

All values are reserved.

### CSR4 . field1

All values are reserved.

### CSR4 . field0

All values are reserved.

## CSR5

- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0x7fffff`
- Register enable: [`CSR0_REGWEN`](#csr0_regwen)

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "field1", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "field2", "bits": 9, "attr": ["rw"], "rotate": 0}, {"name": "field3", "bits": 5, "attr": ["rw"], "rotate": 0}, {"name": "field4", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 9}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                    |
|:------:|:------:|:-------:|:------------------------|
| 31:23  |        |         | Reserved                |
| 22:19  |   rw   |   0x0   | [field4](#csr5--field4) |
| 18:14  |   rw   |   0x0   | [field3](#csr5--field3) |
|  13:5  |   rw   |   0x0   | [field2](#csr5--field2) |
|  4:3   |   rw   |   0x0   | [field1](#csr5--field1) |
|  2:0   |   rw   |   0x0   | [field0](#csr5--field0) |

### CSR5 . field4

All values are reserved.

### CSR5 . field3

All values are reserved.

### CSR5 . field2

All values are reserved.

### CSR5 . field1

All values are reserved.

### CSR5 . field0

All values are reserved.

## CSR6

- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0x1ffffff`
- Register enable: [`CSR0_REGWEN`](#csr0_regwen)

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "field1", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "field2", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "field3", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "field4", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "field5", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "field6", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "field7", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "field8", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 7}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                    |
|:------:|:------:|:-------:|:------------------------|
| 31:25  |        |         | Reserved                |
|   24   |   rw   |   0x0   | [field8](#csr6--field8) |
|   23   |   rw   |   0x0   | [field7](#csr6--field7) |
| 22:21  |   rw   |   0x0   | [field6](#csr6--field6) |
| 20:19  |   rw   |   0x0   | [field5](#csr6--field5) |
| 18:17  |   rw   |   0x0   | [field4](#csr6--field4) |
| 16:14  |   rw   |   0x0   | [field3](#csr6--field3) |
|  13:6  |   rw   |   0x0   | [field2](#csr6--field2) |
|  5:3   |   rw   |   0x0   | [field1](#csr6--field1) |
|  2:0   |   rw   |   0x0   | [field0](#csr6--field0) |

### CSR6 . field8

All values are reserved.

### CSR6 . field7

All values are reserved.

### CSR6 . field6

All values are reserved.

### CSR6 . field5

All values are reserved.

### CSR6 . field4

All values are reserved.

### CSR6 . field3

All values are reserved.

### CSR6 . field2

All values are reserved.

### CSR6 . field1

All values are reserved.

### CSR6 . field0

All values are reserved.

## CSR7

- Offset: `0x1c`
- Reset default: `0x0`
- Reset mask: `0x1ffff`
- Register enable: [`CSR0_REGWEN`](#csr0_regwen)

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "field1", "bits": 9, "attr": ["rw"], "rotate": 0}, {"bits": 15}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                    |
|:------:|:------:|:-------:|:------------------------|
| 31:17  |        |         | Reserved                |
|  16:8  |   rw   |   0x0   | [field1](#csr7--field1) |
|  7:0   |   rw   |   0x0   | [field0](#csr7--field0) |

### CSR7 . field1

All values are reserved.

### CSR7 . field0

All values are reserved.

## CSR8

- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CSR0_REGWEN`](#csr0_regwen)

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                    |
|:------:|:------:|:-------:|:------------------------|
|  31:0  |   rw   |   0x0   | [field0](#csr8--field0) |

### CSR8 . field0

All values are reserved.

## CSR9

- Offset: `0x24`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CSR0_REGWEN`](#csr0_regwen)

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                    |
|:------:|:------:|:-------:|:------------------------|
|  31:0  |   rw   |   0x0   | [field0](#csr9--field0) |

### CSR9 . field0

All values are reserved.

## CSR10

- Offset: `0x28`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CSR0_REGWEN`](#csr0_regwen)

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                     |
|:------:|:------:|:-------:|:-------------------------|
|  31:0  |   rw   |   0x0   | [field0](#csr10--field0) |

### CSR10 . field0

All values are reserved.

## CSR11

- Offset: `0x2c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CSR0_REGWEN`](#csr0_regwen)

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                     |
|:------:|:------:|:-------:|:-------------------------|
|  31:0  |   rw   |   0x0   | [field0](#csr11--field0) |

### CSR11 . field0

All values are reserved.

## CSR12

- Offset: `0x30`
- Reset default: `0x0`
- Reset mask: `0x3ff`
- Register enable: [`CSR0_REGWEN`](#csr0_regwen)

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 22}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                     |
|:------:|:------:|:-------:|:-------------------------|
| 31:10  |        |         | Reserved                 |
|  9:0   |   rw   |   0x0   | [field0](#csr12--field0) |

### CSR12 . field0

All values are reserved.

## CSR13

- Offset: `0x34`
- Reset default: `0x0`
- Reset mask: `0x1fffff`
- Register enable: [`CSR0_REGWEN`](#csr0_regwen)

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 20, "attr": ["rw"], "rotate": 0}, {"name": "field1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 11}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                     |
|:------:|:------:|:-------:|:-------------------------|
| 31:21  |        |         | Reserved                 |
|   20   |   rw   |   0x0   | [field1](#csr13--field1) |
|  19:0  |   rw   |   0x0   | [field0](#csr13--field0) |

### CSR13 . field1

All values are reserved.

### CSR13 . field0

All values are reserved.

## CSR14

- Offset: `0x38`
- Reset default: `0x0`
- Reset mask: `0x1ff`
- Register enable: [`CSR0_REGWEN`](#csr0_regwen)

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "field1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 23}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                     |
|:------:|:------:|:-------:|:-------------------------|
|  31:9  |        |         | Reserved                 |
|   8    |   rw   |   0x0   | [field1](#csr14--field1) |
|  7:0   |   rw   |   0x0   | [field0](#csr14--field0) |

### CSR14 . field1

All values are reserved.

### CSR14 . field0

All values are reserved.

## CSR15

- Offset: `0x3c`
- Reset default: `0x0`
- Reset mask: `0x1ff`
- Register enable: [`CSR0_REGWEN`](#csr0_regwen)

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "field1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 23}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                     |
|:------:|:------:|:-------:|:-------------------------|
|  31:9  |        |         | Reserved                 |
|   8    |   rw   |   0x0   | [field1](#csr15--field1) |
|  7:0   |   rw   |   0x0   | [field0](#csr15--field0) |

### CSR15 . field1

All values are reserved.

### CSR15 . field0

All values are reserved.

## CSR16

- Offset: `0x40`
- Reset default: `0x0`
- Reset mask: `0x1ff`
- Register enable: [`CSR0_REGWEN`](#csr0_regwen)

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "field1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 23}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                     |
|:------:|:------:|:-------:|:-------------------------|
|  31:9  |        |         | Reserved                 |
|   8    |   rw   |   0x0   | [field1](#csr16--field1) |
|  7:0   |   rw   |   0x0   | [field0](#csr16--field0) |

### CSR16 . field1

All values are reserved.

### CSR16 . field0

All values are reserved.

## CSR17

- Offset: `0x44`
- Reset default: `0x0`
- Reset mask: `0x1ff`
- Register enable: [`CSR0_REGWEN`](#csr0_regwen)

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "field1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 23}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                     |
|:------:|:------:|:-------:|:-------------------------|
|  31:9  |        |         | Reserved                 |
|   8    |   rw   |   0x0   | [field1](#csr17--field1) |
|  7:0   |   rw   |   0x0   | [field0](#csr17--field0) |

### CSR17 . field1

All values are reserved.

### CSR17 . field0

All values are reserved.

## CSR18

- Offset: `0x48`
- Reset default: `0x0`
- Reset mask: `0x1`
- Register enable: [`CSR0_REGWEN`](#csr0_regwen)

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                     |
|:------:|:------:|:-------:|:-------------------------|
|  31:1  |        |         | Reserved                 |
|   0    |   rw   |   0x0   | [field0](#csr18--field0) |

### CSR18 . field0

All values are reserved.

## CSR19

- Offset: `0x4c`
- Reset default: `0x0`
- Reset mask: `0x1`
- Register enable: [`CSR0_REGWEN`](#csr0_regwen)

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                     |
|:------:|:------:|:-------:|:-------------------------|
|  31:1  |        |         | Reserved                 |
|   0    |   rw   |   0x0   | [field0](#csr19--field0) |

### CSR19 . field0

All values are reserved.

## CSR20

- Offset: `0x50`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "field1", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "field2", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                     |
|:------:|:------:|:-------:|:-------------------------|
|  31:3  |        |         | Reserved                 |
|   2    |   ro   |   0x0   | [field2](#csr20--field2) |
|   1    |  rw1c  |   0x0   | [field1](#csr20--field1) |
|   0    |  rw1c  |   0x0   | [field0](#csr20--field0) |

### CSR20 . field2

All values are reserved.

### CSR20 . field1

All values are reserved.

### CSR20 . field0

All values are reserved.

This interface does not expose any registers.
<!-- END CMDGEN -->
