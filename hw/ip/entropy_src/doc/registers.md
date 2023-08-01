# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/entropy_src/data/entropy_src.hjson -->
## Summary

| Name                                                                  | Offset   |   Length | Description                                                  |
|:----------------------------------------------------------------------|:---------|---------:|:-------------------------------------------------------------|
| entropy_src.[`INTR_STATE`](#intr_state)                               | 0x0      |        4 | Interrupt State Register                                     |
| entropy_src.[`INTR_ENABLE`](#intr_enable)                             | 0x4      |        4 | Interrupt Enable Register                                    |
| entropy_src.[`INTR_TEST`](#intr_test)                                 | 0x8      |        4 | Interrupt Test Register                                      |
| entropy_src.[`ALERT_TEST`](#alert_test)                               | 0xc      |        4 | Alert Test Register                                          |
| entropy_src.[`ME_REGWEN`](#me_regwen)                                 | 0x10     |        4 | Register write enable for module enable register             |
| entropy_src.[`SW_REGUPD`](#sw_regupd)                                 | 0x14     |        4 | Register write enable for control and threshold registers    |
| entropy_src.[`REGWEN`](#regwen)                                       | 0x18     |        4 | Register write enable for all control registers              |
| entropy_src.[`REV`](#rev)                                             | 0x1c     |        4 | Revision register                                            |
| entropy_src.[`MODULE_ENABLE`](#module_enable)                         | 0x20     |        4 | Module enable register                                       |
| entropy_src.[`CONF`](#conf)                                           | 0x24     |        4 | Configuration register                                       |
| entropy_src.[`ENTROPY_CONTROL`](#entropy_control)                     | 0x28     |        4 | Entropy control register                                     |
| entropy_src.[`ENTROPY_DATA`](#entropy_data)                           | 0x2c     |        4 | Entropy data bits                                            |
| entropy_src.[`HEALTH_TEST_WINDOWS`](#health_test_windows)             | 0x30     |        4 | Health test windows register                                 |
| entropy_src.[`REPCNT_THRESHOLDS`](#repcnt_thresholds)                 | 0x34     |        4 | Repetition count test thresholds register                    |
| entropy_src.[`REPCNTS_THRESHOLDS`](#repcnts_thresholds)               | 0x38     |        4 | Repetition count symbol test thresholds register             |
| entropy_src.[`ADAPTP_HI_THRESHOLDS`](#adaptp_hi_thresholds)           | 0x3c     |        4 | Adaptive proportion test high thresholds register            |
| entropy_src.[`ADAPTP_LO_THRESHOLDS`](#adaptp_lo_thresholds)           | 0x40     |        4 | Adaptive proportion test low thresholds register             |
| entropy_src.[`BUCKET_THRESHOLDS`](#bucket_thresholds)                 | 0x44     |        4 | Bucket test thresholds register                              |
| entropy_src.[`MARKOV_HI_THRESHOLDS`](#markov_hi_thresholds)           | 0x48     |        4 | Markov test high thresholds register                         |
| entropy_src.[`MARKOV_LO_THRESHOLDS`](#markov_lo_thresholds)           | 0x4c     |        4 | Markov test low thresholds register                          |
| entropy_src.[`EXTHT_HI_THRESHOLDS`](#extht_hi_thresholds)             | 0x50     |        4 | External health test high thresholds register                |
| entropy_src.[`EXTHT_LO_THRESHOLDS`](#extht_lo_thresholds)             | 0x54     |        4 | External health test low thresholds register                 |
| entropy_src.[`REPCNT_HI_WATERMARKS`](#repcnt_hi_watermarks)           | 0x58     |        4 | Repetition count test high watermarks register               |
| entropy_src.[`REPCNTS_HI_WATERMARKS`](#repcnts_hi_watermarks)         | 0x5c     |        4 | Repetition count symbol test high watermarks register        |
| entropy_src.[`ADAPTP_HI_WATERMARKS`](#adaptp_hi_watermarks)           | 0x60     |        4 | Adaptive proportion test high watermarks register            |
| entropy_src.[`ADAPTP_LO_WATERMARKS`](#adaptp_lo_watermarks)           | 0x64     |        4 | Adaptive proportion test low watermarks register             |
| entropy_src.[`EXTHT_HI_WATERMARKS`](#extht_hi_watermarks)             | 0x68     |        4 | External health test high watermarks register                |
| entropy_src.[`EXTHT_LO_WATERMARKS`](#extht_lo_watermarks)             | 0x6c     |        4 | External health test low watermarks register                 |
| entropy_src.[`BUCKET_HI_WATERMARKS`](#bucket_hi_watermarks)           | 0x70     |        4 | Bucket test high watermarks register                         |
| entropy_src.[`MARKOV_HI_WATERMARKS`](#markov_hi_watermarks)           | 0x74     |        4 | Markov test high watermarks register                         |
| entropy_src.[`MARKOV_LO_WATERMARKS`](#markov_lo_watermarks)           | 0x78     |        4 | Markov test low watermarks register                          |
| entropy_src.[`REPCNT_TOTAL_FAILS`](#repcnt_total_fails)               | 0x7c     |        4 | Repetition count test failure counter register               |
| entropy_src.[`REPCNTS_TOTAL_FAILS`](#repcnts_total_fails)             | 0x80     |        4 | Repetition count symbol test failure counter register        |
| entropy_src.[`ADAPTP_HI_TOTAL_FAILS`](#adaptp_hi_total_fails)         | 0x84     |        4 | Adaptive proportion high test failure counter register       |
| entropy_src.[`ADAPTP_LO_TOTAL_FAILS`](#adaptp_lo_total_fails)         | 0x88     |        4 | Adaptive proportion low test failure counter register        |
| entropy_src.[`BUCKET_TOTAL_FAILS`](#bucket_total_fails)               | 0x8c     |        4 | Bucket test failure counter register                         |
| entropy_src.[`MARKOV_HI_TOTAL_FAILS`](#markov_hi_total_fails)         | 0x90     |        4 | Markov high test failure counter register                    |
| entropy_src.[`MARKOV_LO_TOTAL_FAILS`](#markov_lo_total_fails)         | 0x94     |        4 | Markov low test failure counter register                     |
| entropy_src.[`EXTHT_HI_TOTAL_FAILS`](#extht_hi_total_fails)           | 0x98     |        4 | External health test high threshold failure counter register |
| entropy_src.[`EXTHT_LO_TOTAL_FAILS`](#extht_lo_total_fails)           | 0x9c     |        4 | External health test low threshold failure counter register  |
| entropy_src.[`ALERT_THRESHOLD`](#alert_threshold)                     | 0xa0     |        4 | Alert threshold register                                     |
| entropy_src.[`ALERT_SUMMARY_FAIL_COUNTS`](#alert_summary_fail_counts) | 0xa4     |        4 | Alert summary failure counts register                        |
| entropy_src.[`ALERT_FAIL_COUNTS`](#alert_fail_counts)                 | 0xa8     |        4 | Alert failure counts register                                |
| entropy_src.[`EXTHT_FAIL_COUNTS`](#extht_fail_counts)                 | 0xac     |        4 | External health test alert failure counts register           |
| entropy_src.[`FW_OV_CONTROL`](#fw_ov_control)                         | 0xb0     |        4 | Firmware override control register                           |
| entropy_src.[`FW_OV_SHA3_START`](#fw_ov_sha3_start)                   | 0xb4     |        4 | Firmware override sha3 block start control register          |
| entropy_src.[`FW_OV_WR_FIFO_FULL`](#fw_ov_wr_fifo_full)               | 0xb8     |        4 | Firmware override FIFO write full status register            |
| entropy_src.[`FW_OV_RD_FIFO_OVERFLOW`](#fw_ov_rd_fifo_overflow)       | 0xbc     |        4 | Firmware override observe FIFO overflow status               |
| entropy_src.[`FW_OV_RD_DATA`](#fw_ov_rd_data)                         | 0xc0     |        4 | Firmware override observe FIFO read register                 |
| entropy_src.[`FW_OV_WR_DATA`](#fw_ov_wr_data)                         | 0xc4     |        4 | Firmware override FIFO write register                        |
| entropy_src.[`OBSERVE_FIFO_THRESH`](#observe_fifo_thresh)             | 0xc8     |        4 | Observe FIFO threshold register                              |
| entropy_src.[`OBSERVE_FIFO_DEPTH`](#observe_fifo_depth)               | 0xcc     |        4 | Observe FIFO depth register                                  |
| entropy_src.[`DEBUG_STATUS`](#debug_status)                           | 0xd0     |        4 | Debug status register                                        |
| entropy_src.[`RECOV_ALERT_STS`](#recov_alert_sts)                     | 0xd4     |        4 | Recoverable alert status register                            |
| entropy_src.[`ERR_CODE`](#err_code)                                   | 0xd8     |        4 | Hardware detection of error conditions status register       |
| entropy_src.[`ERR_CODE_TEST`](#err_code_test)                         | 0xdc     |        4 | Test error conditions register                               |
| entropy_src.[`MAIN_SM_STATE`](#main_sm_state)                         | 0xe0     |        4 | Main state machine state debug register                      |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "es_entropy_valid", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "es_health_test_failed", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "es_observe_fifo_ready", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "es_fatal_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                                                         |
|:------:|:------:|:-------:|:----------------------|:------------------------------------------------------------------------------------|
|  31:4  |        |         |                       | Reserved                                                                            |
|   3    |  rw1c  |   0x0   | es_fatal_err          | Asserted when a FIFO error occurs, or if an illegal state machine state is reached. |
|   2    |  rw1c  |   0x0   | es_observe_fifo_ready | Asserted when the observe FIFO has filled to the threshold level.                   |
|   1    |  rw1c  |   0x0   | es_health_test_failed | Asserted when the alert count has been met.                                         |
|   0    |  rw1c  |   0x0   | es_entropy_valid      | Asserted when entropy source bits are available.                                    |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "es_entropy_valid", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "es_health_test_failed", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "es_observe_fifo_ready", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "es_fatal_err", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                                                     |
|:------:|:------:|:-------:|:----------------------|:--------------------------------------------------------------------------------|
|  31:4  |        |         |                       | Reserved                                                                        |
|   3    |   rw   |   0x0   | es_fatal_err          | Enable interrupt when [`INTR_STATE.es_fatal_err`](#intr_state) is set.          |
|   2    |   rw   |   0x0   | es_observe_fifo_ready | Enable interrupt when [`INTR_STATE.es_observe_fifo_ready`](#intr_state) is set. |
|   1    |   rw   |   0x0   | es_health_test_failed | Enable interrupt when [`INTR_STATE.es_health_test_failed`](#intr_state) is set. |
|   0    |   rw   |   0x0   | es_entropy_valid      | Enable interrupt when [`INTR_STATE.es_entropy_valid`](#intr_state) is set.      |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "es_entropy_valid", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "es_health_test_failed", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "es_observe_fifo_ready", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "es_fatal_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                                              |
|:------:|:------:|:-------:|:----------------------|:-------------------------------------------------------------------------|
|  31:4  |        |         |                       | Reserved                                                                 |
|   3    |   wo   |   0x0   | es_fatal_err          | Write 1 to force [`INTR_STATE.es_fatal_err`](#intr_state) to 1.          |
|   2    |   wo   |   0x0   | es_observe_fifo_ready | Write 1 to force [`INTR_STATE.es_observe_fifo_ready`](#intr_state) to 1. |
|   1    |   wo   |   0x0   | es_health_test_failed | Write 1 to force [`INTR_STATE.es_health_test_failed`](#intr_state) to 1. |
|   0    |   wo   |   0x0   | es_entropy_valid      | Write 1 to force [`INTR_STATE.es_entropy_valid`](#intr_state) to 1.      |

## ALERT_TEST
Alert Test Register
- Offset: `0xc`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "recov_alert", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_alert", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                      |
|:------:|:------:|:-------:|:------------|:-------------------------------------------------|
|  31:2  |        |         |             | Reserved                                         |
|   1    |   wo   |   0x0   | fatal_alert | Write 1 to trigger one alert event of this kind. |
|   0    |   wo   |   0x0   | recov_alert | Write 1 to trigger one alert event of this kind. |

## ME_REGWEN
Register write enable for module enable register
- Offset: `0x10`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "ME_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                                                                  |
|:------:|:------:|:-------:|:----------|:-------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |           | Reserved                                                                                                     |
|   0    |  rw0c  |   0x1   | ME_REGWEN | When true, the [`MODULE_ENABLE`](#module_enable) register can be modified. When false, it becomes read-only. |

## SW_REGUPD
Register write enable for control and threshold registers
- Offset: `0x14`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "SW_REGUPD", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                                                                                                                                                                            |
|:------:|:------:|:-------:|:----------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |           | Reserved                                                                                                                                                                                                               |
|   0    |  rw0c  |   0x1   | SW_REGUPD | When this bit true and the MODULE_ENABLE field is false, the REGWEN write enable bit read as true, and is distributed to all associated control and threshold registers. When false, these registers become read-only. |

## REGWEN
Register write enable for all control registers
- Offset: `0x18`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "REGWEN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                      |
|:------:|:------:|:-------:|:--------------------------|
|  31:1  |        |         | Reserved                  |
|   0    |   ro   |   0x1   | [REGWEN](#regwen--regwen) |

### REGWEN . REGWEN
This read-only write enable bit will allow write access to control and threshold registers that are associated with this bit, but only when the [`MODULE_ENABLE`](#module_enable) register is set to `kMultiBitBool4False` and the [`SW_REGUPD`](#sw_regupd) write enable bit is set to true.
When read as false, these registers become read-only.

## REV
Revision register
- Offset: `0x1c`
- Reset default: `0x10303`
- Reset mask: `0xffffff`

### Fields

```wavejson
{"reg": [{"name": "ABI_REVISION", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "HW_REVISION", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "CHIP_TYPE", "bits": 8, "attr": ["ro"], "rotate": 0}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                                    |
|:------:|:------:|:-------:|:-------------|:---------------------------------------------------------------|
| 31:24  |        |         |              | Reserved                                                       |
| 23:16  |   ro   |   0x1   | CHIP_TYPE    | Read of this register shows the type of chip using this block. |
|  15:8  |   ro   |   0x3   | HW_REVISION  | Read of this register shows the revision of this block.        |
|  7:0   |   ro   |   0x3   | ABI_REVISION | Read of this register shows the ABI of this block.             |

## MODULE_ENABLE
Module enable register
- Offset: `0x20`
- Reset default: `0x9`
- Reset mask: `0xf`
- Register enable: [`ME_REGWEN`](#me_regwen)

### Fields

```wavejson
{"reg": [{"name": "MODULE_ENABLE", "bits": 4, "attr": ["rw"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name                                           |
|:------:|:------:|:-------:|:-----------------------------------------------|
|  31:4  |        |         | Reserved                                       |
|  3:0   |   rw   |   0x9   | [MODULE_ENABLE](#module_enable--module_enable) |

### MODULE_ENABLE . MODULE_ENABLE
Setting this field to `kMultiBitBool4True` will enable the ENTROPY_SRC module. Setting this field to `kMultiBitBool4False` will effectively reset the module.
The modules of the entropy complex may only be enabled and disabled in a specific order, see Programmers Guide for details.

## CONF
Configuration register
- Offset: `0x24`
- Reset default: `0x909099`
- Reset mask: `0x3f0f0ff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "FIPS_ENABLE", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ENTROPY_DATA_REG_ENABLE", "bits": 4, "attr": ["rw"], "rotate": -90}, {"bits": 4}, {"name": "THRESHOLD_SCOPE", "bits": 4, "attr": ["rw"], "rotate": -90}, {"bits": 4}, {"name": "RNG_BIT_ENABLE", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "RNG_BIT_SEL", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 250}}
```

|  Bits  |  Type  |  Reset  | Name                                                      |
|:------:|:------:|:-------:|:----------------------------------------------------------|
| 31:26  |        |         | Reserved                                                  |
| 25:24  |   rw   |   0x0   | [RNG_BIT_SEL](#conf--rng_bit_sel)                         |
| 23:20  |   rw   |   0x9   | [RNG_BIT_ENABLE](#conf--rng_bit_enable)                   |
| 19:16  |        |         | Reserved                                                  |
| 15:12  |   rw   |   0x9   | [THRESHOLD_SCOPE](#conf--threshold_scope)                 |
|  11:8  |        |         | Reserved                                                  |
|  7:4   |   rw   |   0x9   | [ENTROPY_DATA_REG_ENABLE](#conf--entropy_data_reg_enable) |
|  3:0   |   rw   |   0x9   | [FIPS_ENABLE](#conf--fips_enable)                         |

### CONF . RNG_BIT_SEL
When the above bit iset, this field selects which bit from the RNG bus will
be processed when in single RNG bit mode.
This two bit field selects the RNG bit stream:
0b00: RNG bit 0
0b01: RNG bit 1
0b10: RNG bit 2
0b11: RNG bit 3

### CONF . RNG_BIT_ENABLE
Setting this field to `kMultiBitBool4True` enables the single RNG bit mode, where only one bit is sampled.
Note that the ENTROPY_SRC block can only generate FIPS qualified entropy if this field is set to `kMultiBitBool4False`.
Additional requirements to generate FIPS qualified entropy are i) that [`CONF.FIPS_ENABLE`](#conf) is set to `kMultiBitBool4True`, and ii) that at most one of the [`ENTROPY_CONTROL.ES_ROUTE`](#entropy_control) and [`ENTROPY_CONTROL.ES_TYPE`](#entropy_control) fields but not both are set to `kMultiBitBool4True`.

### CONF . THRESHOLD_SCOPE
This field controls the scope (either by-line or by-sum) of the health checks.
If set to `kMultiBitBool4True`, the Adaptive Proportion and Markov Tests will accumulate all RNG input lines into a single score, and thresholds will be applied to the sum all the entropy input lines.
If set to `kMultiBitBool4False`, the RNG input lines are all scored individually.
A statistical deviation in any one input line, be it due to coincidence or failure, will force rejection of the sample, and count toward the total alert count.

### CONF . ENTROPY_DATA_REG_ENABLE
Setting this field to `kMultiBitBool4True` will enable reading entropy values from the [`ENTROPY_DATA`](#entropy_data) register.
This function also requires that the otp_en_entropy_src_fw_read input is set to `kMultiBitBool8True`.

### CONF . FIPS_ENABLE
Setting this field to `kMultiBitBool4True` selects the FIPS/CC compliant mode (or short FIPS mode).
In this mode, the ENTROPY_SRC block can generate FIPS qualified entropy.
Additional requirements to generate FIPS qualified entropy are i) that at most one of the [`ENTROPY_CONTROL.ES_ROUTE`](#entropy_control) and [`ENTROPY_CONTROL.ES_TYPE`](#entropy_control) fields are set to `kMultiBitBool4True` but not both, and ii) that [`CONF.RNG_BIT_ENABLE`](#conf) is set to `kMultiBitBool4False`.

Setting this field to `kMultiBitBool4False` selects the boot-time / bypass mode in which the hardware conditioning is bypassed.


## ENTROPY_CONTROL
Entropy control register
- Offset: `0x28`
- Reset default: `0x99`
- Reset mask: `0xff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "ES_ROUTE", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "ES_TYPE", "bits": 4, "attr": ["rw"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name                                   |
|:------:|:------:|:-------:|:---------------------------------------|
|  31:8  |        |         | Reserved                               |
|  7:4   |   rw   |   0x9   | [ES_TYPE](#entropy_control--es_type)   |
|  3:0   |   rw   |   0x9   | [ES_ROUTE](#entropy_control--es_route) |

### ENTROPY_CONTROL . ES_TYPE
When this field is `kMultiBitBool4False`, the hardware conditioning inside the ENTROPY_SRC block is enabled.
Setting this field to `kMultiBitBool4True` will bypass the hardware conditioning.
For this to work, also [`ENTROPY_CONTROL.ES_ROUTE`](#entropy_control) needs to be set to `kMultiBitBool4True` to route the unconditioned, raw entropy to the [`ENTROPY_DATA`](#entropy_data) register.
Alternatively, the hardware conditioning can be bypassed by setting [`CONF.FIPS_ENABLE`](#conf) to `kMultiBitBool4False` to disable FIPS mode and enable bypass / boot-time mode.
In both cases, the ENTROPY_SRC block will not generate FIPS qualified entropy.

To generate FIPS qualified entropy, i) [`CONF.FIPS_ENABLE`](#conf) needs to be set to `kMultiBitBool4True`, ii) [`CONF.RNG_BIT_ENABLE`](#conf) needs to be set to `kMultiBitBool4False`, and iii) at most one of the [`ENTROPY_CONTROL.ES_ROUTE`](#entropy_control) and [`ENTROPY_CONTROL.ES_TYPE`](#entropy_control) fields needs to be set to `kMultiBitBool4True` but not both.

### ENTROPY_CONTROL . ES_ROUTE
When this field is `kMultiBitBool4False`, the generated entropy will be forwarded out of this module to the hardware interface.
Setting this field to `kMultiBitBool4True` routes the generated entropy to the [`ENTROPY_DATA`](#entropy_data) register to be read by firmware.
Note that for [`ENTROPY_DATA`](#entropy_data) to become readable, also [`CONF.ENTROPY_DATA_REG_ENABLE`](#conf) needs to be set to `kMultiBitBool4True`.
In addition, the otp_en_entropy_src_fw_read input needs to be set to `kMultiBitBool8True`.

## ENTROPY_DATA
Entropy data bits
- Offset: `0x2c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "ENTROPY_DATA", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                        |
|:------:|:------:|:-------:|:--------------------------------------------|
|  31:0  |   ro   |    x    | [ENTROPY_DATA](#entropy_data--entropy_data) |

### ENTROPY_DATA . ENTROPY_DATA
A read of this register provides generated entropy bits to firmware.
For this to work also [`CONF.ENTROPY_DATA_REG_ENABLE`](#conf) needs to be set to `kMultiBitBool4True`.
In addition, the otp_en_entropy_src_fw_read input needs to be set to `kMultiBitBool8True`.

## HEALTH_TEST_WINDOWS
Health test windows register
- Offset: `0x30`
- Reset default: `0x600200`
- Reset mask: `0xffffffff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "FIPS_WINDOW", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "BYPASS_WINDOW", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                 |
|:------:|:------:|:-------:|:-----------------------------------------------------|
| 31:16  |   rw   |  0x60   | [BYPASS_WINDOW](#health_test_windows--bypass_window) |
|  15:0  |   rw   |  0x200  | [FIPS_WINDOW](#health_test_windows--fips_window)     |

### HEALTH_TEST_WINDOWS . BYPASS_WINDOW
This is the window size for all health tests when running in bypass mode.
This mode is active after reset for the first and only test run, or when this mode is programmed by firmware by setting [`CONF.FIPS_ENABLE`](#conf) to `kMultiBitBool4False`.
The default value is (384 bits * 1 clock/4 bits);

Note that currently only a window size of 384 is supported and tested (this corresponds to the register default value 0x60).
Do not use any other values, unless you know what you are doing.

### HEALTH_TEST_WINDOWS . FIPS_WINDOW
This is the window size for all health tests.
This value is used when entropy is being tested in FIPS/CC compliance mode (for simplicity referred to as FIPS mode).
The default value is (2048 bits * 1 clock/4 bits);

## REPCNT_THRESHOLDS
Repetition count test thresholds register
- Offset: `0x34`
- Reset default: `0xffffffff`
- Reset mask: `0xffffffff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "FIPS_THRESH", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "BYPASS_THRESH", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                               |
|:------:|:------:|:-------:|:---------------------------------------------------|
| 31:16  |   rw   | 0xffff  | [BYPASS_THRESH](#repcnt_thresholds--bypass_thresh) |
|  15:0  |   rw   | 0xffff  | [FIPS_THRESH](#repcnt_thresholds--fips_thresh)     |

### REPCNT_THRESHOLDS . BYPASS_THRESH
This is the threshold size for the repetition count health test
   running in bypass mode. This mode is active after reset for the
   first and only test run, or when this mode is programmed by firmware.
   This register must be written before the module is enabled.
   Writing to this register will only update the register if the
   written value is less than the current value of this register.
   A read from this register always reflects the current value.

### REPCNT_THRESHOLDS . FIPS_THRESH
This is the threshold size for the repetition count health test.
   This value is used in FIPS mode.
   This register must be written before the module is enabled.
   Writing to this register will only update the register if the
   written value is less than the current value of this register.
   A read from this register always reflects the current value.

## REPCNTS_THRESHOLDS
Repetition count symbol test thresholds register
- Offset: `0x38`
- Reset default: `0xffffffff`
- Reset mask: `0xffffffff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "FIPS_THRESH", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "BYPASS_THRESH", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                |
|:------:|:------:|:-------:|:----------------------------------------------------|
| 31:16  |   rw   | 0xffff  | [BYPASS_THRESH](#repcnts_thresholds--bypass_thresh) |
|  15:0  |   rw   | 0xffff  | [FIPS_THRESH](#repcnts_thresholds--fips_thresh)     |

### REPCNTS_THRESHOLDS . BYPASS_THRESH
This is the threshold size for the repetition count symbol health test
   running in bypass mode. This mode is active after reset for the
   first and only test run, or when this mode is programmed by firmware.
   This register must be written before the module is enabled.
   Writing to this register will only update the register if the
   written value is less than the current value of this register.
   A read from this register always reflects the current value.

### REPCNTS_THRESHOLDS . FIPS_THRESH
This is the threshold size for the repetition count symbol health test.
   This value is used in FIPS mode.
   This register must be written before the module is enabled.
   Writing to this register will only update the register if the
   written value is less than the current value of this register.
   A read from this register always reflects the current value.

## ADAPTP_HI_THRESHOLDS
Adaptive proportion test high thresholds register
- Offset: `0x3c`
- Reset default: `0xffffffff`
- Reset mask: `0xffffffff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "FIPS_THRESH", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "BYPASS_THRESH", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                  |
|:------:|:------:|:-------:|:------------------------------------------------------|
| 31:16  |   rw   | 0xffff  | [BYPASS_THRESH](#adaptp_hi_thresholds--bypass_thresh) |
|  15:0  |   rw   | 0xffff  | [FIPS_THRESH](#adaptp_hi_thresholds--fips_thresh)     |

### ADAPTP_HI_THRESHOLDS . BYPASS_THRESH
This is the threshold size for the adaptive proportion health test
   running in bypass mode. This mode is active after reset for the
   first and only test run, or when this mode is programmed by firmware.
   This register must be written before the module is enabled.
   Writing to this register will only update the register if the
   written value is less than the current value of this register.
   A read from this register always reflects the current value.

### ADAPTP_HI_THRESHOLDS . FIPS_THRESH
This is the threshold size for the adaptive proportion health test.
   This value is used in FIPS mode.
   This register must be written before the module is enabled.
   Writing to this register will only update the register if the
   written value is less than the current value of this register.
   A read from this register always reflects the current value.

## ADAPTP_LO_THRESHOLDS
Adaptive proportion test low thresholds register
- Offset: `0x40`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "FIPS_THRESH", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "BYPASS_THRESH", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                  |
|:------:|:------:|:-------:|:------------------------------------------------------|
| 31:16  |   rw   |   0x0   | [BYPASS_THRESH](#adaptp_lo_thresholds--bypass_thresh) |
|  15:0  |   rw   |   0x0   | [FIPS_THRESH](#adaptp_lo_thresholds--fips_thresh)     |

### ADAPTP_LO_THRESHOLDS . BYPASS_THRESH
This is the threshold size for the adaptive proportion health test
   running in bypass mode. This mode is active after reset for the
   first and only test run, or when this mode is programmed by firmware.
   This register must be written before the module is enabled.
   Writing to this register will only update the register if the
   written value is greater than the current value of this register.
   A read from this register always reflects the current value.

### ADAPTP_LO_THRESHOLDS . FIPS_THRESH
This is the threshold size for the adaptive proportion health test.
   This value is used in FIPS mode.
   This register must be written before the module is enabled.
   Writing to this register will only update the register if the
   written value is greater than the current value of this register.
   A read from this register always reflects the current value.

## BUCKET_THRESHOLDS
Bucket test thresholds register
- Offset: `0x44`
- Reset default: `0xffffffff`
- Reset mask: `0xffffffff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "FIPS_THRESH", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "BYPASS_THRESH", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                               |
|:------:|:------:|:-------:|:---------------------------------------------------|
| 31:16  |   rw   | 0xffff  | [BYPASS_THRESH](#bucket_thresholds--bypass_thresh) |
|  15:0  |   rw   | 0xffff  | [FIPS_THRESH](#bucket_thresholds--fips_thresh)     |

### BUCKET_THRESHOLDS . BYPASS_THRESH
This is the threshold size for the bucket health test
   running in bypass mode. This mode is active after reset for the
   first and only test run, or when this mode is programmed by firmware.
   This register must be written before the module is enabled.
   Writing to this register will only update the register if the
   written value is less than the current value of this register.
   A read from this register always reflects the current value.

### BUCKET_THRESHOLDS . FIPS_THRESH
This is the threshold size for the bucket health test.
   This value is used in FIPS mode.
   This register must be written before the module is enabled.
   Writing to this register will only update the register if the
   written value is less than the current value of this register.
   A read from this register always reflects the current value.

## MARKOV_HI_THRESHOLDS
Markov test high thresholds register
- Offset: `0x48`
- Reset default: `0xffffffff`
- Reset mask: `0xffffffff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "FIPS_THRESH", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "BYPASS_THRESH", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                  |
|:------:|:------:|:-------:|:------------------------------------------------------|
| 31:16  |   rw   | 0xffff  | [BYPASS_THRESH](#markov_hi_thresholds--bypass_thresh) |
|  15:0  |   rw   | 0xffff  | [FIPS_THRESH](#markov_hi_thresholds--fips_thresh)     |

### MARKOV_HI_THRESHOLDS . BYPASS_THRESH
This is the threshold size for the Markov health test
   running in bypass mode. This mode is active after reset for the
   first and only test run, or when this mode is programmed by firmware.
   This register must be written before the module is enabled.
   Writing to this register will only update the register if the
   written value is less than the current value of this register.
   A read from this register always reflects the current value.

### MARKOV_HI_THRESHOLDS . FIPS_THRESH
This is the threshold size for the Markov health test.
   This value is used in FIPS mode.
   This register must be written before the module is enabled.
   Writing to this register will only update the register if the
   written value is less than the current value of this register.
   A read from this register always reflects the current value.

## MARKOV_LO_THRESHOLDS
Markov test low thresholds register
- Offset: `0x4c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "FIPS_THRESH", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "BYPASS_THRESH", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                  |
|:------:|:------:|:-------:|:------------------------------------------------------|
| 31:16  |   rw   |   0x0   | [BYPASS_THRESH](#markov_lo_thresholds--bypass_thresh) |
|  15:0  |   rw   |   0x0   | [FIPS_THRESH](#markov_lo_thresholds--fips_thresh)     |

### MARKOV_LO_THRESHOLDS . BYPASS_THRESH
This is the threshold size for the Markov health test
   running in bypass mode. This mode is active after reset for the
   first and only test run, or when this mode is programmed by firmware.
   This register must be written before the module is enabled.
   Writing to this register will only update the register if the
   written value is greater than the current value of this register.
   A read from this register always reflects the current value.

### MARKOV_LO_THRESHOLDS . FIPS_THRESH
This is the threshold size for the Markov health test.
   This value is used in FIPS mode.
   This register must be written before the module is enabled.
   Writing to this register will only update the register if the
   written value is greater than the current value of this register.
   A read from this register always reflects the current value.

## EXTHT_HI_THRESHOLDS
External health test high thresholds register
- Offset: `0x50`
- Reset default: `0xffffffff`
- Reset mask: `0xffffffff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "FIPS_THRESH", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "BYPASS_THRESH", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                 |
|:------:|:------:|:-------:|:-----------------------------------------------------|
| 31:16  |   rw   | 0xffff  | [BYPASS_THRESH](#extht_hi_thresholds--bypass_thresh) |
|  15:0  |   rw   | 0xffff  | [FIPS_THRESH](#extht_hi_thresholds--fips_thresh)     |

### EXTHT_HI_THRESHOLDS . BYPASS_THRESH
This is the threshold size for the external health test
   running in bypass mode. This mode is active after reset for the
   first and only test run, or when this mode is programmed by firmware.
   This register must be written before the module is enabled.
   Writing to this register will only update the register if the
   written value is less than the current value of this register.
   A read from this register always reflects the current value.

### EXTHT_HI_THRESHOLDS . FIPS_THRESH
This is the threshold size for the external health test.
   This value is used in FIPS mode.
   This register must be written before the module is enabled.
   Writing to this register will only update the register if the
   written value is less than the current value of this register.
   A read from this register always reflects the current value.

## EXTHT_LO_THRESHOLDS
External health test low thresholds register
- Offset: `0x54`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "FIPS_THRESH", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "BYPASS_THRESH", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                 |
|:------:|:------:|:-------:|:-----------------------------------------------------|
| 31:16  |   rw   |   0x0   | [BYPASS_THRESH](#extht_lo_thresholds--bypass_thresh) |
|  15:0  |   rw   |   0x0   | [FIPS_THRESH](#extht_lo_thresholds--fips_thresh)     |

### EXTHT_LO_THRESHOLDS . BYPASS_THRESH
This is the threshold size for the external health test
   running in bypass mode. This mode is active after reset for the
   first and only test run, or when this mode is programmed by firmware.
   This register must be written before the module is enabled.
   Writing to this register will only update the register if the
   written value is greater than the current value of this register.
   A read from this register always reflects the current value.

### EXTHT_LO_THRESHOLDS . FIPS_THRESH
This is the threshold size for the external health test.
   This value is used in FIPS mode.
   This register must be written before the module is enabled.
   Writing to this register will only update the register if the
   written value is greater than the current value of this register.
   A read from this register always reflects the current value.

## REPCNT_HI_WATERMARKS
Repetition count test high watermarks register
- Offset: `0x58`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "FIPS_WATERMARK", "bits": 16, "attr": ["ro"], "rotate": 0}, {"name": "BYPASS_WATERMARK", "bits": 16, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                             |
|:------:|:------:|:-------:|:-----------------|:--------------------------------------------------------|
| 31:16  |   ro   |    x    | BYPASS_WATERMARK | High watermark value of the REPCNT test in bypass mode. |
|  15:0  |   ro   |    x    | FIPS_WATERMARK   | High watermark value of the REPCNT test in FIPS mode.   |

## REPCNTS_HI_WATERMARKS
Repetition count symbol test high watermarks register
- Offset: `0x5c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "FIPS_WATERMARK", "bits": 16, "attr": ["ro"], "rotate": 0}, {"name": "BYPASS_WATERMARK", "bits": 16, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                              |
|:------:|:------:|:-------:|:-----------------|:---------------------------------------------------------|
| 31:16  |   ro   |    x    | BYPASS_WATERMARK | High watermark value of the REPCNTS test in bypass mode. |
|  15:0  |   ro   |    x    | FIPS_WATERMARK   | High watermark value of the REPCNTS test in FIPS mode.   |

## ADAPTP_HI_WATERMARKS
Adaptive proportion test high watermarks register
- Offset: `0x60`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "FIPS_WATERMARK", "bits": 16, "attr": ["ro"], "rotate": 0}, {"name": "BYPASS_WATERMARK", "bits": 16, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                          |
|:------:|:------:|:-------:|:-----------------|:---------------------------------------------------------------------|
| 31:16  |   ro   |    x    | BYPASS_WATERMARK | High watermark value of the adaptive proportion test in bypass mode. |
|  15:0  |   ro   |    x    | FIPS_WATERMARK   | High watermark value of the adaptive proportion test in FIPS mode.   |

## ADAPTP_LO_WATERMARKS
Adaptive proportion test low watermarks register
- Offset: `0x64`
- Reset default: `0xffffffff`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "FIPS_WATERMARK", "bits": 16, "attr": ["ro"], "rotate": 0}, {"name": "BYPASS_WATERMARK", "bits": 16, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                         |
|:------:|:------:|:-------:|:-----------------|:--------------------------------------------------------------------|
| 31:16  |   ro   | 0xffff  | BYPASS_WATERMARK | Low watermark value of the adaptive proportion test in bypass mode. |
|  15:0  |   ro   | 0xffff  | FIPS_WATERMARK   | Low watermark value of the adaptive proportion test in FIPS mode.   |

## EXTHT_HI_WATERMARKS
External health test high watermarks register
- Offset: `0x68`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "FIPS_WATERMARK", "bits": 16, "attr": ["ro"], "rotate": 0}, {"name": "BYPASS_WATERMARK", "bits": 16, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                      |
|:------:|:------:|:-------:|:-----------------|:-----------------------------------------------------------------|
| 31:16  |   ro   |    x    | BYPASS_WATERMARK | High watermark value of the external health test in bypass mode. |
|  15:0  |   ro   |    x    | FIPS_WATERMARK   | High watermark value of the external health test in FIPS mode.   |

## EXTHT_LO_WATERMARKS
External health test low watermarks register
- Offset: `0x6c`
- Reset default: `0xffffffff`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "FIPS_WATERMARK", "bits": 16, "attr": ["ro"], "rotate": 0}, {"name": "BYPASS_WATERMARK", "bits": 16, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                     |
|:------:|:------:|:-------:|:-----------------|:----------------------------------------------------------------|
| 31:16  |   ro   | 0xffff  | BYPASS_WATERMARK | Low watermark value of the external health test in bypass mode. |
|  15:0  |   ro   | 0xffff  | FIPS_WATERMARK   | Low watermark value of the external health test in FIPS mode.   |

## BUCKET_HI_WATERMARKS
Bucket test high watermarks register
- Offset: `0x70`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "FIPS_WATERMARK", "bits": 16, "attr": ["ro"], "rotate": 0}, {"name": "BYPASS_WATERMARK", "bits": 16, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                             |
|:------:|:------:|:-------:|:-----------------|:--------------------------------------------------------|
| 31:16  |   ro   |    x    | BYPASS_WATERMARK | High watermark value of the bucket test in bypass mode. |
|  15:0  |   ro   |    x    | FIPS_WATERMARK   | High watermark value of the bucket test in FIPS mode.   |

## MARKOV_HI_WATERMARKS
Markov test high watermarks register
- Offset: `0x74`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "FIPS_WATERMARK", "bits": 16, "attr": ["ro"], "rotate": 0}, {"name": "BYPASS_WATERMARK", "bits": 16, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                             |
|:------:|:------:|:-------:|:-----------------|:--------------------------------------------------------|
| 31:16  |   ro   |    x    | BYPASS_WATERMARK | High watermark value of the Markov test in bypass mode. |
|  15:0  |   ro   |    x    | FIPS_WATERMARK   | High watermark value of the Markov test in FIPS mode.   |

## MARKOV_LO_WATERMARKS
Markov test low watermarks register
- Offset: `0x78`
- Reset default: `0xffffffff`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "FIPS_WATERMARK", "bits": 16, "attr": ["ro"], "rotate": 0}, {"name": "BYPASS_WATERMARK", "bits": 16, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                            |
|:------:|:------:|:-------:|:-----------------|:-------------------------------------------------------|
| 31:16  |   ro   | 0xffff  | BYPASS_WATERMARK | Low watermark value of the Markov test in bypass mode. |
|  15:0  |   ro   | 0xffff  | FIPS_WATERMARK   | Low watermark value of the Markov test in FIPS mode.   |

## REPCNT_TOTAL_FAILS
Repetition count test failure counter register
- Offset: `0x7c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "REPCNT_TOTAL_FAILS", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                                                                                                  |
|:------:|:------:|:-------:|:-------------------|:-----------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   ro   |    x    | REPCNT_TOTAL_FAILS | This register will hold a running count of test failures observed    during normal operation. It will persist until cleared. |

## REPCNTS_TOTAL_FAILS
Repetition count symbol test failure counter register
- Offset: `0x80`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "REPCNTS_TOTAL_FAILS", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                | Description                                                                                                                  |
|:------:|:------:|:-------:|:--------------------|:-----------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   ro   |    x    | REPCNTS_TOTAL_FAILS | This register will hold a running count of test failures observed    during normal operation. It will persist until cleared. |

## ADAPTP_HI_TOTAL_FAILS
Adaptive proportion high test failure counter register
- Offset: `0x84`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "ADAPTP_HI_TOTAL_FAILS", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                                                                                                  |
|:------:|:------:|:-------:|:----------------------|:-----------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   ro   |    x    | ADAPTP_HI_TOTAL_FAILS | This register will hold a running count of test failures observed    during normal operation. It will persist until cleared. |

## ADAPTP_LO_TOTAL_FAILS
Adaptive proportion low test failure counter register
- Offset: `0x88`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "ADAPTP_LO_TOTAL_FAILS", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                                                                                                  |
|:------:|:------:|:-------:|:----------------------|:-----------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   ro   |    x    | ADAPTP_LO_TOTAL_FAILS | This register will hold a running count of test failures observed    during normal operation. It will persist until cleared. |

## BUCKET_TOTAL_FAILS
Bucket test failure counter register
- Offset: `0x8c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "BUCKET_TOTAL_FAILS", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                                                                                                  |
|:------:|:------:|:-------:|:-------------------|:-----------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   ro   |    x    | BUCKET_TOTAL_FAILS | This register will hold a running count of test failures observed    during normal operation. It will persist until cleared. |

## MARKOV_HI_TOTAL_FAILS
Markov high test failure counter register
- Offset: `0x90`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "MARKOV_HI_TOTAL_FAILS", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                                                                                                  |
|:------:|:------:|:-------:|:----------------------|:-----------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   ro   |    x    | MARKOV_HI_TOTAL_FAILS | This register will hold a running count of test failures observed    during normal operation. It will persist until cleared. |

## MARKOV_LO_TOTAL_FAILS
Markov low test failure counter register
- Offset: `0x94`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "MARKOV_LO_TOTAL_FAILS", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                                                                                                  |
|:------:|:------:|:-------:|:----------------------|:-----------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   ro   |    x    | MARKOV_LO_TOTAL_FAILS | This register will hold a running count of test failures observed    during normal operation. It will persist until cleared. |

## EXTHT_HI_TOTAL_FAILS
External health test high threshold failure counter register
- Offset: `0x98`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "EXTHT_HI_TOTAL_FAILS", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                                                  |
|:------:|:------:|:-------:|:---------------------|:-----------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   ro   |    x    | EXTHT_HI_TOTAL_FAILS | This register will hold a running count of test failures observed    during normal operation. It will persist until cleared. |

## EXTHT_LO_TOTAL_FAILS
External health test low threshold failure counter register
- Offset: `0x9c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "EXTHT_LO_TOTAL_FAILS", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                                                  |
|:------:|:------:|:-------:|:---------------------|:-----------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   ro   |    x    | EXTHT_LO_TOTAL_FAILS | This register will hold a running count of test failures observed    during normal operation. It will persist until cleared. |

## ALERT_THRESHOLD
Alert threshold register
- Offset: `0xa0`
- Reset default: `0xfffd0002`
- Reset mask: `0xffffffff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "ALERT_THRESHOLD", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "ALERT_THRESHOLD_INV", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                | Description                                                                                                                                    |
|:------:|:------:|:-------:|:--------------------|:-----------------------------------------------------------------------------------------------------------------------------------------------|
| 31:16  |   rw   | 0xfffd  | ALERT_THRESHOLD_INV | This should be set to the value above, but inverted.                                                                                           |
|  15:0  |   rw   |   0x2   | ALERT_THRESHOLD     | This is the threshold size that will signal an alert when    value is reached. A value of zero will disable alerts.    The default value is 2. |

## ALERT_SUMMARY_FAIL_COUNTS
Alert summary failure counts register
- Offset: `0xa4`
- Reset default: `0x0`
- Reset mask: `0xffff`

### Fields

```wavejson
{"reg": [{"name": "ANY_FAIL_COUNT", "bits": 16, "attr": ["ro"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                         |
|:------:|:------:|:-------:|:-------------------------------------------------------------|
| 31:16  |        |         | Reserved                                                     |
|  15:0  |   ro   |    x    | [ANY_FAIL_COUNT](#alert_summary_fail_counts--any_fail_count) |

### ALERT_SUMMARY_FAIL_COUNTS . ANY_FAIL_COUNT
This field will hold a running count of
   the total alert count, which is a sum of all of the other
   counters in the [`ALERT_FAIL_COUNTS`](#alert_fail_counts) register.
   It will be reset after every passing test sequence unless in firmware override mode (extract and insert only).
   If an alert is signaled, this value will persist until it is cleared.

## ALERT_FAIL_COUNTS
Alert failure counts register
- Offset: `0xa8`
- Reset default: `0x0`
- Reset mask: `0xfffffff0`

### Fields

```wavejson
{"reg": [{"bits": 4}, {"name": "REPCNT_FAIL_COUNT", "bits": 4, "attr": ["ro"], "rotate": -90}, {"name": "ADAPTP_HI_FAIL_COUNT", "bits": 4, "attr": ["ro"], "rotate": -90}, {"name": "ADAPTP_LO_FAIL_COUNT", "bits": 4, "attr": ["ro"], "rotate": -90}, {"name": "BUCKET_FAIL_COUNT", "bits": 4, "attr": ["ro"], "rotate": -90}, {"name": "MARKOV_HI_FAIL_COUNT", "bits": 4, "attr": ["ro"], "rotate": -90}, {"name": "MARKOV_LO_FAIL_COUNT", "bits": 4, "attr": ["ro"], "rotate": -90}, {"name": "REPCNTS_FAIL_COUNT", "bits": 4, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                                                             |
|:------:|:------:|:-------:|:-----------------------------------------------------------------|
| 31:28  |   ro   |    x    | [REPCNTS_FAIL_COUNT](#alert_fail_counts--repcnts_fail_count)     |
| 27:24  |   ro   |    x    | [MARKOV_LO_FAIL_COUNT](#alert_fail_counts--markov_lo_fail_count) |
| 23:20  |   ro   |    x    | [MARKOV_HI_FAIL_COUNT](#alert_fail_counts--markov_hi_fail_count) |
| 19:16  |   ro   |    x    | [BUCKET_FAIL_COUNT](#alert_fail_counts--bucket_fail_count)       |
| 15:12  |   ro   |    x    | [ADAPTP_LO_FAIL_COUNT](#alert_fail_counts--adaptp_lo_fail_count) |
|  11:8  |   ro   |    x    | [ADAPTP_HI_FAIL_COUNT](#alert_fail_counts--adaptp_hi_fail_count) |
|  7:4   |   ro   |    x    | [REPCNT_FAIL_COUNT](#alert_fail_counts--repcnt_fail_count)       |
|  3:0   |        |         | Reserved                                                         |

### ALERT_FAIL_COUNTS . REPCNTS_FAIL_COUNT
This field will hold a running count of test failures that
   contribute to the total alert count.
   It will be reset after every passing test sequence unless in firmware override mode (extract and insert only).
   If an alert is signaled, this value will persist until it is cleared.

### ALERT_FAIL_COUNTS . MARKOV_LO_FAIL_COUNT
This field will hold a running count of test failures that
   contribute to the total alert count.
   It will be reset after every passing test sequence unless in firmware override mode (extract and insert only).
   If an alert is signaled, this value will persist until it is cleared.

### ALERT_FAIL_COUNTS . MARKOV_HI_FAIL_COUNT
This field will hold a running count of test failures that
   contribute to the total alert count.
   It will be reset after every passing test sequence unless in firmware override mode (extract and insert only).
   If an alert is signaled, this value will persist until it is cleared.

### ALERT_FAIL_COUNTS . BUCKET_FAIL_COUNT
This field will hold a running count of test failures that
   contribute to the total alert count.
   It will be reset after every passing test sequence unless in firmware override mode (extract and insert only).
   If an alert is signaled, this value will persist until it is cleared.

### ALERT_FAIL_COUNTS . ADAPTP_LO_FAIL_COUNT
This field will hold a running count of test failures that
   contribute to the total alert count.
   It will be reset after every passing test sequence unless in firmware override mode (extract and insert only).
   If an alert is signaled, this value will persist until it is cleared.

### ALERT_FAIL_COUNTS . ADAPTP_HI_FAIL_COUNT
This field will hold a running count of test failures that
   contribute to the total alert count.
   It will be reset after every passing test sequence unless in firmware override mode (extract and insert only).
   If an alert is signaled, this value will persist until it is cleared.

### ALERT_FAIL_COUNTS . REPCNT_FAIL_COUNT
This field will hold a running count of test failures that
   contribute to the total alert count.
   It will be reset after every passing test sequence unless in firmware override mode (extract and insert only).
   If an alert is signaled, this value will persist until it is cleared.

## EXTHT_FAIL_COUNTS
External health test alert failure counts register
- Offset: `0xac`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "EXTHT_HI_FAIL_COUNT", "bits": 4, "attr": ["ro"], "rotate": -90}, {"name": "EXTHT_LO_FAIL_COUNT", "bits": 4, "attr": ["ro"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 210}}
```

|  Bits  |  Type  |  Reset  | Name                                                           |
|:------:|:------:|:-------:|:---------------------------------------------------------------|
|  31:8  |        |         | Reserved                                                       |
|  7:4   |   ro   |    x    | [EXTHT_LO_FAIL_COUNT](#extht_fail_counts--extht_lo_fail_count) |
|  3:0   |   ro   |    x    | [EXTHT_HI_FAIL_COUNT](#extht_fail_counts--extht_hi_fail_count) |

### EXTHT_FAIL_COUNTS . EXTHT_LO_FAIL_COUNT
This field will hold a running count of test failures that
   contribute to the total alert count.
   It will be reset after every passing test sequence unless in firmware override mode (extract and insert only).
   If an alert is signaled, this value will persist until it is cleared.

### EXTHT_FAIL_COUNTS . EXTHT_HI_FAIL_COUNT
This field will hold a running count of test failures that
   contribute to the total alert count.
   It will be reset after every passing test sequence unless in firmware override mode (extract and insert only).
   If an alert is signaled, this value will persist until it is cleared.

## FW_OV_CONTROL
Firmware override control register
- Offset: `0xb0`
- Reset default: `0x99`
- Reset mask: `0xff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "FW_OV_MODE", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "FW_OV_ENTROPY_INSERT", "bits": 4, "attr": ["rw"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                                                         |
|:------:|:------:|:-------:|:-------------------------------------------------------------|
|  31:8  |        |         | Reserved                                                     |
|  7:4   |   rw   |   0x9   | [FW_OV_ENTROPY_INSERT](#fw_ov_control--fw_ov_entropy_insert) |
|  3:0   |   rw   |   0x9   | [FW_OV_MODE](#fw_ov_control--fw_ov_mode)                     |

### FW_OV_CONTROL . FW_OV_ENTROPY_INSERT
Setting this field to `kMultiBitBool4True` allows firmware to extract entropy bits by reading the observe FIFO (see [`FW_OV_RD_DATA`](#fw_ov_rd_data)) and insert entropy bits into the entropy flow by writing the [`FW_OV_WR_DATA`](#fw_ov_wr_data) register.
This is useful e.g. for performing additional health tests and/or firmware-based conditioning.
For this to work, [`FW_OV_CONTROL.FW_OV_MODE`](#fw_ov_control) needs to be set to `kMultiBitBool4True`.
In addition, the otp_en_entropy_src_fw_over input needs to be set to `kMultiBitBool8True`.

Firmware can use the hardware conditioning for the inserted entropy bits (see [`FW_OV_SHA3_START`](#fw_ov_sha3_start)).

Note that if the field is set to `kMultiBitBool4True`, post-health test entropy bits do NOT continue to flow through the hardware pipeline.
Also, the [`FW_OV_CONTROL.FW_OV_MODE`](#fw_ov_control) bit must be set.
The observe FIFO will collect 2 kBit of contiguous entropy bits.
Any entropy bits arriving after the observe FIFO is full are being discarded.
Firmware has to read out the entire observe FIFO to restart entropy collection.
Only entropy bits inserted by firmware by writing [`FW_OV_WR_DATA`](#fw_ov_wr_data) may eventually reach the block hardware interface.

### FW_OV_CONTROL . FW_OV_MODE
Setting this field to `kMultiBitBool4True` will put the entropy flow in firmware override mode.
In this mode, firmware can monitor the post-health test entropy by reading
the observe FIFO (see [`FW_OV_RD_DATA`](#fw_ov_rd_data)).
For this to work, the otp_en_entropy_src_fw_over input needs to be set to `kMultiBitBool8True`.

Note that the post-health test entropy bits collected in the observe FIFO continue to flow through the hardware pipeline and may eventually reach the block hardware interface.

## FW_OV_SHA3_START
Firmware override sha3 block start control register
- Offset: `0xb4`
- Reset default: `0x9`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "FW_OV_INSERT_START", "bits": 4, "attr": ["rw"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name                                                        |
|:------:|:------:|:-------:|:------------------------------------------------------------|
|  31:4  |        |         | Reserved                                                    |
|  3:0   |   rw   |   0x9   | [FW_OV_INSERT_START](#fw_ov_sha3_start--fw_ov_insert_start) |

### FW_OV_SHA3_START . FW_OV_INSERT_START
Setting this field to `kMultiBitBool4True` will instruct the ENTROPY_SRC main state machine to start the SHA3 process and be ready to accept entropy data.
This field should be set prior to writing the [`FW_OV_WR_DATA`](#fw_ov_wr_data) register.
Once all data has been written, this field should be set to `kMultiBitBool4False`.
Once that happened, the SHA3 block will finish processing and push the result into the esfinal FIFO.

Note that clearing this bit to `kMultiBitBool4False` while there is still unprocessed entropy in [`FW_OV_WR_DATA`](#fw_ov_wr_data) will start the SHA3 engine before data can be added to the input message, and will also signal a recoverable alert in [`RECOV_ALERT_STS.ES_FW_OV_DISABLE_ALERT.`](#recov_alert_sts)
To avoid this, check that [`FW_OV_WR_FIFO_FULL`](#fw_ov_wr_fifo_full) is clear before setting this field to `kMultiBitBool4False`.

## FW_OV_WR_FIFO_FULL
Firmware override FIFO write full status register
- Offset: `0xb8`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "FW_OV_WR_FIFO_FULL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                                                                                                                                                                                                     |
|:------:|:------:|:-------:|:-------------------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                    | Reserved                                                                                                                                                                                                                        |
|   0    |   ro   |    x    | FW_OV_WR_FIFO_FULL | "When this bit is clear, writes to the FW_OV_WR_DATA register are allowed. If this bit is set, it is the equivalent to a FIFO full condition, and writes to the FW_OV_WR_DATA register must be delayed until this bit is reset. |

## FW_OV_RD_FIFO_OVERFLOW
Firmware override observe FIFO overflow status
- Offset: `0xbc`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "FW_OV_RD_FIFO_OVERFLOW", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 240}}
```

|  Bits  |  Type  |  Reset  | Name                                                                      |
|:------:|:------:|:-------:|:--------------------------------------------------------------------------|
|  31:1  |        |         | Reserved                                                                  |
|   0    |  rw0c  |   0x0   | [FW_OV_RD_FIFO_OVERFLOW](#fw_ov_rd_fifo_overflow--fw_ov_rd_fifo_overflow) |

### FW_OV_RD_FIFO_OVERFLOW . FW_OV_RD_FIFO_OVERFLOW
This bit is set by hardware whenever RNG data is lost due to an overflow condition
in the observe FIFO. The RNG data rate is slow enough that firmware should always
be able to keep up. This register meanwhile provides an additional check to confirm
that bytes read from the [`FW_OV_RD_DATA`](#fw_ov_rd_data) register represent contiguous RNG samples.
If an overflow event occurs, this bit must be cleared by software.

## FW_OV_RD_DATA
Firmware override observe FIFO read register
- Offset: `0xc0`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "FW_OV_RD_DATA", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                           |
|:------:|:------:|:-------:|:-----------------------------------------------|
|  31:0  |   ro   |    x    | [FW_OV_RD_DATA](#fw_ov_rd_data--fw_ov_rd_data) |

### FW_OV_RD_DATA . FW_OV_RD_DATA
A read of this register pops and returns the top of the observe FIFO.
For this to work, the [`FW_OV_CONTROL.FW_OV_MODE`](#fw_ov_control) field needs to be set to `kMultiBitBool4True`
In addition, the otp_en_entropy_src_fw_over input needs to be set to `kMultiBitBool8True`.

## FW_OV_WR_DATA
Firmware override FIFO write register
- Offset: `0xc4`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "FW_OV_WR_DATA", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                           |
|:------:|:------:|:-------:|:-----------------------------------------------|
|  31:0  |   wo   |    x    | [FW_OV_WR_DATA](#fw_ov_wr_data--fw_ov_wr_data) |

### FW_OV_WR_DATA . FW_OV_WR_DATA
A write to this register will insert entropy back into the entropy source module flow.
For this to work, both the [`FW_OV_CONTROL.FW_OV_MODE`](#fw_ov_control) and [`FW_OV_CONTROL.FW_OV_ENTROPY_INSERT`](#fw_ov_control) fields need to be set to `kMultiBitBool4True`.
In addition, the otp_en_entropy_src_fw_over input needs to be set to `kMultiBitBool8True`.

## OBSERVE_FIFO_THRESH
Observe FIFO threshold register
- Offset: `0xc8`
- Reset default: `0x20`
- Reset mask: `0x7f`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "OBSERVE_FIFO_THRESH", "bits": 7, "attr": ["rw"], "rotate": -90}, {"bits": 25}], "config": {"lanes": 1, "fontsize": 10, "vspace": 210}}
```

|  Bits  |  Type  |  Reset  | Name                | Description                                                                                                                                                                             |
|:------:|:------:|:-------:|:--------------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:7  |        |         |                     | Reserved                                                                                                                                                                                |
|  6:0   |   rw   |  0x20   | OBSERVE_FIFO_THRESH | This field will set the threshold that the depth of the observe FIFO will be compared with when setting the interrupt status bit. Note: a value of zero is reserved and not to be used. |

## OBSERVE_FIFO_DEPTH
Observe FIFO depth register
- Offset: `0xcc`
- Reset default: `0x0`
- Reset mask: `0x7f`

### Fields

```wavejson
{"reg": [{"name": "OBSERVE_FIFO_DEPTH", "bits": 7, "attr": ["ro"], "rotate": -90}, {"bits": 25}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                                 |
|:------:|:------:|:-------:|:-------------------|:------------------------------------------------------------|
|  31:7  |        |         |                    | Reserved                                                    |
|  6:0   |   ro   |    x    | OBSERVE_FIFO_DEPTH | This field will hold the current depth of the observe FIFO. |

## DEBUG_STATUS
Debug status register
- Offset: `0xd0`
- Reset default: `0x10000`
- Reset mask: `0x303ff`

### Fields

```wavejson
{"reg": [{"name": "ENTROPY_FIFO_DEPTH", "bits": 3, "attr": ["ro"], "rotate": -90}, {"name": "SHA3_FSM", "bits": 3, "attr": ["ro"], "rotate": -90}, {"name": "SHA3_BLOCK_PR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SHA3_SQUEEZING", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SHA3_ABSORBED", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SHA3_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 6}, {"name": "MAIN_SM_IDLE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "MAIN_SM_BOOT_DONE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 14}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                                         |
|:------:|:------:|:-------:|:-------------------|:--------------------------------------------------------------------|
| 31:18  |        |         |                    | Reserved                                                            |
|   17   |   ro   |    x    | MAIN_SM_BOOT_DONE  | The entropy_src main state machine is in the boot phase done state. |
|   16   |   ro   |   0x1   | MAIN_SM_IDLE       | The entropy_src main state machine is in the idle state.            |
| 15:10  |        |         |                    | Reserved                                                            |
|   9    |   ro   |    x    | SHA3_ERR           | This is a logic-or of all of the SHA3 error signals.                |
|   8    |   ro   |    x    | SHA3_ABSORBED      | This is the SHA3 absorbed signal current state.                     |
|   7    |   ro   |    x    | SHA3_SQUEEZING     | This is the SHA3 squeezing signal current state.                    |
|   6    |   ro   |    x    | SHA3_BLOCK_PR      | This is the SHA3 block processed signal current state.              |
|  5:3   |   ro   |    x    | SHA3_FSM           | This is the SHA3 finite state machine current state.                |
|  2:0   |   ro   |    x    | ENTROPY_FIFO_DEPTH | This is the depth of the entropy source FIFO.                       |

## RECOV_ALERT_STS
Recoverable alert status register
- Offset: `0xd4`
- Reset default: `0x0`
- Reset mask: `0x1ffaf`

### Fields

```wavejson
{"reg": [{"name": "FIPS_ENABLE_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "ENTROPY_DATA_REG_EN_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "MODULE_ENABLE_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "THRESHOLD_SCOPE_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 1}, {"name": "RNG_BIT_ENABLE_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 1}, {"name": "FW_OV_SHA3_START_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "FW_OV_MODE_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "FW_OV_ENTROPY_INSERT_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "ES_ROUTE_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "ES_TYPE_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "ES_MAIN_SM_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "ES_BUS_CMP_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "ES_THRESH_CFG_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "ES_FW_OV_WR_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "ES_FW_OV_DISABLE_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 15}], "config": {"lanes": 1, "fontsize": 10, "vspace": 340}}
```

|  Bits  |  Type  |  Reset  | Name                                                                                   |
|:------:|:------:|:-------:|:---------------------------------------------------------------------------------------|
| 31:17  |        |         | Reserved                                                                               |
|   16   |  rw0c  |   0x0   | [ES_FW_OV_DISABLE_ALERT](#recov_alert_sts--es_fw_ov_disable_alert)                     |
|   15   |  rw0c  |   0x0   | [ES_FW_OV_WR_ALERT](#recov_alert_sts--es_fw_ov_wr_alert)                               |
|   14   |  rw0c  |   0x0   | [ES_THRESH_CFG_ALERT](#recov_alert_sts--es_thresh_cfg_alert)                           |
|   13   |  rw0c  |   0x0   | [ES_BUS_CMP_ALERT](#recov_alert_sts--es_bus_cmp_alert)                                 |
|   12   |  rw0c  |   0x0   | [ES_MAIN_SM_ALERT](#recov_alert_sts--es_main_sm_alert)                                 |
|   11   |  rw0c  |   0x0   | [ES_TYPE_FIELD_ALERT](#recov_alert_sts--es_type_field_alert)                           |
|   10   |  rw0c  |   0x0   | [ES_ROUTE_FIELD_ALERT](#recov_alert_sts--es_route_field_alert)                         |
|   9    |  rw0c  |   0x0   | [FW_OV_ENTROPY_INSERT_FIELD_ALERT](#recov_alert_sts--fw_ov_entropy_insert_field_alert) |
|   8    |  rw0c  |   0x0   | [FW_OV_MODE_FIELD_ALERT](#recov_alert_sts--fw_ov_mode_field_alert)                     |
|   7    |  rw0c  |   0x0   | [FW_OV_SHA3_START_FIELD_ALERT](#recov_alert_sts--fw_ov_sha3_start_field_alert)         |
|   6    |        |         | Reserved                                                                               |
|   5    |  rw0c  |   0x0   | [RNG_BIT_ENABLE_FIELD_ALERT](#recov_alert_sts--rng_bit_enable_field_alert)             |
|   4    |        |         | Reserved                                                                               |
|   3    |  rw0c  |   0x0   | [THRESHOLD_SCOPE_FIELD_ALERT](#recov_alert_sts--threshold_scope_field_alert)           |
|   2    |  rw0c  |   0x0   | [MODULE_ENABLE_FIELD_ALERT](#recov_alert_sts--module_enable_field_alert)               |
|   1    |  rw0c  |   0x0   | [ENTROPY_DATA_REG_EN_FIELD_ALERT](#recov_alert_sts--entropy_data_reg_en_field_alert)   |
|   0    |  rw0c  |   0x0   | [FIPS_ENABLE_FIELD_ALERT](#recov_alert_sts--fips_enable_field_alert)                   |

### RECOV_ALERT_STS . ES_FW_OV_DISABLE_ALERT
This bit is set when [`FW_OV_SHA3_START`](#fw_ov_sha3_start) has been set to `kMultiBitBool4False`, without waiting for the bypass packer FIFO to clear.
The final entropy entry in the FIFO will not be included in the SHA3 digest.
(Rather it will be added to the subsequent SHA3 digest.)
To avoid this alert, monitor [`FW_OV_WR_FIFO_FULL`](#fw_ov_wr_fifo_full) before clearing [`FW_OV_SHA3_START.`](#fw_ov_sha3_start)
This alert only applies when both [`FW_OV_CONTROL.FW_OV_MODE`](#fw_ov_control) and [`FW_OV_CONTROL.FW_OV_ENTROPY_INSERT`](#fw_ov_control) are set to `kMultiBitBool4True`.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . ES_FW_OV_WR_ALERT
This bit is set when the packer FIFO has been written but was full at the time,
and in both FW_OV_MODE and FW_OV_ENTROPY_INSERT modes.
This alert would normally be the result of not monitoring the [`FW_OV_WR_FIFO_FULL`](#fw_ov_wr_fifo_full)
register before each write to the [`FW_OV_WR_DATA`](#fw_ov_wr_data) register.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . ES_THRESH_CFG_ALERT
This bit is set when the [`ALERT_THRESHOLD`](#alert_threshold) register is not configured properly.
The upper field must be the exact inverse of the lower field.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . ES_BUS_CMP_ALERT
This bit is set when the interal entropy bus value is equal to the prior
valid value on the bus, indicating a possible attack.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . ES_MAIN_SM_ALERT
This bit is set when the main state machine detects a threshhold failure state.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . ES_TYPE_FIELD_ALERT
This bit is set when the ES_TYPE field in the [`ENTROPY_CONTROL`](#entropy_control) register is set to a value other than `kMultiBitBool4False` or `kMultiBitBool4True`.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . ES_ROUTE_FIELD_ALERT
This bit is set when the ES_ROUTE field in the [`ENTROPY_CONTROL`](#entropy_control) register is set to a value other than `kMultiBitBool4False` or `kMultiBitBool4True`.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . FW_OV_ENTROPY_INSERT_FIELD_ALERT
This bit is set when the FW_OV_ENTROPY_INSERT field in the [`FW_OV_CONTROL`](#fw_ov_control) register is set to a value other than `kMultiBitBool4False` or `kMultiBitBool4True`.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . FW_OV_MODE_FIELD_ALERT
This bit is set when the FW_OV_MODE field in the [`FW_OV_CONTROL`](#fw_ov_control) register is set to a value other than `kMultiBitBool4False` or `kMultiBitBool4True`.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . FW_OV_SHA3_START_FIELD_ALERT
This bit is set when the FW_OV_SHA3_START field in the [`FW_OV_SHA3_START`](#fw_ov_sha3_start) register is set to a value other than `kMultiBitBool4False` or `kMultiBitBool4True`.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . RNG_BIT_ENABLE_FIELD_ALERT
This bit is set when the RNG_BIT_ENABLE field in the [`CONF`](#conf) register is set to a value other than `kMultiBitBool4False` or `kMultiBitBool4True`.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . THRESHOLD_SCOPE_FIELD_ALERT
This bit is set when the THRESHOLD_SCOPE field in the [`CONF`](#conf) register is set to a value other than `kMultiBitBool4False` or `kMultiBitBool4True`.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . MODULE_ENABLE_FIELD_ALERT
This bit is set when the MODULE_ENABLE field in the [`MODULE_ENABLE`](#module_enable) register is set to a value other than `kMultiBitBool4False` or `kMultiBitBool4True`.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . ENTROPY_DATA_REG_EN_FIELD_ALERT
This bit is set when the ENTROPY_DATA_REG_ENABLE field in the [`CONF`](#conf) register is set to a value other than `kMultiBitBool4False` or `kMultiBitBool4True`.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . FIPS_ENABLE_FIELD_ALERT
This bit is set when the FIPS_ENABLE field in the [`CONF`](#conf) register is set to a value other than `kMultiBitBool4False` or `kMultiBitBool4True`.
Writing a zero resets this status bit.

## ERR_CODE
Hardware detection of error conditions status register
- Offset: `0xd8`
- Reset default: `0x0`
- Reset mask: `0x71f00007`

### Fields

```wavejson
{"reg": [{"name": "SFIFO_ESRNG_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SFIFO_OBSERVE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SFIFO_ESFINAL_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 17}, {"name": "ES_ACK_SM_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ES_MAIN_SM_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ES_CNTR_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SHA3_STATE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SHA3_RST_STORAGE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 3}, {"name": "FIFO_WRITE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FIFO_READ_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FIFO_STATE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 1}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                                                    |
|:------:|:------:|:-------:|:--------------------------------------------------------|
|   31   |        |         | Reserved                                                |
|   30   |   ro   |   0x0   | [FIFO_STATE_ERR](#err_code--fifo_state_err)             |
|   29   |   ro   |   0x0   | [FIFO_READ_ERR](#err_code--fifo_read_err)               |
|   28   |   ro   |   0x0   | [FIFO_WRITE_ERR](#err_code--fifo_write_err)             |
| 27:25  |        |         | Reserved                                                |
|   24   |   ro   |   0x0   | [SHA3_RST_STORAGE_ERR](#err_code--sha3_rst_storage_err) |
|   23   |   ro   |   0x0   | [SHA3_STATE_ERR](#err_code--sha3_state_err)             |
|   22   |   ro   |   0x0   | [ES_CNTR_ERR](#err_code--es_cntr_err)                   |
|   21   |   ro   |   0x0   | [ES_MAIN_SM_ERR](#err_code--es_main_sm_err)             |
|   20   |   ro   |   0x0   | [ES_ACK_SM_ERR](#err_code--es_ack_sm_err)               |
|  19:3  |        |         | Reserved                                                |
|   2    |   ro   |   0x0   | [SFIFO_ESFINAL_ERR](#err_code--sfifo_esfinal_err)       |
|   1    |   ro   |   0x0   | [SFIFO_OBSERVE_ERR](#err_code--sfifo_observe_err)       |
|   0    |   ro   |   0x0   | [SFIFO_ESRNG_ERR](#err_code--sfifo_esrng_err)           |

### ERR_CODE . FIFO_STATE_ERR
This bit will be set to one when any of the source bits (bits 0 through 1 of this
this register) are asserted as a result of an error pulse generated from
any FIFO where both the empty and full status bits are set.
This bit will stay set until the next reset.

### ERR_CODE . FIFO_READ_ERR
This bit will be set to one when any of the source bits (bits 0 through 1 of this
this register) are asserted as a result of an error pulse generated from
any empty FIFO that has recieved a read pulse.
This bit will stay set until the next reset.

### ERR_CODE . FIFO_WRITE_ERR
This bit will be set to one when any of the source bits (bits 0 through 1 of this
this register) are asserted as a result of an error pulse generated from
any full FIFO that has been recieved a write pulse.
This bit will stay set until the next reset.

### ERR_CODE . SHA3_RST_STORAGE_ERR
This bit will be set to one when a SHA3_RST_STORAGE_ERR signal being
active has been detected.
This error will signal a fatal alert, and also an interrupt if enabled.
This bit will stay set until the next reset.

### ERR_CODE . SHA3_STATE_ERR
This bit will be set to one when a SHA3 state error has been detected.
This error will signal a fatal alert, and also an interrupt if enabled.
This bit will stay set until the next reset.

### ERR_CODE . ES_CNTR_ERR
This bit will be set to one when a hardened counter has detected an error
condition. This error will signal a fatal alert, and also
an interrupt if enabled.
This bit will stay set until the next reset.

### ERR_CODE . ES_MAIN_SM_ERR
This bit will be set to one when an illegal state has been detected for the
ES main stage state machine. This error will signal a fatal alert, and also
an interrupt if enabled.
This bit will stay set until the next reset.

### ERR_CODE . ES_ACK_SM_ERR
This bit will be set to one when an illegal state has been detected for the
ES ack stage state machine. This error will signal a fatal alert, and also
an interrupt if enabled.
This bit will stay set until the next reset.

### ERR_CODE . SFIFO_ESFINAL_ERR
This bit will be set to one when an error has been detected for the
esfinal FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
This bit will stay set until the next reset.

### ERR_CODE . SFIFO_OBSERVE_ERR
This bit will be set to one when an error has been detected for the
observe FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
This bit will stay set until the next reset.

### ERR_CODE . SFIFO_ESRNG_ERR
This bit will be set to one when an error has been detected for the
esrng FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
This bit will stay set until the next reset.

## ERR_CODE_TEST
Test error conditions register
- Offset: `0xdc`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "ERR_CODE_TEST", "bits": 5, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name                                           |
|:------:|:------:|:-------:|:-----------------------------------------------|
|  31:5  |        |         | Reserved                                       |
|  4:0   |   rw   |   0x0   | [ERR_CODE_TEST](#err_code_test--err_code_test) |

### ERR_CODE_TEST . ERR_CODE_TEST
Setting this field will set the bit number for which an error
will be forced in the hardware. This bit number is that same one
found in the [`ERR_CODE`](#err_code) register. The action of writing this
register will force an error pulse. The sole purpose of this
register is to test that any error properly propagates to either
an interrupt or an alert.

## MAIN_SM_STATE
Main state machine state debug register
- Offset: `0xe0`
- Reset default: `0xf5`
- Reset mask: `0x1ff`

### Fields

```wavejson
{"reg": [{"name": "MAIN_SM_STATE", "bits": 9, "attr": ["ro"], "rotate": 0}, {"bits": 23}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                                                                                    |
|:------:|:------:|:-------:|:--------------|:-------------------------------------------------------------------------------------------------------------------------------|
|  31:9  |        |         |               | Reserved                                                                                                                       |
|  8:0   |   ro   |  0xf5   | MAIN_SM_STATE | This is the state of the ENTROPY_SRC main state machine. See the RTL file `entropy_src_main_sm` for the meaning of the values. |


<!-- END CMDGEN -->
