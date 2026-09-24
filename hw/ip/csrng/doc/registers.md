# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/csrng/data/csrng.hjson -->
## Summary

| Name                                                        | Offset   |   Length | Description                                                                |
|:------------------------------------------------------------|:---------|---------:|:---------------------------------------------------------------------------|
| csrng.[`INTR_STATE`](#intr_state)                           | 0x0      |        4 | Interrupt State Register                                                   |
| csrng.[`INTR_ENABLE`](#intr_enable)                         | 0x4      |        4 | Interrupt Enable Register                                                  |
| csrng.[`INTR_TEST`](#intr_test)                             | 0x8      |        4 | Interrupt Test Register                                                    |
| csrng.[`ALERT_TEST`](#alert_test)                           | 0xc      |        4 | Alert Test Register                                                        |
| csrng.[`REGWEN`](#regwen)                                   | 0x10     |        4 | Register write enable for all control registers                            |
| csrng.[`CTRL`](#ctrl)                                       | 0x14     |        4 | Control register                                                           |
| csrng.[`CMD_REQ`](#cmd_req)                                 | 0x18     |        4 | Command request register                                                   |
| csrng.[`RESEED_INTERVAL`](#reseed_interval)                 | 0x1c     |        4 | CSRNG maximum number of generate requests allowed between reseeds register |
| csrng.[`RESEED_COUNTER_0`](#reseed_counter)                 | 0x20     |        4 | Reseed counter.                                                            |
| csrng.[`RESEED_COUNTER_1`](#reseed_counter)                 | 0x24     |        4 | Reseed counter.                                                            |
| csrng.[`RESEED_COUNTER_2`](#reseed_counter)                 | 0x28     |        4 | Reseed counter.                                                            |
| csrng.[`SW_CMD_STS`](#sw_cmd_sts)                           | 0x2c     |        4 | Application interface command status register                              |
| csrng.[`GENBITS_VLD`](#genbits_vld)                         | 0x30     |        4 | Generate bits returned valid register                                      |
| csrng.[`GENBITS`](#genbits)                                 | 0x34     |        4 | Generate bits returned register                                            |
| csrng.[`INT_STATE_CMD_REGWEN`](#int_state_cmd_regwen)       | 0x38     |        4 | Register write enable for [`INT_STATE_CMD`](#int_state_cmd)                |
| csrng.[`INT_STATE_CMD`](#int_state_cmd)                     | 0x3c     |        4 | Internal state EXPORT/IMPORT/RESUME command register                       |
| csrng.[`INT_STATE_NUM`](#int_state_num)                     | 0x40     |        4 | Internal state number register                                             |
| csrng.[`INT_STATE_VAL`](#int_state_val)                     | 0x44     |        4 | Internal state read/write access register                                  |
| csrng.[`INT_STATE_CMD_GEN_VAL`](#int_state_cmd_gen_val)     | 0x48     |        4 | Internal state Generate-resume bookkeeping read/write access register      |
| csrng.[`INT_STATE_CMD_ADATA_VAL`](#int_state_cmd_adata_val) | 0x4c     |        4 | Internal state Generate-resume additional data read/write access register  |
| csrng.[`INT_STATE_CMD_STS_0`](#int_state_cmd_sts)           | 0x50     |        4 | Internal state command status register                                     |
| csrng.[`INT_STATE_CMD_STS_1`](#int_state_cmd_sts)           | 0x54     |        4 | Internal state command status register                                     |
| csrng.[`INT_STATE_CMD_STS_2`](#int_state_cmd_sts)           | 0x58     |        4 | Internal state command status register                                     |
| csrng.[`FIPS_FORCE`](#fips_force)                           | 0x5c     |        4 | FIPS/CC compliance flag forcing register                                   |
| csrng.[`GEN_ABORT_REGWEN`](#gen_abort_regwen)               | 0x60     |        4 | Register write enable for [`GEN_ABORT`](#gen_abort)                        |
| csrng.[`GEN_ABORT_0`](#gen_abort)                           | 0x64     |        4 | Generate command abort request register                                    |
| csrng.[`GEN_ABORT_1`](#gen_abort)                           | 0x68     |        4 | Generate command abort request register                                    |
| csrng.[`GEN_ABORT_2`](#gen_abort)                           | 0x6c     |        4 | Generate command abort request register                                    |
| csrng.[`GEN_ABORT_STATUS_0`](#gen_abort_status)             | 0x70     |        4 | Generate command abort completion status register                          |
| csrng.[`GEN_ABORT_STATUS_1`](#gen_abort_status)             | 0x74     |        4 | Generate command abort completion status register                          |
| csrng.[`GEN_ABORT_STATUS_2`](#gen_abort_status)             | 0x78     |        4 | Generate command abort completion status register                          |
| csrng.[`HW_EXC_STS`](#hw_exc_sts)                           | 0x7c     |        4 | Hardware instance exception status register                                |
| csrng.[`RECOV_ALERT_STS`](#recov_alert_sts)                 | 0x80     |        4 | Recoverable alert status register                                          |
| csrng.[`ERR_CODE`](#err_code)                               | 0x84     |        4 | Hardware detection of error conditions status register                     |
| csrng.[`ERR_CODE_TEST`](#err_code_test)                     | 0x88     |        4 | Test error conditions register                                             |
| csrng.[`MAIN_SM_STATE`](#main_sm_state)                     | 0x8c     |        4 | Main state machine state debug register                                    |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "cs_cmd_req_done", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "cs_entropy_req", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "cs_hw_inst_exc", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "cs_fatal_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "cs_int_state_stopped", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                                                              |
|:------:|:------:|:-------:|:---------------------|:-----------------------------------------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                                                                                 |
|   4    |  rw1c  |   0x0   | cs_int_state_stopped | Asserted when a CSRNG instance targeted by an internal-state EXPORT or IMPORT command has quiesced and is ready for state export/import. |
|   3    |  rw1c  |   0x0   | cs_fatal_err         | Asserted when a FIFO error or a fatal alert occurs. Check the [`ERR_CODE`](#err_code) register to get more information.                  |
|   2    |  rw1c  |   0x0   | cs_hw_inst_exc       | Asserted when a hardware-attached CSRNG instance encounters a command exception                                                          |
|   1    |  rw1c  |   0x0   | cs_entropy_req       | Asserted when a request for entropy has been made.                                                                                       |
|   0    |  rw1c  |   0x0   | cs_cmd_req_done      | Asserted when a command request is completed.                                                                                            |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "cs_cmd_req_done", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "cs_entropy_req", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "cs_hw_inst_exc", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "cs_fatal_err", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "cs_int_state_stopped", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                    |
|:------:|:------:|:-------:|:---------------------|:-------------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                       |
|   4    |   rw   |   0x0   | cs_int_state_stopped | Enable interrupt when [`INTR_STATE.cs_int_state_stopped`](#intr_state) is set. |
|   3    |   rw   |   0x0   | cs_fatal_err         | Enable interrupt when [`INTR_STATE.cs_fatal_err`](#intr_state) is set.         |
|   2    |   rw   |   0x0   | cs_hw_inst_exc       | Enable interrupt when [`INTR_STATE.cs_hw_inst_exc`](#intr_state) is set.       |
|   1    |   rw   |   0x0   | cs_entropy_req       | Enable interrupt when [`INTR_STATE.cs_entropy_req`](#intr_state) is set.       |
|   0    |   rw   |   0x0   | cs_cmd_req_done      | Enable interrupt when [`INTR_STATE.cs_cmd_req_done`](#intr_state) is set.      |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "cs_cmd_req_done", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "cs_entropy_req", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "cs_hw_inst_exc", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "cs_fatal_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "cs_int_state_stopped", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                             |
|:------:|:------:|:-------:|:---------------------|:------------------------------------------------------------------------|
|  31:5  |        |         |                      | Reserved                                                                |
|   4    |   wo   |   0x0   | cs_int_state_stopped | Write 1 to force [`INTR_STATE.cs_int_state_stopped`](#intr_state) to 1. |
|   3    |   wo   |   0x0   | cs_fatal_err         | Write 1 to force [`INTR_STATE.cs_fatal_err`](#intr_state) to 1.         |
|   2    |   wo   |   0x0   | cs_hw_inst_exc       | Write 1 to force [`INTR_STATE.cs_hw_inst_exc`](#intr_state) to 1.       |
|   1    |   wo   |   0x0   | cs_entropy_req       | Write 1 to force [`INTR_STATE.cs_entropy_req`](#intr_state) to 1.       |
|   0    |   wo   |   0x0   | cs_cmd_req_done      | Write 1 to force [`INTR_STATE.cs_cmd_req_done`](#intr_state) to 1.      |

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

## REGWEN
Register write enable for all control registers
- Offset: `0x10`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                            |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                               |
|   0    |  rw0c  |   0x1   | REGWEN | When true, all writeable registers can be modified. When false, they become read-only. |

## CTRL
Control register
- Offset: `0x14`
- Reset default: `0x9999`
- Reset mask: `0xffff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "ENABLE", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "SW_APP_ENABLE", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "INT_STATE_ENABLE", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "FIPS_FORCE_ENABLE", "bits": 4, "attr": ["rw"], "rotate": -90}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name                                          |
|:------:|:------:|:-------:|:----------------------------------------------|
| 31:16  |        |         | Reserved                                      |
| 15:12  |   rw   |   0x9   | [FIPS_FORCE_ENABLE](#ctrl--fips_force_enable) |
|  11:8  |   rw   |   0x9   | [INT_STATE_ENABLE](#ctrl--int_state_enable)   |
|  7:4   |   rw   |   0x9   | [SW_APP_ENABLE](#ctrl--sw_app_enable)         |
|  3:0   |   rw   |   0x9   | [ENABLE](#ctrl--enable)                       |

### CTRL . FIPS_FORCE_ENABLE
Setting this field to kMultiBitBool4True enables forcing the FIPS/CC compliance flag to true via the [`FIPS_FORCE`](#fips_force) register.

### CTRL . INT_STATE_ENABLE
Setting this field to kMultiBitBool4True will enable issuing EXPORT/IMPORT/RESUME commands via [`INT_STATE_CMD.`](#int_state_cmd)
Issuing EXPORT/IMPORT/RESUME commands to the internal state of the enabled instances is enabled only if the
otp_en_csrng_sw_app_read input vector is set to the enable encoding.

### CTRL . SW_APP_ENABLE
Setting this field to kMultiBitBool4True will enable reading from the [`GENBITS`](#genbits) register.
This application interface for software (register based) will be enabled
only if the otp_en_csrng_sw_app_read input vector is set to the enable encoding.

### CTRL . ENABLE
Setting this field to kMultiBitBool4True will enable the CSRNG module. The modules
of the entropy complex may only be enabled and disabled in a specific order, see
Programmers Guide for details.

## CMD_REQ
Command request register
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "CMD_REQ", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name    | Description                                                                                                                                                                         |
|:------:|:------:|:-------:|:--------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   wo   |   0x0   | CMD_REQ | Writing this request with defined CSRNG commands will initiate all possible CSRNG actions. The application interface must wait for the "ack" to return before issuing new commands. |

## RESEED_INTERVAL
CSRNG maximum number of generate requests allowed between reseeds register
- Offset: `0x1c`
- Reset default: `0xffffffff`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "RESEED_INTERVAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |   Reset    | Name                                                 |
|:------:|:------:|:----------:|:-----------------------------------------------------|
|  31:0  |   rw   | 0xffffffff | [RESEED_INTERVAL](#reseed_interval--reseed_interval) |

### RESEED_INTERVAL . RESEED_INTERVAL
Setting this field will set the number of generate requests that can be
made to CSRNG before a reseed request needs to be made.
This register supports a maximum of 2^32 requests between reseeds.
This register will be compared to a counter, which counts the number of
generate commands between reseed or instantiate commands.
If the counter reaches the value of this register, the violating command
will be acknowledged with a status error.
If the violating command was issued by a HW instance, an interrupt will
be triggered.

## RESEED_COUNTER
Reseed counter.

The per-instance reseed counter indicates the number of Generate requests that have been completed since new entropy input has been obtained with an Instantiate or a Reseed command.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name             | Offset   |
|:-----------------|:---------|
| RESEED_COUNTER_0 | 0x20     |
| RESEED_COUNTER_1 | 0x24     |
| RESEED_COUNTER_2 | 0x28     |


### Fields

```wavejson
{"reg": [{"name": "RESEED_COUNTER", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                                                                                                       |
|:------:|:------:|:-------:|:---------------|:------------------------------------------------------------------------------------------------------------------|
|  31:0  |   ro   |   0x0   | RESEED_COUNTER | Reseed Counter indicating the number of completed Generate requests since the last Instantiate or Reseed command. |

## SW_CMD_STS
Application interface command status register
- Offset: `0x2c`
- Reset default: `0x0`
- Reset mask: `0x3e`

### Fields

```wavejson
{"reg": [{"bits": 1}, {"name": "CMD_RDY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CMD_ACK", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CMD_STS", "bits": 3, "attr": ["ro"], "rotate": -90}, {"bits": 26}], "config": {"lanes": 1, "fontsize": 10, "vspace": 90}}
```

|  Bits  |  Type  |  Reset  | Name                            |
|:------:|:------:|:-------:|:--------------------------------|
|  31:6  |        |         | Reserved                        |
|  5:3   |   ro   |   0x0   | [CMD_STS](#sw_cmd_sts--cmd_sts) |
|   2    |   ro   |   0x0   | [CMD_ACK](#sw_cmd_sts--cmd_ack) |
|   1    |   ro   |   0x0   | [CMD_RDY](#sw_cmd_sts--cmd_rdy) |

### SW_CMD_STS . CMD_STS
This field represents the status code returned with the application command ack.
It is updated each time a command ack is asserted on the internal application
interface for software use.
To check whether a command was successful, wait for [`INTR_STATE.CS_CMD_REQ_DONE`](#intr_state) or
[`SW_CMD_STS.CMD_ACK`](#sw_cmd_sts) to be high and then check the value of this field.

| Value   | Name                | Description                                                                                                                                                                                                                                                                                                   |
|:--------|:--------------------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0x0     | SUCCESS             | Request completed successfully.                                                                                                                                                                                                                                                                               |
| 0x1     | INVALID_ACMD        | Request completed with an invalid application command error. This error indicates that the issued application command doesn't represent a valid operation.                                                                                                                                                    |
| 0x2     | INVALID_GEN_CMD     | Request completed with an invalid counter DRBG generation command error. This error indicates that CSRNG entropy was generated for a command that is not a Generate command. In this case the entropy should not be considered as valid.                                                                      |
| 0x3     | INVALID_CMD_SEQ     | This error indicates that the last command was issued out of sequence. This happens when a command other than Instantiate was issued without sending an Instantiate command first. This can also happen when an Uninstantiate command is sent without instantiating first.                                    |
| 0x4     | RESEED_CNT_EXCEEDED | This error indicates that the number of generate requests between reseeds exceeded the maximum number allowed (see [`RESEED_INTERVAL`](#reseed_interval)). This happens only for Generate commands.                                                                                                           |
| 0x5     | GEN_ABORTED         | This bit indicates that a Generate command for this instance was aborted via [`GEN_ABORT`](#gen_abort) before returning all requested genbits. The instance has been uninstantiated as a result and must be instantiated again before further commands will succeed. This happens only for Generate commands. |

Other values are reserved.

### SW_CMD_STS . CMD_ACK
This one bit field indicates when a SW command has been acknowledged by the CSRNG.
It is set to low each time a new command is written to [`CMD_REQ.`](#cmd_req)
The field is set to high once a SW command request has been acknowledged by the CSRNG.
0b0: The last SW command has not been acknowledged yet.
0b1: The last SW command has been acknowledged.
In case of a generate command the acknowledgement goes high after all of the requested entropy is consumed.

### SW_CMD_STS . CMD_RDY
This bit indicates when the command interface is ready to accept commands.
Before starting to write a new command to [`SW_CMD_REQ`](#sw_cmd_req), this field needs to be polled.
0b0: CSRNG is not ready to accept commands or the last command hasn't been acked yet.
0b1: CSRNG is ready to accept the next command.

## GENBITS_VLD
Generate bits returned valid register
- Offset: `0x30`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "GENBITS_VLD", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "GENBITS_FIPS", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                                                                                        |
|:------:|:------:|:-------:|:-------------|:-------------------------------------------------------------------------------------------------------------------|
|  31:2  |        |         |              | Reserved                                                                                                           |
|   1    |   ro   |    x    | GENBITS_FIPS | This bit is set when genbits are FIPS/CC compliant.                                                                |
|   0    |   ro   |    x    | GENBITS_VLD  | This bit is set when genbits are available on this application interface after a generate command has been issued. |

## GENBITS
Generate bits returned register
- Offset: `0x34`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "GENBITS", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                         |
|:------:|:------:|:-------:|:-----------------------------|
|  31:0  |   ro   |    x    | [GENBITS](#genbits--genbits) |

### GENBITS . GENBITS
Reading this register will get the generated bits that were requested with
the generate request. This register must be read four times for each request
made. For example, an application command generate request with
a `clen` value of 4 requires this register to be read 16 times to get all
of the data out of the FIFO path.
Note that for [`GENBITS`](#genbits) to be able to deliver random numbers, also [`CTRL.SW_APP_ENABLE`](#ctrl) needs to be set to `kMultiBitBool4True`.
In addition, the otp_en_csrng_sw_app_read input needs to be set to `kMultiBitBool8True`.
Otherwise, the register reads as 0.

## INT_STATE_CMD_REGWEN
Register write enable for [`INT_STATE_CMD`](#int_state_cmd)
- Offset: `0x38`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "INT_STATE_CMD_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                                                      |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                      | Reserved                                                                                                                         |
|   0    |  rw0c  |   0x1   | INT_STATE_CMD_REGWEN | When true, the [`INT_STATE_CMD`](#int_state_cmd) register can be written. When false, it becomes read-only until the next reset. |

## INT_STATE_CMD
Internal state EXPORT/IMPORT/RESUME command register
- Offset: `0x3c`
- Reset default: `0x999`
- Reset mask: `0xfff`
- Register enable: [`INT_STATE_CMD_REGWEN`](#int_state_cmd_regwen)

### Fields

```wavejson
{"reg": [{"name": "EXPORT_REQ", "bits": 4, "attr": ["rw1s"], "rotate": -90}, {"name": "IMPORT_REQ", "bits": 4, "attr": ["rw1s"], "rotate": -90}, {"name": "RESUME", "bits": 4, "attr": ["rw1s"], "rotate": 0}, {"bits": 20}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name                                     |
|:------:|:------:|:-------:|:-----------------------------------------|
| 31:12  |        |         | Reserved                                 |
|  11:8  |  rw1s  |   0x9   | [RESUME](#int_state_cmd--resume)         |
|  7:4   |  rw1s  |   0x9   | [IMPORT_REQ](#int_state_cmd--import_req) |
|  3:0   |  rw1s  |   0x9   | [EXPORT_REQ](#int_state_cmd--export_req) |

### INT_STATE_CMD . RESUME
Setting this field to kMultiBitBool4True resumes the command processing of the instance selected
by [`INT_STATE_NUM.`](#int_state_num)

### INT_STATE_CMD . IMPORT_REQ
Setting this field to kMultiBitBool4True requests that the instance selected by [`INT_STATE_NUM`](#int_state_num)
stops accepting and processing further commands, and quiesces as soon as it safely can, so that
its state can be overwritten via [`INT_STATE_VAL.`](#int_state_val)
Poll [`INT_STATE_CMD_STS.STOPPED`](#int_state_cmd_sts), or wait for [`INTR_STATE.CS_INT_STATE_STOPPED`](#intr_state), before writing
[`INT_STATE_VAL`](#int_state_val) or issuing a RESUME command.
Subsequent writes to [`INT_STATE_VAL`](#int_state_val) overwrite the state word by word.

### INT_STATE_CMD . EXPORT_REQ
Setting this field to kMultiBitBool4True requests that the instance selected by [`INT_STATE_NUM`](#int_state_num)
stops accepting and processing further commands, and quiesces as soon as it safely can, so that
its state can be read out via [`INT_STATE_VAL.`](#int_state_val)
Poll [`INT_STATE_CMD_STS.STOPPED`](#int_state_cmd_sts), or wait for [`INTR_STATE.CS_INT_STATE_STOPPED`](#intr_state), before reading
[`INT_STATE_VAL`](#int_state_val) or issuing a RESUME command.
Subsequent reads to [`INT_STATE_VAL`](#int_state_val) export the state word by word.

## INT_STATE_NUM
Internal state number register
- Offset: `0x40`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "INT_STATE_NUM", "bits": 4, "attr": ["rw"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name                                           |
|:------:|:------:|:-------:|:-----------------------------------------------|
|  31:4  |        |         | Reserved                                       |
|  3:0   |   rw   |   0x0   | [INT_STATE_NUM](#int_state_num--int_state_num) |

### INT_STATE_NUM . INT_STATE_NUM
Setting this field will set the number for which instance is targeted by
[`INT_STATE_CMD.`](#int_state_cmd) Up to 16 internal state values can be chosen
from this register. The actual number of valid internal state fields
is set by parameter NumHwApps plus 1 software app. For those selections that point
to reserved locations (greater than NumHwApps plus 1), the returned value
will be zero. Writing this register will also reset the internal read/write
pointer for the [`INT_STATE_VAL`](#int_state_val) register.
Note: This register should be read back after being written to ensure
that the [`INT_STATE_VAL`](#int_state_val) read back is accurate.

## INT_STATE_VAL
Internal state read/write access register
- Offset: `0x44`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "INT_STATE_VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                           |
|:------:|:------:|:-------:|:-----------------------------------------------|
|  31:0  |   rw   |    x    | [INT_STATE_VAL](#int_state_val--int_state_val) |

### INT_STATE_VAL . INT_STATE_VAL
Reading this register will dump out the contents of the selected instance's CTR_DRBG
state. Since this field is 448 bits wide, it will require 14 reads from this register
to gather the entire field. Once 14 reads have been done, the internal read/write
pointer (selects 32 bits of the 448 bit field) will reset to zero.

Writing this register is only meaningful while an IMPORT command is active for the
currently stopped and targeted instance (see [`INT_STATE_CMD`](#int_state_cmd)). Writes overwrite the state
word by word as they arrive. Reading while an IMPORT command is active returns the
already-written contents.

This register only covers the CTR_DRBG state (key/V/reseed counter/fips/instantiated).
If the targeted instance may have a Generate command paused mid-sequence that needs to
be resumed correctly, also see [`INT_STATE_CMD_GEN_VAL`](#int_state_cmd_gen_val) and [`INT_STATE_CMD_ADATA_VAL.`](#int_state_cmd_adata_val)

Note that for [`INT_STATE_VAL`](#int_state_val) to provide access to the internal state, also
[`CTRL.INT_STATE_ENABLE`](#ctrl) needs to be set to `kMultiBitBool4True`.
In addition, the otp_en_csrng_sw_app_read input needs to be set to `kMultiBitBool8True`.
Otherwise, the register reads as 0 and writes are dropped.

## INT_STATE_CMD_GEN_VAL
Internal state Generate-resume bookkeeping read/write access register
- Offset: `0x48`
- Reset default: `0x0`
- Reset mask: `0x3fff`

### Fields

```wavejson
{"reg": [{"name": "CMD_GEN_CNT", "bits": 12, "attr": ["rw"], "rotate": 0}, {"name": "CMD_GEN_FLAG", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "GENERATE_ADATA_VLD", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 18}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                                                                                                                                                                                    |
|:------:|:------:|:-------:|:-------------------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:14  |        |         |                    | Reserved                                                                                                                                                                                                       |
|   13   |   rw   |    x    | GENERATE_ADATA_VLD | Whether [`INT_STATE_CMD_ADATA_VAL`](#int_state_cmd_adata_val) currently holds valid additional data for the paused Generate command. Directly reflects/overwrites the internal generate_adata_vld_q flip-flop. |
|   12   |   rw   |    x    | CMD_GEN_FLAG       | Whether the selected instance has a Generate command paused mid-sequence. Directly reflects/overwrites the internal cmd_gen_flag_q flip-flop.                                                                  |
|  11:0  |   rw   |    x    | CMD_GEN_CNT        | Number of generate requests remaining in the Generate command that was paused mid-sequence for the selected instance. Directly reflects/overwrites the internal cmd_gen_cnt flip-flop.                         |

## INT_STATE_CMD_ADATA_VAL
Internal state Generate-resume additional data read/write access register
- Offset: `0x4c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "INT_STATE_CMD_ADATA_VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                                         |
|:------:|:------:|:-------:|:-----------------------------------------------------------------------------|
|  31:0  |   rw   |    x    | [INT_STATE_CMD_ADATA_VAL](#int_state_cmd_adata_val--int_state_cmd_adata_val) |

### INT_STATE_CMD_ADATA_VAL . INT_STATE_CMD_ADATA_VAL
Reading this register will dump out the additional data supplied to the Generate
command that was paused mid-sequence for the selected instance. Since this field is
384 bits wide, it will require 12 reads from this register to gather the entire
field. Once 12 reads have been done, the internal read/write pointer (selects 32
bits of the 384 bit field) will reset to zero.

Writing this register is only meaningful while an IMPORT command is active for the
currently stopped and targeted instance (see [`INT_STATE_CMD`](#int_state_cmd)). Writes overwrite the
additional data word by word as they arrive. Reading while an IMPORT command is
active returns the already-written (or defaulted) contents.

This register only covers the Generate-resume additional data. Accepting an IMPORT
command always first resets all Generate-resume bookkeeping, including this field,
to a "no Generate in progress" default, which then only changes for the words that
are subsequently written. If [`INT_STATE_CMD_GEN_VAL.GENERATE_ADATA_VLD`](#int_state_cmd_gen_val) reads
False, this register does not need to be read or written.

Note that for [`INT_STATE_CMD_ADATA_VAL`](#int_state_cmd_adata_val) to provide access to the internal state, also
[`CTRL.INT_STATE_ENABLE`](#ctrl) needs to be set to `kMultiBitBool4True`.
In addition, the otp_en_csrng_sw_app_read input needs to be set to `kMultiBitBool8True`.
Otherwise, the register reads as 0 and writes are dropped.

## INT_STATE_CMD_STS
Internal state command status register
- Reset default: `0x0`
- Reset mask: `0x1`

### Instances

| Name                | Offset   |
|:--------------------|:---------|
| INT_STATE_CMD_STS_0 | 0x50     |
| INT_STATE_CMD_STS_1 | 0x54     |
| INT_STATE_CMD_STS_2 | 0x58     |


### Fields

```wavejson
{"reg": [{"name": "STOPPED", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 90}}
```

|  Bits  |  Type  |  Reset  | Name                                   |
|:------:|:------:|:-------:|:---------------------------------------|
|  31:1  |        |         | Reserved                               |
|   0    |   ro   |   0x0   | [STOPPED](#int_state_cmd_sts--stopped) |

### INT_STATE_CMD_STS . STOPPED
Reflects whether this instance has quiesced following an accepted EXPORT/IMPORT
command, and is safe to read/write via [`INT_STATE_VAL`](#int_state_val)/[`INT_STATE_CMD_GEN_VAL`](#int_state_cmd_gen_val)/
[`INT_STATE_CMD_ADATA_VAL`](#int_state_cmd_adata_val) or resume via [`INT_STATE_CMD.RESUME.`](#int_state_cmd)
Also see [`INTR_STATE.CS_INT_STATE_STOPPED`](#intr_state), which fires for either command.

## FIPS_FORCE
FIPS/CC compliance flag forcing register
- Offset: `0x5c`
- Reset default: `0x0`
- Reset mask: `0x7`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "FIPS_FORCE", "bits": 3, "attr": ["rw"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name                                  |
|:------:|:------:|:-------:|:--------------------------------------|
|  31:3  |        |         | Reserved                              |
|  2:0   |   rw   |   0x0   | [FIPS_FORCE](#fips_force--fips_force) |

### FIPS_FORCE . FIPS_FORCE
Force the FIPS/CC compliance flag of individual instances to true.
This allows CSRNG to set the output FIPS/CC compliance flag to true despite running in fully deterministic mode (flag0 being true).
This can be useful e.g. for known-answer testing through entropy consumers accepting FIPS/CC compliant entropy only, or when firmware is used to derive FIPS/CC compliant entropy seeds.
After setting a particular bit to 1, the FIPS/CC compliance flag of the corresponding instance will be forced to true upon the next Instantiate or Reseed command.

Note that for this to work, [`CTRL.FIPS_FORCE_ENABLE`](#ctrl) needs to be set to kMultiBitBool4True.

## GEN_ABORT_REGWEN
Register write enable for [`GEN_ABORT`](#gen_abort)
- Offset: `0x60`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "GEN_ABORT_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                                                                              |
|:------:|:------:|:-------:|:-----------------|:-------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                  | Reserved                                                                                                                 |
|   0    |  rw0c  |   0x1   | GEN_ABORT_REGWEN | When true, the [`GEN_ABORT`](#gen_abort) register can be written. When false, it becomes read-only until the next reset. |

## GEN_ABORT
Generate command abort request register
- Reset default: `0x9`
- Reset mask: `0xf`
- Register enable: [`GEN_ABORT_REGWEN`](#gen_abort_regwen)

### Instances

| Name        | Offset   |
|:------------|:---------|
| GEN_ABORT_0 | 0x64     |
| GEN_ABORT_1 | 0x68     |
| GEN_ABORT_2 | 0x6c     |


### Fields

```wavejson
{"reg": [{"name": "GEN_ABORT", "bits": 4, "attr": ["rw1s"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name                               |
|:------:|:------:|:-------:|:-----------------------------------|
|  31:4  |        |         | Reserved                           |
|  3:0   |  rw1s  |   0x9   | [GEN_ABORT](#gen_abort--gen_abort) |

### GEN_ABORT . GEN_ABORT
Setting this field to kMultiBitBool4True requests aborting a Generate command that is currently in progress for this instance.
The instance is zeroed as a result.
It must be instantiated again before further Reseed, Update, or Generate commands can succeed.

This request is only accepted while a Generate command is actually in progress for this instance.
If no Generate command is in progress, the write is ignored and [`RECOV_ALERT_STS.GEN_ABORT_INVALID_ALERT`](#recov_alert_sts) is set instead.

## GEN_ABORT_STATUS
Generate command abort completion status register
- Reset default: `0x0`
- Reset mask: `0x1`

### Instances

| Name               | Offset   |
|:-------------------|:---------|
| GEN_ABORT_STATUS_0 | 0x70     |
| GEN_ABORT_STATUS_1 | 0x74     |
| GEN_ABORT_STATUS_2 | 0x78     |


### Fields

```wavejson
{"reg": [{"name": "GEN_ABORT_STATUS", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                                                                                              |
|:------:|:------:|:-------:|:-----------------|:-----------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                  | Reserved                                                                                                                                 |
|   0    |  rw1c  |   0x0   | GEN_ABORT_STATUS | This bit is set when a Generate command abort requested via [`GEN_ABORT`](#gen_abort) for this instance has completed. Write 1 to clear. |

## HW_EXC_STS
Hardware instance exception status register
- Offset: `0x7c`
- Reset default: `0x0`
- Reset mask: `0xffff`

### Fields

```wavejson
{"reg": [{"name": "HW_EXC_STS", "bits": 16, "attr": ["rw0c"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                  |
|:------:|:------:|:-------:|:--------------------------------------|
| 31:16  |        |         | Reserved                              |
|  15:0  |  rw0c  |   0x0   | [HW_EXC_STS](#hw_exc_sts--hw_exc_sts) |

### HW_EXC_STS . HW_EXC_STS
Reading this register indicates whether one of the CSRNG HW instances has
encountered an exception.  Each bit corresponds to a particular hardware
instance, with bit 0 corresponding to instance HW0, bit 1 corresponding
to instance HW1, and so forth. (To monitor the status of requests made
to the SW instance, check the [`SW_CMD_STS`](#sw_cmd_sts) register). Writing a zero to this register
resets the status bits.

## RECOV_ALERT_STS
Recoverable alert status register
- Offset: `0x80`
- Reset default: `0x0`
- Reset mask: `0xf1ff`

### Fields

```wavejson
{"reg": [{"name": "ENABLE_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "SW_APP_ENABLE_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "INT_STATE_ENABLE_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "FIPS_FORCE_ENABLE_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "ACMD_FLAG0_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "GEN_ABORT_INVALID_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "GEN_ABORT_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "INT_STATE_CMD_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "INT_STATE_CMD_INVALID_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 3}, {"name": "CS_BUS_CMP_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "CMD_STAGE_INVALID_ACMD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "CMD_STAGE_INVALID_CMD_SEQ_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "CMD_STAGE_RESEED_CNT_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 330}}
```

|  Bits  |  Type  |  Reset  | Name                                                                                 |
|:------:|:------:|:-------:|:-------------------------------------------------------------------------------------|
| 31:16  |        |         | Reserved                                                                             |
|   15   |  rw0c  |   0x0   | [CMD_STAGE_RESEED_CNT_ALERT](#recov_alert_sts--cmd_stage_reseed_cnt_alert)           |
|   14   |  rw0c  |   0x0   | [CMD_STAGE_INVALID_CMD_SEQ_ALERT](#recov_alert_sts--cmd_stage_invalid_cmd_seq_alert) |
|   13   |  rw0c  |   0x0   | [CMD_STAGE_INVALID_ACMD_ALERT](#recov_alert_sts--cmd_stage_invalid_acmd_alert)       |
|   12   |  rw0c  |   0x0   | [CS_BUS_CMP_ALERT](#recov_alert_sts--cs_bus_cmp_alert)                               |
|  11:9  |        |         | Reserved                                                                             |
|   8    |  rw0c  |   0x0   | [INT_STATE_CMD_INVALID_ALERT](#recov_alert_sts--int_state_cmd_invalid_alert)         |
|   7    |  rw0c  |   0x0   | [INT_STATE_CMD_FIELD_ALERT](#recov_alert_sts--int_state_cmd_field_alert)             |
|   6    |  rw0c  |   0x0   | [GEN_ABORT_FIELD_ALERT](#recov_alert_sts--gen_abort_field_alert)                     |
|   5    |  rw0c  |   0x0   | [GEN_ABORT_INVALID_ALERT](#recov_alert_sts--gen_abort_invalid_alert)                 |
|   4    |  rw0c  |   0x0   | [ACMD_FLAG0_FIELD_ALERT](#recov_alert_sts--acmd_flag0_field_alert)                   |
|   3    |  rw0c  |   0x0   | [FIPS_FORCE_ENABLE_FIELD_ALERT](#recov_alert_sts--fips_force_enable_field_alert)     |
|   2    |  rw0c  |   0x0   | [INT_STATE_ENABLE_FIELD_ALERT](#recov_alert_sts--int_state_enable_field_alert)       |
|   1    |  rw0c  |   0x0   | [SW_APP_ENABLE_FIELD_ALERT](#recov_alert_sts--sw_app_enable_field_alert)             |
|   0    |  rw0c  |   0x0   | [ENABLE_FIELD_ALERT](#recov_alert_sts--enable_field_alert)                           |

### RECOV_ALERT_STS . CMD_STAGE_RESEED_CNT_ALERT
This bit is set when the maximum number of generate requests between reseeds is
exceeded.
The invalid generate command is ignored and CSRNG continues to operate.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . CMD_STAGE_INVALID_CMD_SEQ_ALERT
This bit is set when an out of order command is received by the main state machine.
This happens when an instantiate command is sent for a state that was already
instantiated or when any command other than instantiate is sent for a state that
wasn't instantiated yet.
The invalid command is ignored and CSRNG continues to operate.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . CMD_STAGE_INVALID_ACMD_ALERT
This bit is set when an unsupported/illegal CSRNG command is received by the
main state machine.
The invalid command is ignored and CSRNG continues to operate.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . CS_BUS_CMP_ALERT
This bit is set when the software application port genbits bus value is equal
to the prior valid value on the bus, indicating a possible attack.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . INT_STATE_CMD_INVALID_ALERT
This bit is set on a misuse of the internal-state EXPORT/IMPORT/RESUME command
interface. This is the case for any of the following:
  - More than one of EXPORT/IMPORT/RESUME is set to kMultiBitBool4True in the same write.
  - EXPORT or IMPORT is issued while [`CTRL.INT_STATE_ENABLE`](#ctrl) (and the OTP gate) is not enabled.
  - IMPORT/EXPORT is issued while an IMPORT/EXPORT is already active for some instance.
  - RESUME is issued for an instance that has not yet reached [`INT_STATE_CMD_STS.STOPPED.`](#int_state_cmd_sts)
  - [`INT_STATE_VAL`](#int_state_val), [`INT_STATE_CMD_GEN_VAL`](#int_state_cmd_gen_val), or [`INT_STATE_CMD_ADATA_VAL`](#int_state_cmd_adata_val) is written
    for an instance that has not yet reached [`INT_STATE_CMD_STS.STOPPED.`](#int_state_cmd_sts)
  - [`INT_STATE_NUM`](#int_state_num) was written to while an instance was stopped.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . INT_STATE_CMD_FIELD_ALERT
This bit is set when a field of the [`INT_STATE_CMD`](#int_state_cmd) register is set to a value other than
kMultiBitBool4True or kMultiBitBool4False.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . GEN_ABORT_FIELD_ALERT
This bit is set when a field of the [`GEN_ABORT`](#gen_abort) register is set to a value other than kMultiBitBool4True or kMultiBitBool4False.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . GEN_ABORT_INVALID_ALERT
This bit is set when a field of the [`GEN_ABORT`](#gen_abort) register is set to kMultiBitBool4True for an instance that does not currently have a Generate command in progress.
The write is ignored and CSRNG continues to operate.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . ACMD_FLAG0_FIELD_ALERT
This bit is set when the FLAG0 field in the Application Command is set to
a value other than kMultiBitBool4True or kMultiBitBool4False.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . FIPS_FORCE_ENABLE_FIELD_ALERT
This bit is set when the FIPS_FORCE_ENABLE field in the [`CTRL`](#ctrl) register is set to a value other than kMultiBitBool4True or kMultiBitBool4False.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . INT_STATE_ENABLE_FIELD_ALERT
This bit is set when the INT_STATE_ENABLE field in the [`CTRL`](#ctrl) register is set to
a value other than kMultiBitBool4True or kMultiBitBool4False.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . SW_APP_ENABLE_FIELD_ALERT
This bit is set when the SW_APP_ENABLE field in the [`CTRL`](#ctrl) register is set to
a value other than kMultiBitBool4True or kMultiBitBool4False.
Writing a zero resets this status bit.

### RECOV_ALERT_STS . ENABLE_FIELD_ALERT
This bit is set when the ENABLE field in the [`CTRL`](#ctrl) register is set to
a value other than kMultiBitBool4True or kMultiBitBool4False.
Writing a zero resets this status bit.

## ERR_CODE
Hardware detection of error conditions status register
- Offset: `0x84`
- Reset default: `0x0`
- Reset mask: `0x76700003`

### Fields

```wavejson
{"reg": [{"name": "SFIFO_CMD_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SFIFO_GENBITS_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 18}, {"name": "CMD_STAGE_SM_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "MAIN_SM_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CTR_DRBG_SM_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 2}, {"name": "AES_CIPHER_SM_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CTR_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 1}, {"name": "FIFO_WRITE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FIFO_READ_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FIFO_STATE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 1}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name                                              |
|:------:|:------:|:-------:|:--------------------------------------------------|
|   31   |        |         | Reserved                                          |
|   30   |   ro   |   0x0   | [FIFO_STATE_ERR](#err_code--fifo_state_err)       |
|   29   |   ro   |   0x0   | [FIFO_READ_ERR](#err_code--fifo_read_err)         |
|   28   |   ro   |   0x0   | [FIFO_WRITE_ERR](#err_code--fifo_write_err)       |
|   27   |        |         | Reserved                                          |
|   26   |   ro   |   0x0   | [CTR_ERR](#err_code--ctr_err)                     |
|   25   |   ro   |   0x0   | [AES_CIPHER_SM_ERR](#err_code--aes_cipher_sm_err) |
| 24:23  |        |         | Reserved                                          |
|   22   |   ro   |   0x0   | [CTR_DRBG_SM_ERR](#err_code--ctr_drbg_sm_err)     |
|   21   |   ro   |   0x0   | [MAIN_SM_ERR](#err_code--main_sm_err)             |
|   20   |   ro   |   0x0   | [CMD_STAGE_SM_ERR](#err_code--cmd_stage_sm_err)   |
|  19:2  |        |         | Reserved                                          |
|   1    |   ro   |   0x0   | [SFIFO_GENBITS_ERR](#err_code--sfifo_genbits_err) |
|   0    |   ro   |   0x0   | [SFIFO_CMD_ERR](#err_code--sfifo_cmd_err)         |

### ERR_CODE . FIFO_STATE_ERR
This bit will be set to one when any of the source bits (bits 0 through 15 of this
this register) are asserted as a result of an error pulse generated from
any FIFO where both the empty and full status bits are set.
This bit will stay set until the next reset.

### ERR_CODE . FIFO_READ_ERR
This bit will be set to one when any of the source bits (bits 0 through 15 of this
this register) are asserted as a result of an error pulse generated from
any empty FIFO that has received a read pulse.
This bit will stay set until the next reset.

### ERR_CODE . FIFO_WRITE_ERR
This bit will be set to one when any of the source bits (bits 0 through 15 of this
this register) are asserted as a result of an error pulse generated from
any full FIFO that has been received a write pulse.
This bit will stay set until the next reset.

### ERR_CODE . CTR_ERR
This bit will be set to one when a mismatch in any of the hardened counters
has been detected.
This error will signal a fatal alert, and also an interrupt if enabled.
This bit will stay set until the next reset.

### ERR_CODE . AES_CIPHER_SM_ERR
This bit will be set to one when an AES fatal error has been detected.
This error will signal a fatal alert, and also an interrupt if enabled.
This bit will stay set until the next reset.

### ERR_CODE . CTR_DRBG_SM_ERR
This bit will be set to one when an illegal state has been detected for the
ctr_drbg state machine. This error will signal a fatal alert, and also
an interrupt if enabled.
This bit will stay set until the next reset.

### ERR_CODE . MAIN_SM_ERR
This bit will be set to one when an illegal state has been detected for the
main state machine. This error will signal a fatal alert, and also
an interrupt if enabled.
This bit will stay set until the next reset.

### ERR_CODE . CMD_STAGE_SM_ERR
This bit will be set to one when an illegal state has been detected for the
command stage state machine. This error will signal a fatal alert, and also
an interrupt if enabled.
This bit will stay set until the next reset.

### ERR_CODE . SFIFO_GENBITS_ERR
This bit will be set to one when an error has been detected for the
command stage genbits FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
This bit will stay set until the next reset.

### ERR_CODE . SFIFO_CMD_ERR
This bit will be set to one when an error has been detected for the
command stage command FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
This bit will stay set until the next reset.

## ERR_CODE_TEST
Test error conditions register
- Offset: `0x88`
- Reset default: `0x0`
- Reset mask: `0x1f`
- Register enable: [`REGWEN`](#regwen)

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
- Offset: `0x8c`
- Reset default: `0x37`
- Reset mask: `0x3f`

### Fields

```wavejson
{"reg": [{"name": "MAIN_SM_STATE", "bits": 6, "attr": ["ro"], "rotate": -90}, {"bits": 26}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                                                                        |
|:------:|:------:|:-------:|:--------------|:-------------------------------------------------------------------------------------------------------------------|
|  31:6  |        |         |               | Reserved                                                                                                           |
|  5:0   |   ro   |  0x37   | MAIN_SM_STATE | This is the state of the CSRNG main state machine. See the RTL file `csrng_main_sm` for the meaning of the values. |


<!-- END CMDGEN -->
