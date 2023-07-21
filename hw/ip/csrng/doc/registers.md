# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/csrng/data/csrng.hjson -->
## Summary

| Name                                                      | Offset   |   Length | Description                                            |
|:----------------------------------------------------------|:---------|---------:|:-------------------------------------------------------|
| csrng.[`CIP_ID`](#cip_id)                                 | 0x0      |        4 | Comportable IP ID.                                     |
| csrng.[`REVISION`](#revision)                             | 0x4      |        4 | Comportable IP semantic version.                       |
| csrng.[`PARAMETER_BLOCK_TYPE`](#parameter_block_type)     | 0x8      |        4 | Parameter block type.                                  |
| csrng.[`PARAMETER_BLOCK_LENGTH`](#parameter_block_length) | 0xc      |        4 | Parameter block length.                                |
| csrng.[`NEXT_PARAMETER_BLOCK`](#next_parameter_block)     | 0x10     |        4 | Next parameter block offset.                           |
| csrng.[`INTR_STATE`](#intr_state)                         | 0x40     |        4 | Interrupt State Register                               |
| csrng.[`INTR_ENABLE`](#intr_enable)                       | 0x44     |        4 | Interrupt Enable Register                              |
| csrng.[`INTR_TEST`](#intr_test)                           | 0x48     |        4 | Interrupt Test Register                                |
| csrng.[`ALERT_TEST`](#alert_test)                         | 0x4c     |        4 | Alert Test Register                                    |
| csrng.[`REGWEN`](#regwen)                                 | 0x50     |        4 | Register write enable for all control registers        |
| csrng.[`CTRL`](#ctrl)                                     | 0x54     |        4 | Control register                                       |
| csrng.[`CMD_REQ`](#cmd_req)                               | 0x58     |        4 | Command request register                               |
| csrng.[`SW_CMD_STS`](#sw_cmd_sts)                         | 0x5c     |        4 | Application interface command status register          |
| csrng.[`GENBITS_VLD`](#genbits_vld)                       | 0x60     |        4 | Generate bits returned valid register                  |
| csrng.[`GENBITS`](#genbits)                               | 0x64     |        4 | Generate bits returned register                        |
| csrng.[`INT_STATE_NUM`](#int_state_num)                   | 0x68     |        4 | Internal state number register                         |
| csrng.[`INT_STATE_VAL`](#int_state_val)                   | 0x6c     |        4 | Internal state read access register                    |
| csrng.[`HW_EXC_STS`](#hw_exc_sts)                         | 0x70     |        4 | Hardware instance exception status register            |
| csrng.[`RECOV_ALERT_STS`](#recov_alert_sts)               | 0x74     |        4 | Recoverable alert status register                      |
| csrng.[`ERR_CODE`](#err_code)                             | 0x78     |        4 | Hardware detection of error conditions status register |
| csrng.[`ERR_CODE_TEST`](#err_code_test)                   | 0x7c     |        4 | Test error conditions register                         |
| csrng.[`MAIN_SM_STATE`](#main_sm_state)                   | 0x80     |        4 | Main state machine state debug register                |

## CIP_ID
Comportable IP ID.
- Offset: `0x0`
- Reset default: `0x5`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "CIP_ID", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                       |
|:------:|:------:|:-------:|:-------|:--------------------------------------------------|
|  31:0  |   ro   |   0x5   | CIP_ID | This value is a unique comportable IP identifier. |

## REVISION
Comportable IP semantic version.
- Offset: `0x4`
- Reset default: `0x2000000`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "RESERVED", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "SUBMINOR", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "MINOR", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "MAJOR", "bits": 8, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                      |
|:------:|:------:|:-------:|:---------|:---------------------------------|
| 31:24  |   ro   |   0x2   | MAJOR    | Major version number.            |
| 23:16  |   ro   |   0x0   | MINOR    | Minor version number.            |
|  15:8  |   ro   |   0x0   | SUBMINOR | Subminor (patch) version number. |
|  7:0   |   ro   |   0x0   | RESERVED | Reserved version number.         |

## PARAMETER_BLOCK_TYPE
Parameter block type.
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "BLOCK_TYPE", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description           |
|:------:|:------:|:-------:|:-----------|:----------------------|
|  31:0  |   ro   |   0x0   | BLOCK_TYPE | Parameter block type. |

## PARAMETER_BLOCK_LENGTH
Parameter block length.
- Offset: `0xc`
- Reset default: `0xc`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "BLOCK_LENGTH", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                      |
|:------:|:------:|:-------:|:-------------|:---------------------------------|
|  31:0  |   ro   |   0xc   | BLOCK_LENGTH | Parameter block length in bytes. |

## NEXT_PARAMETER_BLOCK
Next parameter block offset.
- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "BLOCK_OFFSET", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                                                             |
|:------:|:------:|:-------:|:-------------|:----------------------------------------------------------------------------------------|
|  31:0  |   ro   |   0x0   | BLOCK_OFFSET | This offset value is zero if there is no other                         parameter block. |

## INTR_STATE
Interrupt State Register
- Offset: `0x40`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "cs_cmd_req_done", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "cs_entropy_req", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "cs_hw_inst_exc", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "cs_fatal_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name            | Description                                                                                                             |
|:------:|:------:|:-------:|:----------------|:------------------------------------------------------------------------------------------------------------------------|
|  31:4  |        |         |                 | Reserved                                                                                                                |
|   3    |  rw1c  |   0x0   | cs_fatal_err    | Asserted when a FIFO error or a fatal alert occurs. Check the [`ERR_CODE`](#err_code) register to get more information. |
|   2    |  rw1c  |   0x0   | cs_hw_inst_exc  | Asserted when a hardware-attached CSRNG instance encounters a command exception                                         |
|   1    |  rw1c  |   0x0   | cs_entropy_req  | Asserted when a request for entropy has been made.                                                                      |
|   0    |  rw1c  |   0x0   | cs_cmd_req_done | Asserted when a command request is completed.                                                                           |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x44`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "cs_cmd_req_done", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "cs_entropy_req", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "cs_hw_inst_exc", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "cs_fatal_err", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name            | Description                                                               |
|:------:|:------:|:-------:|:----------------|:--------------------------------------------------------------------------|
|  31:4  |        |         |                 | Reserved                                                                  |
|   3    |   rw   |   0x0   | cs_fatal_err    | Enable interrupt when [`INTR_STATE.cs_fatal_err`](#intr_state) is set.    |
|   2    |   rw   |   0x0   | cs_hw_inst_exc  | Enable interrupt when [`INTR_STATE.cs_hw_inst_exc`](#intr_state) is set.  |
|   1    |   rw   |   0x0   | cs_entropy_req  | Enable interrupt when [`INTR_STATE.cs_entropy_req`](#intr_state) is set.  |
|   0    |   rw   |   0x0   | cs_cmd_req_done | Enable interrupt when [`INTR_STATE.cs_cmd_req_done`](#intr_state) is set. |

## INTR_TEST
Interrupt Test Register
- Offset: `0x48`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "cs_cmd_req_done", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "cs_entropy_req", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "cs_hw_inst_exc", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "cs_fatal_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name            | Description                                                        |
|:------:|:------:|:-------:|:----------------|:-------------------------------------------------------------------|
|  31:4  |        |         |                 | Reserved                                                           |
|   3    |   wo   |   0x0   | cs_fatal_err    | Write 1 to force [`INTR_STATE.cs_fatal_err`](#intr_state) to 1.    |
|   2    |   wo   |   0x0   | cs_hw_inst_exc  | Write 1 to force [`INTR_STATE.cs_hw_inst_exc`](#intr_state) to 1.  |
|   1    |   wo   |   0x0   | cs_entropy_req  | Write 1 to force [`INTR_STATE.cs_entropy_req`](#intr_state) to 1.  |
|   0    |   wo   |   0x0   | cs_cmd_req_done | Write 1 to force [`INTR_STATE.cs_cmd_req_done`](#intr_state) to 1. |

## ALERT_TEST
Alert Test Register
- Offset: `0x4c`
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
- Offset: `0x50`
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
- Offset: `0x54`
- Reset default: `0x999`
- Reset mask: `0xfff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "ENABLE", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "SW_APP_ENABLE", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "READ_INT_STATE", "bits": 4, "attr": ["rw"], "rotate": -90}, {"bits": 20}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                                                                                                                                                                                                                                                           |
|:------:|:------:|:-------:|:---------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:12  |        |         |                | Reserved                                                                                                                                                                                                                                                              |
|  11:8  |   rw   |   0x9   | READ_INT_STATE | Setting this field to kMultiBitBool4True will enable reading from the [`INT_STATE_VAL`](#int_state_val) register. Reading the internal state of the enable instances will be enabled only if the otp_en_csrng_sw_app_read input vector is set to the enable encoding. |
|  7:4   |   rw   |   0x9   | SW_APP_ENABLE  | Setting this field to kMultiBitBool4True will enable reading from the [`GENBITS`](#genbits) register. This application interface for software (register based) will be enabled only if the otp_en_csrng_sw_app_read input vector is set to the enable encoding.       |
|  3:0   |   rw   |   0x9   | ENABLE         | Setting this field to kMultiBitBool4True will enable the CSRNG module. The modules of the entropy complex may only be enabled and disabled in a specific order, see Programmers Guide for details.                                                                    |

## CMD_REQ
Command request register
- Offset: `0x58`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "CMD_REQ", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name    | Description                                                                                                                                                                         |
|:------:|:------:|:-------:|:--------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   wo   |   0x0   | CMD_REQ | Writing this request with defined CSRNG commands will initiate all possible CSRNG actions. The application interface must wait for the "ack" to return before issuing new commands. |

## SW_CMD_STS
Application interface command status register
- Offset: `0x5c`
- Reset default: `0x1`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "CMD_RDY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CMD_STS", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 90}}
```

|  Bits  |  Type  |  Reset  | Name                            |
|:------:|:------:|:-------:|:--------------------------------|
|  31:2  |        |         | Reserved                        |
|   1    |   ro   |   0x0   | [CMD_STS](#sw_cmd_sts--cmd_sts) |
|   0    |   ro   |   0x1   | [CMD_RDY](#sw_cmd_sts--cmd_rdy) |

### SW_CMD_STS . CMD_STS
This one bit field is the status code returned with the application command ack.
It is updated each time a command ack is asserted on the internal application
interface for software use.
0b0: Request completed successfully
0b1: Request completed with an error

### SW_CMD_STS . CMD_RDY
This bit indicates when the command interface is ready to accept commands.

## GENBITS_VLD
Generate bits returned valid register
- Offset: `0x60`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "GENBITS_VLD", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "GENBITS_FIPS", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                                               |
|:------:|:------:|:-------:|:-------------|:--------------------------------------------------------------------------|
|  31:2  |        |         |              | Reserved                                                                  |
|   1    |   ro   |    x    | GENBITS_FIPS | This bit is set when genbits are FIPS/CC compliant.                       |
|   0    |   ro   |    x    | GENBITS_VLD  | This bit is set when genbits are available on this application interface. |

## GENBITS
Generate bits returned register
- Offset: `0x64`
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
the generate request. This register must be four times for each request
number made. For example, a application command generate request with
a `creq` value of 4 requires this register to be read 16 times to get all
of the data out of the FIFO path.

## INT_STATE_NUM
Internal state number register
- Offset: `0x68`
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
Setting this field will set the number for which internal state can be
selected for a read access. Up to 16 internal state values can be chosen
from this register. The actual number of valid internal state fields
is set by parameter NHwApps plus 1 software app. For those selections that point
to reserved locations (greater than NHwApps plus 1), the returned value
will be zero. Writing this register will also reset the internal read
pointer for the [`INT_STATE_VAL`](#int_state_val) register.
Note: This register should be read back after being written to ensure
that the [`INT_STATE_VAL`](#int_state_val) read back is accurate.

## INT_STATE_VAL
Internal state read access register
- Offset: `0x6c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "INT_STATE_VAL", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                           |
|:------:|:------:|:-------:|:-----------------------------------------------|
|  31:0  |   ro   |    x    | [INT_STATE_VAL](#int_state_val--int_state_val) |

### INT_STATE_VAL . INT_STATE_VAL
Reading this register will dump out the contents of the selected internal state field.
Since the internal state field is 448 bits wide, it will require 14 reads from this
register to gather the entire field. Once 14 reads have been done, the internal read
pointer (selects 32 bits of the 448 bit field) will reset to zero. The [`INT_STATE_NUM`](#int_state_num)
can be re-written at this time (internal read pointer is also reset), and then
another internal state field can be read.

## HW_EXC_STS
Hardware instance exception status register
- Offset: `0x70`
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
- Offset: `0x74`
- Reset default: `0x0`
- Reset mask: `0x300f`

### Fields

```wavejson
{"reg": [{"name": "ENABLE_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "SW_APP_ENABLE_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "READ_INT_STATE_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "ACMD_FLAG0_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 8}, {"name": "CS_BUS_CMP_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "CS_MAIN_SM_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 18}], "config": {"lanes": 1, "fontsize": 10, "vspace": 280}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                                                                                                                                                  |
|:------:|:------:|:-------:|:---------------------------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:14  |        |         |                            | Reserved                                                                                                                                                                                     |
|   13   |  rw0c  |   0x0   | CS_MAIN_SM_ALERT           | This bit is set when an unsupported/illegal CSRNG command is being processed. The main FSM will hang unless the module enable field is set to the disabled state.                            |
|   12   |  rw0c  |   0x0   | CS_BUS_CMP_ALERT           | This bit is set when the software application port genbits bus value is equal to the prior valid value on the bus, indicating a possible attack. Writing a zero resets this status bit.      |
|  11:4  |        |         |                            | Reserved                                                                                                                                                                                     |
|   3    |  rw0c  |   0x0   | ACMD_FLAG0_FIELD_ALERT     | This bit is set when the FLAG0 field in the Application Command is set to a value other than kMultiBitBool4True or kMultiBitBool4False. Writing a zero resets this status bit.               |
|   2    |  rw0c  |   0x0   | READ_INT_STATE_FIELD_ALERT | This bit is set when the READ_INT_STATE field in the [`CTRL`](#ctrl) register is set to a value other than kMultiBitBool4True or kMultiBitBool4False. Writing a zero resets this status bit. |
|   1    |  rw0c  |   0x0   | SW_APP_ENABLE_FIELD_ALERT  | This bit is set when the SW_APP_ENABLE field in the [`CTRL`](#ctrl) register is set to a value other than kMultiBitBool4True or kMultiBitBool4False. Writing a zero resets this status bit.  |
|   0    |  rw0c  |   0x0   | ENABLE_FIELD_ALERT         | This bit is set when the ENABLE field in the [`CTRL`](#ctrl) register is set to a value other than kMultiBitBool4True or kMultiBitBool4False. Writing a zero resets this status bit.         |

## ERR_CODE
Hardware detection of error conditions status register
- Offset: `0x78`
- Reset default: `0x0`
- Reset mask: `0x77f0ffff`

### Fields

```wavejson
{"reg": [{"name": "SFIFO_CMD_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SFIFO_GENBITS_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SFIFO_CMDREQ_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SFIFO_RCSTAGE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SFIFO_KEYVRC_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SFIFO_UPDREQ_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SFIFO_BENCREQ_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SFIFO_BENCACK_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SFIFO_PDATA_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SFIFO_FINAL_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SFIFO_GBENCACK_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SFIFO_GRCSTAGE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SFIFO_GGENREQ_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SFIFO_GADSTAGE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SFIFO_GGENBITS_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SFIFO_BLKENC_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 4}, {"name": "CMD_STAGE_SM_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "MAIN_SM_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "DRBG_GEN_SM_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "DRBG_UPDBE_SM_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "DRBG_UPDOB_SM_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "AES_CIPHER_SM_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CMD_GEN_CNT_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 1}, {"name": "FIFO_WRITE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FIFO_READ_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FIFO_STATE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 1}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name                                                |
|:------:|:------:|:-------:|:----------------------------------------------------|
|   31   |        |         | Reserved                                            |
|   30   |   ro   |   0x0   | [FIFO_STATE_ERR](#err_code--fifo_state_err)         |
|   29   |   ro   |   0x0   | [FIFO_READ_ERR](#err_code--fifo_read_err)           |
|   28   |   ro   |   0x0   | [FIFO_WRITE_ERR](#err_code--fifo_write_err)         |
|   27   |        |         | Reserved                                            |
|   26   |   ro   |   0x0   | [CMD_GEN_CNT_ERR](#err_code--cmd_gen_cnt_err)       |
|   25   |   ro   |   0x0   | [AES_CIPHER_SM_ERR](#err_code--aes_cipher_sm_err)   |
|   24   |   ro   |   0x0   | [DRBG_UPDOB_SM_ERR](#err_code--drbg_updob_sm_err)   |
|   23   |   ro   |   0x0   | [DRBG_UPDBE_SM_ERR](#err_code--drbg_updbe_sm_err)   |
|   22   |   ro   |   0x0   | [DRBG_GEN_SM_ERR](#err_code--drbg_gen_sm_err)       |
|   21   |   ro   |   0x0   | [MAIN_SM_ERR](#err_code--main_sm_err)               |
|   20   |   ro   |   0x0   | [CMD_STAGE_SM_ERR](#err_code--cmd_stage_sm_err)     |
| 19:16  |        |         | Reserved                                            |
|   15   |   ro   |   0x0   | [SFIFO_BLKENC_ERR](#err_code--sfifo_blkenc_err)     |
|   14   |   ro   |   0x0   | [SFIFO_GGENBITS_ERR](#err_code--sfifo_ggenbits_err) |
|   13   |   ro   |   0x0   | [SFIFO_GADSTAGE_ERR](#err_code--sfifo_gadstage_err) |
|   12   |   ro   |   0x0   | [SFIFO_GGENREQ_ERR](#err_code--sfifo_ggenreq_err)   |
|   11   |   ro   |   0x0   | [SFIFO_GRCSTAGE_ERR](#err_code--sfifo_grcstage_err) |
|   10   |   ro   |   0x0   | [SFIFO_GBENCACK_ERR](#err_code--sfifo_gbencack_err) |
|   9    |   ro   |   0x0   | [SFIFO_FINAL_ERR](#err_code--sfifo_final_err)       |
|   8    |   ro   |   0x0   | [SFIFO_PDATA_ERR](#err_code--sfifo_pdata_err)       |
|   7    |   ro   |   0x0   | [SFIFO_BENCACK_ERR](#err_code--sfifo_bencack_err)   |
|   6    |   ro   |   0x0   | [SFIFO_BENCREQ_ERR](#err_code--sfifo_bencreq_err)   |
|   5    |   ro   |   0x0   | [SFIFO_UPDREQ_ERR](#err_code--sfifo_updreq_err)     |
|   4    |   ro   |   0x0   | [SFIFO_KEYVRC_ERR](#err_code--sfifo_keyvrc_err)     |
|   3    |   ro   |   0x0   | [SFIFO_RCSTAGE_ERR](#err_code--sfifo_rcstage_err)   |
|   2    |   ro   |   0x0   | [SFIFO_CMDREQ_ERR](#err_code--sfifo_cmdreq_err)     |
|   1    |   ro   |   0x0   | [SFIFO_GENBITS_ERR](#err_code--sfifo_genbits_err)   |
|   0    |   ro   |   0x0   | [SFIFO_CMD_ERR](#err_code--sfifo_cmd_err)           |

### ERR_CODE . FIFO_STATE_ERR
This bit will be set to one when any of the source bits (bits 0 through 15 of this
this register) are asserted as a result of an error pulse generated from
any FIFO where both the empty and full status bits are set.
This bit will stay set until the next reset.

### ERR_CODE . FIFO_READ_ERR
This bit will be set to one when any of the source bits (bits 0 through 15 of this
this register) are asserted as a result of an error pulse generated from
any empty FIFO that has recieved a read pulse.
This bit will stay set until the next reset.

### ERR_CODE . FIFO_WRITE_ERR
This bit will be set to one when any of the source bits (bits 0 through 15 of this
this register) are asserted as a result of an error pulse generated from
any full FIFO that has been recieved a write pulse.
This bit will stay set until the next reset.

### ERR_CODE . CMD_GEN_CNT_ERR
This bit will be set to one when a mismatch in any of the hardened counters
has been detected.
This error will signal a fatal alert, and also
an interrupt if enabled.
This bit will stay set until the next reset.

### ERR_CODE . AES_CIPHER_SM_ERR
This bit will be set to one when an AES fatal error has been detected.
This error will signal a fatal alert, and also
an interrupt if enabled.
This bit will stay set until the next reset.

### ERR_CODE . DRBG_UPDOB_SM_ERR
This bit will be set to one when an illegal state has been detected for the
ctr_drbg update out block state machine. This error will signal a fatal alert, and also
an interrupt if enabled.
This bit will stay set until the next reset.

### ERR_CODE . DRBG_UPDBE_SM_ERR
This bit will be set to one when an illegal state has been detected for the
ctr_drbg update block encode state machine. This error will signal a fatal alert, and also
an interrupt if enabled.
This bit will stay set until the next reset.

### ERR_CODE . DRBG_GEN_SM_ERR
This bit will be set to one when an illegal state has been detected for the
ctr_drbg gen state machine. This error will signal a fatal alert, and also
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

### ERR_CODE . SFIFO_BLKENC_ERR
This bit will be set to one when an error has been detected for the
blkenc FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
This bit will stay set until the next reset.

### ERR_CODE . SFIFO_GGENBITS_ERR
This bit will be set to one when an error has been detected for the
ggenbits FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
This bit will stay set until the next reset.

### ERR_CODE . SFIFO_GADSTAGE_ERR
This bit will be set to one when an error has been detected for the
gadstage FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
This bit will stay set until the next reset.

### ERR_CODE . SFIFO_GGENREQ_ERR
This bit will be set to one when an error has been detected for the
ggenreq FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
This bit will stay set until the next reset.

### ERR_CODE . SFIFO_GRCSTAGE_ERR
This bit will be set to one when an error has been detected for the
grcstage FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
This bit will stay set until the next reset.

### ERR_CODE . SFIFO_GBENCACK_ERR
This bit will be set to one when an error has been detected for the
gbencack FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
This bit will stay set until the next reset.

### ERR_CODE . SFIFO_FINAL_ERR
This bit will be set to one when an error has been detected for the
final FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
This bit will stay set until the next reset.

### ERR_CODE . SFIFO_PDATA_ERR
This bit will be set to one when an error has been detected for the
pdata FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
This bit will stay set until the next reset.

### ERR_CODE . SFIFO_BENCACK_ERR
This bit will be set to one when an error has been detected for the
bencack FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
This bit will stay set until the next reset.

### ERR_CODE . SFIFO_BENCREQ_ERR
This bit will be set to one when an error has been detected for the
bencreq FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
This bit will stay set until the next reset.

### ERR_CODE . SFIFO_UPDREQ_ERR
This bit will be set to one when an error has been detected for the
updreq FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
This bit will stay set until the next reset.

### ERR_CODE . SFIFO_KEYVRC_ERR
This bit will be set to one when an error has been detected for the
keyvrc FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
This bit will stay set until the next reset.

### ERR_CODE . SFIFO_RCSTAGE_ERR
This bit will be set to one when an error has been detected for the
rcstage FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
This bit will stay set until the next reset.

### ERR_CODE . SFIFO_CMDREQ_ERR
This bit will be set to one when an error has been detected for the
cmdreq FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
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
- Offset: `0x7c`
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
- Offset: `0x80`
- Reset default: `0x4e`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "MAIN_SM_STATE", "bits": 8, "attr": ["ro"], "rotate": 0}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                                                                        |
|:------:|:------:|:-------:|:--------------|:-------------------------------------------------------------------------------------------------------------------|
|  31:8  |        |         |               | Reserved                                                                                                           |
|  7:0   |   ro   |  0x4e   | MAIN_SM_STATE | This is the state of the CSRNG main state machine. See the RTL file `csrng_main_sm` for the meaning of the values. |


<!-- END CMDGEN -->
