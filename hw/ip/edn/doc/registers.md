# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/edn/data/edn.hjson -->
## Summary

| Name                                                                | Offset   |   Length | Description                                                  |
|:--------------------------------------------------------------------|:---------|---------:|:-------------------------------------------------------------|
| edn.[`INTR_STATE`](#intr_state)                                     | 0x0      |        4 | Interrupt State Register                                     |
| edn.[`INTR_ENABLE`](#intr_enable)                                   | 0x4      |        4 | Interrupt Enable Register                                    |
| edn.[`INTR_TEST`](#intr_test)                                       | 0x8      |        4 | Interrupt Test Register                                      |
| edn.[`ALERT_TEST`](#alert_test)                                     | 0xc      |        4 | Alert Test Register                                          |
| edn.[`REGWEN`](#regwen)                                             | 0x10     |        4 | Register write enable for all control registers              |
| edn.[`CTRL`](#ctrl)                                                 | 0x14     |        4 | EDN control register                                         |
| edn.[`BOOT_INS_CMD`](#boot_ins_cmd)                                 | 0x18     |        4 | EDN boot instantiate command register                        |
| edn.[`BOOT_GEN_CMD`](#boot_gen_cmd)                                 | 0x1c     |        4 | EDN boot generate command register                           |
| edn.[`SW_CMD_REQ`](#sw_cmd_req)                                     | 0x20     |        4 | EDN csrng app command request register                       |
| edn.[`SW_CMD_STS`](#sw_cmd_sts)                                     | 0x24     |        4 | EDN software command status register                         |
| edn.[`HW_CMD_STS`](#hw_cmd_sts)                                     | 0x28     |        4 | EDN hardware command status register                         |
| edn.[`RESEED_CMD`](#reseed_cmd)                                     | 0x2c     |        4 | EDN csrng reseed command register                            |
| edn.[`GENERATE_CMD`](#generate_cmd)                                 | 0x30     |        4 | EDN csrng generate command register                          |
| edn.[`MAX_NUM_REQS_BETWEEN_RESEEDS`](#max_num_reqs_between_reseeds) | 0x34     |        4 | EDN maximum number of requests between reseeds register      |
| edn.[`RECOV_ALERT_STS`](#recov_alert_sts)                           | 0x38     |        4 | Recoverable alert status register                            |
| edn.[`ERR_CODE`](#err_code)                                         | 0x3c     |        4 | Hardware detection of fatal error conditions status register |
| edn.[`ERR_CODE_TEST`](#err_code_test)                               | 0x40     |        4 | Test error conditions register                               |
| edn.[`MAIN_SM_STATE`](#main_sm_state)                               | 0x44     |        4 | Main state machine state observation register                |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "edn_cmd_req_done", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "edn_fatal_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                           |
|:------:|:------:|:-------:|:-----------------|:------------------------------------------------------|
|  31:2  |        |         |                  | Reserved                                              |
|   1    |  rw1c  |   0x0   | edn_fatal_err    | Asserted when a FIFO error occurs.                    |
|   0    |  rw1c  |   0x0   | edn_cmd_req_done | Asserted when a software CSRNG request has completed. |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "edn_cmd_req_done", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "edn_fatal_err", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                                |
|:------:|:------:|:-------:|:-----------------|:---------------------------------------------------------------------------|
|  31:2  |        |         |                  | Reserved                                                                   |
|   1    |   rw   |   0x0   | edn_fatal_err    | Enable interrupt when [`INTR_STATE.edn_fatal_err`](#intr_state) is set.    |
|   0    |   rw   |   0x0   | edn_cmd_req_done | Enable interrupt when [`INTR_STATE.edn_cmd_req_done`](#intr_state) is set. |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "edn_cmd_req_done", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "edn_fatal_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                         |
|:------:|:------:|:-------:|:-----------------|:--------------------------------------------------------------------|
|  31:2  |        |         |                  | Reserved                                                            |
|   1    |   wo   |   0x0   | edn_fatal_err    | Write 1 to force [`INTR_STATE.edn_fatal_err`](#intr_state) to 1.    |
|   0    |   wo   |   0x0   | edn_cmd_req_done | Write 1 to force [`INTR_STATE.edn_cmd_req_done`](#intr_state) to 1. |

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

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                                                                    |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                                                                                                                                                                       |
|   0    |  rw0c  |   0x1   | REGWEN | When true, the CTRL can be written by software. When false, this field read-only. Defaults true, write zero to clear. Note that this needs to be cleared after initial configuration at boot in order to lock in the listed register settings. |

## CTRL
EDN control register
- Offset: `0x14`
- Reset default: `0x9999`
- Reset mask: `0xffff`
- Register enable: [`REGWEN`](#regwen)

### Fields

```wavejson
{"reg": [{"name": "EDN_ENABLE", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "BOOT_REQ_MODE", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "AUTO_REQ_MODE", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "CMD_FIFO_RST", "bits": 4, "attr": ["rw"], "rotate": -90}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name                                  |
|:------:|:------:|:-------:|:--------------------------------------|
| 31:16  |        |         | Reserved                              |
| 15:12  |   rw   |   0x9   | [CMD_FIFO_RST](#ctrl--cmd_fifo_rst)   |
|  11:8  |   rw   |   0x9   | [AUTO_REQ_MODE](#ctrl--auto_req_mode) |
|  7:4   |   rw   |   0x9   | [BOOT_REQ_MODE](#ctrl--boot_req_mode) |
|  3:0   |   rw   |   0x9   | [EDN_ENABLE](#ctrl--edn_enable)       |

### CTRL . CMD_FIFO_RST
Setting this field to kMultiBitBool4True clears the two command FIFOs: the
RESEED_CMD FIFO and the GENERATE_CMD FIFO. This field must be
set to the reset state by software before any further commands can be issued to
these FIFOs.

### CTRL . AUTO_REQ_MODE
Setting this field to kMultiBitBool4True enables auto request mode.
In this mode, EDN automatically sends `generate` and `reseed` command requests to the CSRNG application interface.
The purpose of this mode is to continuously deliver entropy to endpoints without firmware intervention.

For this to work, firmware has to 1) configure the [`GENERATE_CMD`](#generate_cmd), [`RESEED_CMD`](#reseed_cmd), and [`MAX_NUM_REQS_BETWEEN_RESEEDS`](#max_num_reqs_between_reseeds) registers, and 2) to issue the first `instantiate` command via the [`SW_CMD_REQ`](#sw_cmd_req) register.
Once this command has been acknowledged by CSRNG, the first `generate` command is sent out automatically, and a `reseed` command is sent after every MAX_NUM_REQS_BETWEEN_RESEEDS number of `generate` commands.

Note that the BOOT_REQ_MODE field takes precedence over this field: If both fields are set, EDN enters boot-time request mode.
If none of the fields are set, EDN enters Software Port Mode upon enabling.

### CTRL . BOOT_REQ_MODE
Setting this field to kMultiBitBool4True enables the boot-time request mode.
In this mode, EDN automatically sends a boot-time request to the CSRNG application interface.
The purpose of this mode is to request entropy as fast as possible after reset, and during chip boot time.

Note that this takes precedence over the AUTO_REQ_MODE field: If both fields are set, EDN enters boot-time request mode.
If none of the fields are set, EDN enters Software Port Mode upon enabling.

### CTRL . EDN_ENABLE
Setting this field to kMultiBitBool4True enables the EDN module. The modules of the
entropy complex may only be enabled and disabled in a specific order, see
Programmers Guide for details.

## BOOT_INS_CMD
EDN boot instantiate command register
- Offset: `0x18`
- Reset default: `0x901`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "BOOT_INS_CMD", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                        |
|:------:|:------:|:-------:|:--------------------------------------------|
|  31:0  |   rw   |  0x901  | [BOOT_INS_CMD](#boot_ins_cmd--boot_ins_cmd) |

### BOOT_INS_CMD . BOOT_INS_CMD
This field is used as the value for the `instantiate` command at boot time.

See [Command Header](../../csrng/doc/theory_of_operation.md#command-header) for the meaning of the individual bits.
Note that the hardware only supports a value of 0 for the `clen` field.
If `clen` has a different value, EDN will hang.
Fixing this requires disabling and restarting both EDN and CSRNG.

## BOOT_GEN_CMD
EDN boot generate command register
- Offset: `0x1c`
- Reset default: `0xfff003`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "BOOT_GEN_CMD", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset   | Name                                        |
|:------:|:------:|:--------:|:--------------------------------------------|
|  31:0  |   rw   | 0xfff003 | [BOOT_GEN_CMD](#boot_gen_cmd--boot_gen_cmd) |

### BOOT_GEN_CMD . BOOT_GEN_CMD
This field is used as the value for the `generate` command at boot time.

See [Command Header](../../csrng/doc/theory_of_operation.md#command-header) for the meaning of the individual bits.
Note that the hardware only supports a value of 0 for the `clen` field.
If `clen` has a different value, EDN will hang.
Fixing this requires disabling and restarting both EDN and CSRNG.

## SW_CMD_REQ
EDN csrng app command request register
- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "SW_CMD_REQ", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                  |
|:------:|:------:|:-------:|:--------------------------------------|
|  31:0  |   wo   |    x    | [SW_CMD_REQ](#sw_cmd_req--sw_cmd_req) |

### SW_CMD_REQ . SW_CMD_REQ
Any CSRNG action can be initiated by writing a CSRNG command to this register.
Before any write operation to this register, firmware must read [`SW_CMD_STS`](#sw_cmd_sts) to check whether EDN is ready to receive a new command or the next word of a previously started command.

While [`CTRL.AUTO_REQ_MODE`](#ctrl) is set, only the first instantiate command has any effect.
After that command has been processed, writes to this register will have no effect on operation, until [`CTRL.AUTO_REQ_MODE`](#ctrl) is de-asserted and the state machine of EDN enters the `SwPortMode` state.

Refer to the [CSRNG documentation](../../csrng/doc/theory_of_operation.md#general-command-format) for details on the command format.

## SW_CMD_STS
EDN software command status register
- Offset: `0x24`
- Reset default: `0x0`
- Reset mask: `0x3f`

### Fields

```wavejson
{"reg": [{"name": "CMD_REG_RDY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CMD_RDY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CMD_ACK", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CMD_STS", "bits": 3, "attr": ["ro"], "rotate": -90}, {"bits": 26}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name                                    |
|:------:|:------:|:-------:|:----------------------------------------|
|  31:6  |        |         | Reserved                                |
|  5:3   |   ro   |   0x0   | [CMD_STS](#sw_cmd_sts--cmd_sts)         |
|   2    |   ro   |   0x0   | [CMD_ACK](#sw_cmd_sts--cmd_ack)         |
|   1    |   ro   |   0x0   | [CMD_RDY](#sw_cmd_sts--cmd_rdy)         |
|   0    |   ro   |   0x0   | [CMD_REG_RDY](#sw_cmd_sts--cmd_reg_rdy) |

### SW_CMD_STS . CMD_STS
This field represents the status code returned with the CSRNG application command ack.
It is updated each time a SW command is acknowledged by CSRNG.
To check whether a command was successful, wait for [`INTR_STATE.EDN_CMD_REQ_DONE`](#intr_state) or
[`SW_CMD_STS.CMD_ACK`](#sw_cmd_sts) to be high and then check the value of this field.
A description of the command status types can be found [here](../../csrng/doc/registers.md#sw_cmd_sts--cmd_sts).

### SW_CMD_STS . CMD_ACK
This one bit field indicates when a SW command has been acknowledged by the CSRNG.
It is set to low each time a new command is written to [`SW_CMD_REQ.`](#sw_cmd_req)
The field is set to high once a SW command request has been acknowledged by the CSRNG.
0b0: The last SW command has not been acknowledged yet.
0b1: The last SW command has been acknowledged.

### SW_CMD_STS . CMD_RDY
This bit indicates when the EDN is ready to accept the next command.
Before starting to write a new command to [`SW_CMD_REQ`](#sw_cmd_req), this field needs to be polled.
0b0: The EDN is not ready to accept commands or the last command hasn't been acked yet.
0b1: The EDN is ready to accept the next command.

### SW_CMD_STS . CMD_REG_RDY
This bit indicates when [`SW_CMD_REQ`](#sw_cmd_req) is ready to accept the next word.
This bit has to be polled before each word of a command is written to [`SW_CMD_REQ.`](#sw_cmd_req)
0b0: The EDN is not ready to accept the next word yet.
0b1: The EDN is ready to accept the next word.

## HW_CMD_STS
EDN hardware command status register
- Offset: `0x28`
- Reset default: `0x0`
- Reset mask: `0x3ff`

### Fields

```wavejson
{"reg": [{"name": "BOOT_MODE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "AUTO_MODE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CMD_TYPE", "bits": 4, "attr": ["ro"], "rotate": -90}, {"name": "CMD_ACK", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CMD_STS", "bits": 3, "attr": ["ro"], "rotate": -90}, {"bits": 22}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name                                |
|:------:|:------:|:-------:|:------------------------------------|
| 31:10  |        |         | Reserved                            |
|  9:7   |   ro   |   0x0   | [CMD_STS](#hw_cmd_sts--cmd_sts)     |
|   6    |   ro   |   0x0   | [CMD_ACK](#hw_cmd_sts--cmd_ack)     |
|  5:2   |   ro   |   0x0   | [CMD_TYPE](#hw_cmd_sts--cmd_type)   |
|   1    |   ro   |   0x0   | [AUTO_MODE](#hw_cmd_sts--auto_mode) |
|   0    |   ro   |   0x0   | [BOOT_MODE](#hw_cmd_sts--boot_mode) |

### HW_CMD_STS . CMD_STS
This field represents the status code returned with the CSRNG application command ack.
It is updated each time a HW command is acknowledged by CSRNG.
A description of the command status types can be found [here](../../csrng/doc/registers.md#sw_cmd_sts--cmd_sts).

### HW_CMD_STS . CMD_ACK
This one bit field indicates when a HW command has been acknowledged by the CSRNG.
It is set to low each time a new command is sent to the CSRNG.
The field is set to high once a HW command request has been acknowledged by the CSRNG.
0b0: The last HW command has not been acknowledged yet.
0b1: The last HW command has been acknowledged.

### HW_CMD_STS . CMD_TYPE
This field contains the application command type of the hardware controlled command issued last.
The application command selects one of five operations to perform.
A description of the application command types can be found [here](../../csrng/doc/theory_of_operation.md#command-description).

### HW_CMD_STS . AUTO_MODE
This one bit field indicates whether the EDN is in the hardware controlled part of auto mode.
The instantiate command is issued via SW interface and is thus not part of the hardware controlled part of auto mode.
0b0: The EDN is not in the hardware controlled part of auto mode.
0b1: The EDN is in the hardware controlled part of auto mode.

### HW_CMD_STS . BOOT_MODE
This one bit field indicates whether the EDN is in the hardware controlled boot mode.
0b0: The EDN is not in boot mode.
0b1: The EDN is in boot mode.

## RESEED_CMD
EDN csrng reseed command register
- Offset: `0x2c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "RESEED_CMD", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                  |
|:------:|:------:|:-------:|:--------------------------------------|
|  31:0  |   wo   |    x    | [RESEED_CMD](#reseed_cmd--reseed_cmd) |

### RESEED_CMD . RESEED_CMD
Writing this register will fill a FIFO with up to 13 command words (32b words).
When running in auto request mode, this FIFO is used to automatically send out a `reseed` command to the CSRNG application interface after every MAX_NUM_REQS_BETWEEN_RESEEDS number of `generate` commands.

See [General Command Format](../../csrng/doc/theory_of_operation.md#general-command-format) for details about the command format.

Note that the number of additional data words provided must match the value of the `clen` field of the first word.
Otherwise, undefined behavior may result.
If more than 13 entries are written to the FIFO, they are ignored and EDN signals an `edn_fatal_err` interrupt as well as a fatal alert.

## GENERATE_CMD
EDN csrng generate command register
- Offset: `0x30`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "GENERATE_CMD", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                        |
|:------:|:------:|:-------:|:--------------------------------------------|
|  31:0  |   wo   |    x    | [GENERATE_CMD](#generate_cmd--generate_cmd) |

### GENERATE_CMD . GENERATE_CMD
Writing this register will fill a FIFO with up to 13 command words (32b words).
When running auto request mode, this FIFO is used to automatically send out `generate` commands to the CSRNG
application interface.

See [General Command Format](../../csrng/doc/theory_of_operation.md#general-command-format) for details about the command format.

Note that the number of additional data words provided must match the value of the `clen` field of the first word.
Otherwise, undefined behavior may result.
If more than 13 entries are written to the FIFO, they are ignored and EDN signals an `edn_fatal_err` interrupt as well as a fatal alert.

## MAX_NUM_REQS_BETWEEN_RESEEDS
EDN maximum number of requests between reseeds register
- Offset: `0x34`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "MAX_NUM_REQS_BETWEEN_RESEEDS", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                                                        |
|:------:|:------:|:-------:|:--------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | [MAX_NUM_REQS_BETWEEN_RESEEDS](#max_num_reqs_between_reseeds--max_num_reqs_between_reseeds) |

### MAX_NUM_REQS_BETWEEN_RESEEDS . MAX_NUM_REQS_BETWEEN_RESEEDS
Setting this field will set the number of `generate` command requests that are made
to CSRNG before a reseed request is made.
This value only has meaning when running in auto request mode.
This register supports a maximum of 2^32 `generate` requests between reseeds.
This register will be used by a counter that counts down, triggering an automatic `reseed` request when it reaches zero.

Note that this value must be chosen smaller than or equal to the value configured in the [`RESEED_INTERVAL` register of CSRNG](../../csrng/doc/registers.md#reseed-interval).

## RECOV_ALERT_STS
Recoverable alert status register
- Offset: `0x38`
- Reset default: `0x0`
- Reset mask: `0x300f`

### Fields

```wavejson
{"reg": [{"name": "EDN_ENABLE_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "BOOT_REQ_MODE_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "AUTO_REQ_MODE_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "CMD_FIFO_RST_FIELD_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 8}, {"name": "EDN_BUS_CMP_ALERT", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "CSRNG_ACK_ERR", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 18}], "config": {"lanes": 1, "fontsize": 10, "vspace": 270}}
```

|  Bits  |  Type  |  Reset  | Name                      | Description                                                                                                                                                                                     |
|:------:|:------:|:-------:|:--------------------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:14  |        |         |                           | Reserved                                                                                                                                                                                        |
|   13   |  rw0c  |   0x0   | CSRNG_ACK_ERR             | This bit is set when the CSRNG returns an acknowledgement where the status signal is non-zero. Writing a zero resets this status bit.                                                           |
|   12   |  rw0c  |   0x0   | EDN_BUS_CMP_ALERT         | This bit is set when the interal entropy bus value is equal to the prior valid value on the bus, indicating a possible attack. Writing a zero resets this status bit.                           |
|  11:4  |        |         |                           | Reserved                                                                                                                                                                                        |
|   3    |  rw0c  |   0x0   | CMD_FIFO_RST_FIELD_ALERT  | This bit is set when the CMD_FIFO_RST field is set to an illegal value, something other than kMultiBitBool4True or kMultiBitBool4False. Writing a zero resets this status bit.                  |
|   2    |  rw0c  |   0x0   | AUTO_REQ_MODE_FIELD_ALERT | This bit is set when the [`CTRL.AUTO_REQ_MODE`](#ctrl) field is set to an illegal value, something other than kMultiBitBool4True or kMultiBitBool4False. Writing a zero resets this status bit. |
|   1    |  rw0c  |   0x0   | BOOT_REQ_MODE_FIELD_ALERT | This bit is set when the BOOT_REQ_MODE field is set to an illegal value, something other than kMultiBitBool4True or kMultiBitBool4False. Writing a zero resets this status bit.                 |
|   0    |  rw0c  |   0x0   | EDN_ENABLE_FIELD_ALERT    | This bit is set when the EDN_ENABLE field is set to an illegal value, something other than kMultiBitBool4True or kMultiBitBool4False. Writing a zero resets this status bit.                    |

## ERR_CODE
Hardware detection of fatal error conditions status register
- Offset: `0x3c`
- Reset default: `0x0`
- Reset mask: `0x70700003`

### Fields

```wavejson
{"reg": [{"name": "SFIFO_RESCMD_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SFIFO_GENCMD_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 18}, {"name": "EDN_ACK_SM_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "EDN_MAIN_SM_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "EDN_CNTR_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 5}, {"name": "FIFO_WRITE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FIFO_READ_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FIFO_STATE_ERR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 1}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name                                            |
|:------:|:------:|:-------:|:------------------------------------------------|
|   31   |        |         | Reserved                                        |
|   30   |   ro   |   0x0   | [FIFO_STATE_ERR](#err_code--fifo_state_err)     |
|   29   |   ro   |   0x0   | [FIFO_READ_ERR](#err_code--fifo_read_err)       |
|   28   |   ro   |   0x0   | [FIFO_WRITE_ERR](#err_code--fifo_write_err)     |
| 27:23  |        |         | Reserved                                        |
|   22   |   ro   |   0x0   | [EDN_CNTR_ERR](#err_code--edn_cntr_err)         |
|   21   |   ro   |   0x0   | [EDN_MAIN_SM_ERR](#err_code--edn_main_sm_err)   |
|   20   |   ro   |   0x0   | [EDN_ACK_SM_ERR](#err_code--edn_ack_sm_err)     |
|  19:2  |        |         | Reserved                                        |
|   1    |   ro   |   0x0   | [SFIFO_GENCMD_ERR](#err_code--sfifo_gencmd_err) |
|   0    |   ro   |   0x0   | [SFIFO_RESCMD_ERR](#err_code--sfifo_rescmd_err) |

### ERR_CODE . FIFO_STATE_ERR
This bit will be set to one when any of the source bits (bits 0 through 1 of this register) are asserted as a result of an error pulse generated from any FIFO where both the empty and full status bits are set or in case of error conditions inside the hardened counters.
This bit will stay set until the next reset.

### ERR_CODE . FIFO_READ_ERR
This bit will be set to one when any of the source bits (bits 0 through 1 of this register) are asserted as a result of an error pulse generated from any empty FIFO that has received a read pulse.
This bit will stay set until the next reset.

### ERR_CODE . FIFO_WRITE_ERR
This bit will be set to one when any of the source bits (bits 0 through 1 of this register) are asserted as a result of an error pulse generated from any full FIFO that has received a write pulse.
This bit will stay set until the next reset.

### ERR_CODE . EDN_CNTR_ERR
This bit will be set to one when a hardened counter has detected an error
condition. This error will signal a fatal alert.
This bit will stay set until the next reset.

### ERR_CODE . EDN_MAIN_SM_ERR
This bit will be set to one when an illegal state has been detected for the
EDN main stage state machine. This error will signal a fatal alert.
This bit will stay set until the next reset.

### ERR_CODE . EDN_ACK_SM_ERR
This bit will be set to one when an illegal state has been detected for the
EDN ack stage state machine. This error will signal a fatal alert.
This bit will stay set until the next reset.

### ERR_CODE . SFIFO_GENCMD_ERR
This bit will be set to one when an error has been detected for the
generate command FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
When this bit is set, a fatal error condition will result.
This bit will stay set until the next reset.

### ERR_CODE . SFIFO_RESCMD_ERR
This bit will be set to one when an error has been detected for the
reseed command FIFO. The type of error is reflected in the type status
bits (bits 28 through 30 of this register).
When this bit is set, a fatal error condition will result.

## ERR_CODE_TEST
Test error conditions register
- Offset: `0x40`
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
Main state machine state observation register
- Offset: `0x44`
- Reset default: `0xc1`
- Reset mask: `0x1ff`

### Fields

```wavejson
{"reg": [{"name": "MAIN_SM_STATE", "bits": 9, "attr": ["ro"], "rotate": 0}, {"bits": 23}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                                                                    |
|:------:|:------:|:-------:|:--------------|:---------------------------------------------------------------------------------------------------------------|
|  31:9  |        |         |               | Reserved                                                                                                       |
|  8:0   |   ro   |  0xc1   | MAIN_SM_STATE | This is the state of the EDN main state machine. See the RTL file `edn_main_sm` for the meaning of the values. |


<!-- END CMDGEN -->
