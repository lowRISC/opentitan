# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/spi_device/data/spi_device.hjson -->
## Summary

| Name                                                     | Offset   |   Length | Description                                     |
|:---------------------------------------------------------|:---------|---------:|:------------------------------------------------|
| spi_device.[`INTR_STATE`](#intr_state)                   | 0x0      |        4 | Interrupt State Register                        |
| spi_device.[`INTR_ENABLE`](#intr_enable)                 | 0x4      |        4 | Interrupt Enable Register                       |
| spi_device.[`INTR_TEST`](#intr_test)                     | 0x8      |        4 | Interrupt Test Register                         |
| spi_device.[`ALERT_TEST`](#alert_test)                   | 0xc      |        4 | Alert Test Register                             |
| spi_device.[`CONTROL`](#control)                         | 0x10     |        4 | Control register                                |
| spi_device.[`CFG`](#cfg)                                 | 0x14     |        4 | Configuration Register                          |
| spi_device.[`STATUS`](#status)                           | 0x18     |        4 | SPI Device status register                      |
| spi_device.[`INTERCEPT_EN`](#intercept_en)               | 0x1c     |        4 | Intercept Passthrough datapath.                 |
| spi_device.[`ADDR_MODE`](#addr_mode)                     | 0x20     |        4 | Flash address mode configuration                |
| spi_device.[`LAST_READ_ADDR`](#last_read_addr)           | 0x24     |        4 | Last Read Address                               |
| spi_device.[`FLASH_STATUS`](#flash_status)               | 0x28     |        4 | SPI Flash Status register.                      |
| spi_device.[`JEDEC_CC`](#jedec_cc)                       | 0x2c     |        4 | JEDEC Continuation Code configuration register. |
| spi_device.[`JEDEC_ID`](#jedec_id)                       | 0x30     |        4 | JEDEC ID register.                              |
| spi_device.[`READ_THRESHOLD`](#read_threshold)           | 0x34     |        4 | Read Buffer threshold register.                 |
| spi_device.[`MAILBOX_ADDR`](#mailbox_addr)               | 0x38     |        4 | Mailbox Base address register.                  |
| spi_device.[`UPLOAD_STATUS`](#upload_status)             | 0x3c     |        4 | Upload module status register.                  |
| spi_device.[`UPLOAD_STATUS2`](#upload_status2)           | 0x40     |        4 | Upload module status 2 register.                |
| spi_device.[`UPLOAD_CMDFIFO`](#upload_cmdfifo)           | 0x44     |        4 | Command Fifo Read Port.                         |
| spi_device.[`UPLOAD_ADDRFIFO`](#upload_addrfifo)         | 0x48     |        4 | Address Fifo Read Port.                         |
| spi_device.[`CMD_FILTER_0`](#cmd_filter_0)               | 0x4c     |        4 | Command Filter                                  |
| spi_device.[`CMD_FILTER_1`](#cmd_filter_1)               | 0x50     |        4 | Command Filter                                  |
| spi_device.[`CMD_FILTER_2`](#cmd_filter_2)               | 0x54     |        4 | Command Filter                                  |
| spi_device.[`CMD_FILTER_3`](#cmd_filter_3)               | 0x58     |        4 | Command Filter                                  |
| spi_device.[`CMD_FILTER_4`](#cmd_filter_4)               | 0x5c     |        4 | Command Filter                                  |
| spi_device.[`CMD_FILTER_5`](#cmd_filter_5)               | 0x60     |        4 | Command Filter                                  |
| spi_device.[`CMD_FILTER_6`](#cmd_filter_6)               | 0x64     |        4 | Command Filter                                  |
| spi_device.[`CMD_FILTER_7`](#cmd_filter_7)               | 0x68     |        4 | Command Filter                                  |
| spi_device.[`ADDR_SWAP_MASK`](#addr_swap_mask)           | 0x6c     |        4 | Address Swap Mask register.                     |
| spi_device.[`ADDR_SWAP_DATA`](#addr_swap_data)           | 0x70     |        4 | The address value for the address swap feature. |
| spi_device.[`PAYLOAD_SWAP_MASK`](#payload_swap_mask)     | 0x74     |        4 | Write Data Swap in the passthrough mode.        |
| spi_device.[`PAYLOAD_SWAP_DATA`](#payload_swap_data)     | 0x78     |        4 | Write Data Swap in the passthrough mode.        |
| spi_device.[`CMD_INFO_0`](#cmd_info)                     | 0x7c     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_1`](#cmd_info)                     | 0x80     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_2`](#cmd_info)                     | 0x84     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_3`](#cmd_info)                     | 0x88     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_4`](#cmd_info)                     | 0x8c     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_5`](#cmd_info)                     | 0x90     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_6`](#cmd_info)                     | 0x94     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_7`](#cmd_info)                     | 0x98     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_8`](#cmd_info)                     | 0x9c     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_9`](#cmd_info)                     | 0xa0     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_10`](#cmd_info)                    | 0xa4     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_11`](#cmd_info)                    | 0xa8     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_12`](#cmd_info)                    | 0xac     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_13`](#cmd_info)                    | 0xb0     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_14`](#cmd_info)                    | 0xb4     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_15`](#cmd_info)                    | 0xb8     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_16`](#cmd_info)                    | 0xbc     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_17`](#cmd_info)                    | 0xc0     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_18`](#cmd_info)                    | 0xc4     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_19`](#cmd_info)                    | 0xc8     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_20`](#cmd_info)                    | 0xcc     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_21`](#cmd_info)                    | 0xd0     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_22`](#cmd_info)                    | 0xd4     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_23`](#cmd_info)                    | 0xd8     |        4 | Command Info register.                          |
| spi_device.[`CMD_INFO_EN4B`](#cmd_info_en4b)             | 0xdc     |        4 | Opcode for EN4B.                                |
| spi_device.[`CMD_INFO_EX4B`](#cmd_info_ex4b)             | 0xe0     |        4 | Opcode for EX4B                                 |
| spi_device.[`CMD_INFO_WREN`](#cmd_info_wren)             | 0xe4     |        4 | Opcode for Write Enable (WREN)                  |
| spi_device.[`CMD_INFO_WRDI`](#cmd_info_wrdi)             | 0xe8     |        4 | Opcode for Write Disable (WRDI)                 |
| spi_device.[`TPM_CAP`](#tpm_cap)                         | 0x800    |        4 | TPM HWIP Capability register.                   |
| spi_device.[`TPM_CFG`](#tpm_cfg)                         | 0x804    |        4 | TPM Configuration register.                     |
| spi_device.[`TPM_STATUS`](#tpm_status)                   | 0x808    |        4 | TPM submodule state register.                   |
| spi_device.[`TPM_ACCESS_0`](#tpm_access_0)               | 0x80c    |        4 | TPM_ACCESS_x register.                          |
| spi_device.[`TPM_ACCESS_1`](#tpm_access_1)               | 0x810    |        4 | TPM_ACCESS_x register.                          |
| spi_device.[`TPM_STS`](#tpm_sts)                         | 0x814    |        4 | TPM_STS_x register.                             |
| spi_device.[`TPM_INTF_CAPABILITY`](#tpm_intf_capability) | 0x818    |        4 | TPM_INTF_CAPABILITY                             |
| spi_device.[`TPM_INT_ENABLE`](#tpm_int_enable)           | 0x81c    |        4 | TPM_INT_ENABLE                                  |
| spi_device.[`TPM_INT_VECTOR`](#tpm_int_vector)           | 0x820    |        4 | TPM_INT_VECTOR                                  |
| spi_device.[`TPM_INT_STATUS`](#tpm_int_status)           | 0x824    |        4 | TPM_INT_STATUS                                  |
| spi_device.[`TPM_DID_VID`](#tpm_did_vid)                 | 0x828    |        4 | TPM_DID/ TPM_VID register                       |
| spi_device.[`TPM_RID`](#tpm_rid)                         | 0x82c    |        4 | TPM_RID                                         |
| spi_device.[`TPM_CMD_ADDR`](#tpm_cmd_addr)               | 0x830    |        4 | TPM Command and Address buffer                  |
| spi_device.[`TPM_READ_FIFO`](#tpm_read_fifo)             | 0x834    |        4 | TPM Read command return data FIFO.              |
| spi_device.[`egress_buffer`](#egress_buffer)             | 0x1000   |     3392 | SPI internal egress buffer.                     |
| spi_device.[`ingress_buffer`](#ingress_buffer)           | 0x1e00   |      448 | SPI internal ingress buffer.                    |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "upload_cmdfifo_not_empty", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "upload_payload_not_empty", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "upload_payload_overflow", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "readbuf_watermark", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "readbuf_flip", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "tpm_header_not_empty", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "tpm_rdfifo_cmd_end", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "tpm_rdfifo_drop", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 260}}
```

|  Bits  |  Type  |  Reset  | Name                     | Description                                                                                                                                                                                                                                         |
|:------:|:------:|:-------:|:-------------------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:8  |        |         |                          | Reserved                                                                                                                                                                                                                                            |
|   7    |  rw1c  |   0x0   | tpm_rdfifo_drop          | TPM RdFIFO data dropped. Data was dropped from the RdFIFO. Data was written while a read command was not active, and it was not accepted. This can occur when the host aborts a read command.                                                       |
|   6    |  rw1c  |   0x0   | tpm_rdfifo_cmd_end       | TPM RdFIFO command ended. The TPM Read command targeting the RdFIFO ended. Check TPM_STATUS.rdfifo_aborted to see if the transaction completed.                                                                                                     |
|   5    |   ro   |   0x0   | tpm_header_not_empty     | TPM Header(Command/Address) buffer available                                                                                                                                                                                                        |
|   4    |  rw1c  |   0x0   | readbuf_flip             | Read buffer flipped event. The host system accesses other side of buffer.                                                                                                                                                                           |
|   3    |  rw1c  |   0x0   | readbuf_watermark        | Read Buffer Threshold event. The host system accesses greater than or equal to the threshold of a buffer.                                                                                                                                           |
|   2    |  rw1c  |   0x0   | upload_payload_overflow  | Upload payload overflow event. When a SPI Host system issues a command with payload more than 256B, this event is reported. When it happens, SW should read the last written payload index CSR to figure out the starting address of the last 256B. |
|   1    |  rw1c  |   0x0   | upload_payload_not_empty | Upload payload is not empty. The event occurs after SPI transaction completed                                                                                                                                                                       |
|   0    |  rw1c  |   0x0   | upload_cmdfifo_not_empty | Upload Command FIFO is not empty                                                                                                                                                                                                                    |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "upload_cmdfifo_not_empty", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "upload_payload_not_empty", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "upload_payload_overflow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "readbuf_watermark", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "readbuf_flip", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "tpm_header_not_empty", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "tpm_rdfifo_cmd_end", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "tpm_rdfifo_drop", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 260}}
```

|  Bits  |  Type  |  Reset  | Name                     | Description                                                                        |
|:------:|:------:|:-------:|:-------------------------|:-----------------------------------------------------------------------------------|
|  31:8  |        |         |                          | Reserved                                                                           |
|   7    |   rw   |   0x0   | tpm_rdfifo_drop          | Enable interrupt when [`INTR_STATE.tpm_rdfifo_drop`](#intr_state) is set.          |
|   6    |   rw   |   0x0   | tpm_rdfifo_cmd_end       | Enable interrupt when [`INTR_STATE.tpm_rdfifo_cmd_end`](#intr_state) is set.       |
|   5    |   rw   |   0x0   | tpm_header_not_empty     | Enable interrupt when [`INTR_STATE.tpm_header_not_empty`](#intr_state) is set.     |
|   4    |   rw   |   0x0   | readbuf_flip             | Enable interrupt when [`INTR_STATE.readbuf_flip`](#intr_state) is set.             |
|   3    |   rw   |   0x0   | readbuf_watermark        | Enable interrupt when [`INTR_STATE.readbuf_watermark`](#intr_state) is set.        |
|   2    |   rw   |   0x0   | upload_payload_overflow  | Enable interrupt when [`INTR_STATE.upload_payload_overflow`](#intr_state) is set.  |
|   1    |   rw   |   0x0   | upload_payload_not_empty | Enable interrupt when [`INTR_STATE.upload_payload_not_empty`](#intr_state) is set. |
|   0    |   rw   |   0x0   | upload_cmdfifo_not_empty | Enable interrupt when [`INTR_STATE.upload_cmdfifo_not_empty`](#intr_state) is set. |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "upload_cmdfifo_not_empty", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "upload_payload_not_empty", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "upload_payload_overflow", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "readbuf_watermark", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "readbuf_flip", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "tpm_header_not_empty", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "tpm_rdfifo_cmd_end", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "tpm_rdfifo_drop", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 260}}
```

|  Bits  |  Type  |  Reset  | Name                     | Description                                                                 |
|:------:|:------:|:-------:|:-------------------------|:----------------------------------------------------------------------------|
|  31:8  |        |         |                          | Reserved                                                                    |
|   7    |   wo   |   0x0   | tpm_rdfifo_drop          | Write 1 to force [`INTR_STATE.tpm_rdfifo_drop`](#intr_state) to 1.          |
|   6    |   wo   |   0x0   | tpm_rdfifo_cmd_end       | Write 1 to force [`INTR_STATE.tpm_rdfifo_cmd_end`](#intr_state) to 1.       |
|   5    |   wo   |   0x0   | tpm_header_not_empty     | Write 1 to force [`INTR_STATE.tpm_header_not_empty`](#intr_state) to 1.     |
|   4    |   wo   |   0x0   | readbuf_flip             | Write 1 to force [`INTR_STATE.readbuf_flip`](#intr_state) to 1.             |
|   3    |   wo   |   0x0   | readbuf_watermark        | Write 1 to force [`INTR_STATE.readbuf_watermark`](#intr_state) to 1.        |
|   2    |   wo   |   0x0   | upload_payload_overflow  | Write 1 to force [`INTR_STATE.upload_payload_overflow`](#intr_state) to 1.  |
|   1    |   wo   |   0x0   | upload_payload_not_empty | Write 1 to force [`INTR_STATE.upload_payload_not_empty`](#intr_state) to 1. |
|   0    |   wo   |   0x0   | upload_cmdfifo_not_empty | Write 1 to force [`INTR_STATE.upload_cmdfifo_not_empty`](#intr_state) to 1. |

## ALERT_TEST
Alert Test Register
- Offset: `0xc`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "fatal_fault", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                      |
|:------:|:------:|:-------:|:------------|:-------------------------------------------------|
|  31:1  |        |         |             | Reserved                                         |
|   0    |   wo   |   0x0   | fatal_fault | Write 1 to trigger one alert event of this kind. |

## CONTROL
Control register
- Offset: `0x10`
- Reset default: `0x10`
- Reset mask: `0x33`

### Fields

```wavejson
{"reg": [{"name": "FLASH_STATUS_FIFO_CLR", "bits": 1, "attr": ["rw1s"], "rotate": -90}, {"name": "FLASH_READ_BUFFER_CLR", "bits": 1, "attr": ["rw1s"], "rotate": -90}, {"bits": 2}, {"name": "MODE", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 26}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                                                     |
|:------:|:------:|:-------:|:---------------------------------------------------------|
|  31:6  |        |         | Reserved                                                 |
|  5:4   |   rw   |   0x1   | [MODE](#control--mode)                                   |
|  3:2   |        |         | Reserved                                                 |
|   1    |  rw1s  |   0x0   | [FLASH_READ_BUFFER_CLR](#control--flash_read_buffer_clr) |
|   0    |  rw1s  |   0x0   | [FLASH_STATUS_FIFO_CLR](#control--flash_status_fifo_clr) |

### CONTROL . MODE
SPI Device flash operation mode.

| Value   | Name        | Description                                                                                                                                                                                                                                                                |
|:--------|:------------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0x0     | disabled    | SPI Flash operations disabled. SPI device flash operations are disabled, and all transactions are ignored. Note that SPI TPM operations are controlled by !!TPM_CFG                                                                                                        |
| 0x1     | flashmode   | SPI Flash Emulation mode. In flash mode, SPI Device IP accepts SPI Flash commands and processes internally, then returns data for the read commands. HW processes the Status, JEDEC ID, SFDP commands. The current version does not support Dual/Quad IO and QPI commands. |
| 0x2     | passthrough | In passthrough mode, SPI Device IP forwards the incoming SPI flash traffics to the attached downstream flash device. HW may processes commands internally and returns data. SW may configure the device to drop inadmissable commands.                                     |

Other values are reserved.

### CONTROL . FLASH_READ_BUFFER_CLR
Set to clear the read buffer state.

When set to 1, resets the flash read buffer state that tracks the host read address.
The reset should only be used when the upstream SPI host is known to be inactive.
This function is intended to allow restoring initial values when the upstream SPI host is reset.

This CSR automatically resets to 0.

### CONTROL . FLASH_STATUS_FIFO_CLR
Set to clear the flash status FIFO.

When set to 1, resets the flash status FIFO used for synchronizing changes from firmware.
The reset should only be used when the upstream SPI host is known to be inactive.
This function is intended to allow restoring initial values when the upstream SPI host is reset.

This CSR automatically resets to 0.

## CFG
Configuration Register
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0x100000c`

### Fields

```wavejson
{"reg": [{"bits": 2}, {"name": "tx_order", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rx_order", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 20}, {"name": "mailbox_en", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 7}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                                                                                                                                                                                    |
|:------:|:------:|:-------:|:-----------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:25  |        |         |            | Reserved                                                                                                                                                                                                                       |
|   24   |   rw   |   0x0   | mailbox_en | Mailbox enable. If 1, in the flash and passthrough mode, the IP checks the incoming address and return from the internal Mailbox buffer if the address falls into the MAILBOX range (MAILBOX_ADDR:MAILBOX_ADDR+MAILBOX_SIZE)}. |
|  23:4  |        |         |            | Reserved                                                                                                                                                                                                                       |
|   3    |   rw   |   0x0   | rx_order   | RX bit order on SDI. Module stores bitstream from MSB to LSB if value is 0.                                                                                                                                                    |
|   2    |   rw   |   0x0   | tx_order   | TX bit order on SDO. 0 for MSB to LSB, 1 for LSB to MSB                                                                                                                                                                        |
|  1:0   |        |         |            | Reserved                                                                                                                                                                                                                       |

## STATUS
SPI Device status register
- Offset: `0x18`
- Reset default: `0x60`
- Reset mask: `0x60`

### Fields

```wavejson
{"reg": [{"bits": 5}, {"name": "csb", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "tpm_csb", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 25}], "config": {"lanes": 1, "fontsize": 10, "vspace": 90}}
```

|  Bits  |  Type  |  Reset  | Name    | Description                |
|:------:|:------:|:-------:|:--------|:---------------------------|
|  31:7  |        |         |         | Reserved                   |
|   6    |   ro   |   0x1   | tpm_csb | Direct input of TPM CSb    |
|   5    |   ro   |   0x1   | csb     | Direct input of CSb signal |
|  4:0   |        |         |         | Reserved                   |

## INTERCEPT_EN
Intercept Passthrough datapath.

- Offset: `0x1c`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "status", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "jedec", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "sfdp", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "mbx", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                     |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------|
|  31:4  |        |         |        | Reserved                                                        |
|   3    |   rw   |   0x0   | mbx    | If set, Read Command to Mailbox region is processed internally. |
|   2    |   rw   |   0x0   | sfdp   | If set, Read SFDP is processed internally.                      |
|   1    |   rw   |   0x0   | jedec  | If set, Read JEDEC ID is processed internally.                  |
|   0    |   rw   |   0x0   | status | If set, Read Status is processed internally.                    |

## ADDR_MODE
Flash address mode configuration

This register shows the current address mode and pending changes.
It is updated by the HW when the command phase completes.
- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0x80000001`

### Fields

```wavejson
{"reg": [{"name": "addr_4b_en", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}, {"name": "pending", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name                                 |
|:------:|:------:|:-------:|:-------------------------------------|
|   31   |   ro   |    x    | [pending](#addr_mode--pending)       |
|  30:1  |        |         | Reserved                             |
|   0    |   rw   |    x    | [addr_4b_en](#addr_mode--addr_4b_en) |

### ADDR_MODE . pending
SW-originated change is pending.

This bit is 1 whenever the current value of addr_4b_en has yet to sync with the SPI domain.
If an EN4B or EX4B command arrives next, the current value in `addr_4b_en` will be ignored,
and the SPI flash command will take priority, with an update to `addr_4b_en` to match the command's result.

### ADDR_MODE . addr_4b_en
4B Address Mode enable.

This field configures the internal module to receive 32 bits of the SPI commands.
The affected commands are the SPI read commands except QPI, and program commands.
It is expected for SW to configure this field at the configuration stage and release control to HW until the next reset.

Even though Read SFDP command has address fields, the SFDP command is not affected by this field.
The command always parse 24 bits on the SPI line 0 following the SPI command as the address field.

This field has noteworthy read behavior.
If a software-initiated change is still `pending` the sync to the SPI domain, this bit will reflect the value to be sent.
Otherwise, this field will reflect the current value observed in the SPI domain.

## LAST_READ_ADDR
Last Read Address

This register shows the last address accessed by the host system.
It is updated by the HW when CSb is de-asserted.
- Offset: `0x24`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "addr", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:0  |   ro   |    x    | addr   | Last address  |

## FLASH_STATUS
SPI Flash Status register.

This register emulates the SPI Flash Status 3, 2, 1 registers.
bit [7:0] is for Status register, bit [15:8] is for Status-2 register,
and bit [23:16] is for Status-3 register. It is SW responsibility to
maintain this register value up to date.

When software writes a value here, it is delivered to a staging async FIFO, where it waits for the SPI side to commit it.
Any updates require at least 8 SPI clocks before they commit on the SPI side, which is the source-of-truth.
After committing on the SPI side, the CSRs will eventually update with the latest value.
- Offset: `0x28`
- Reset default: `0x0`
- Reset mask: `0xffffff`

### Fields

```wavejson
{"reg": [{"name": "busy", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "wel", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "status", "bits": 22, "attr": ["rw"], "rotate": 0}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                            |
|:------:|:------:|:-------:|:--------------------------------|
| 31:24  |        |         | Reserved                        |
|  23:2  |   rw   |    x    | [status](#flash_status--status) |
|   1    |  rw0c  |    x    | [wel](#flash_status--wel)       |
|   0    |  rw0c  |    x    | [busy](#flash_status--busy)     |

### FLASH_STATUS . status
Rest of the status register.

Fields other than the bit 0 (BUSY) and bit 1 (WEL) fields are
SW-maintained fields. HW just reads and returns to the host system.

- [ 2]\: BP0
- [ 3]\: BP1
- [ 4]\: BP2
- [ 5]\: TB
- [ 6]\: SEC
- [ 7]\: SRP0
- [ 8]\: SRP1
- [ 9]\: QE
- [11]\: LB1
- [12]\: LB2
- [13]\: LB3
- [14]\: CMP
- [15]\: SUS
- [18]\: WPS
- [21]\: DRV0
- [22]\: DRV1
- [23]\: HOLD /RST

### FLASH_STATUS . wel
The Write Enable Latch signal.
SW should read back the register to confirm the value is cleared.

Bit 1 (WEL) is a SW modifiable and HW modifiable field.
HW updates the WEL field when `WRDI` or `WREN` command is received.

### FLASH_STATUS . busy
The BUSY signal. SW should read back the register to confirm the value is cleared.

Bit 0 (BUSY) is a SW modifiable and HW modifiable field.
HW updates the BUSY field for matching uploaded commands in the CMD_INFO table, when the `upload` and `busy` bits are set in the table entry.

Note that the observable state of the BUSY bit updates every 8 SPI clocks.
This enables continuous polling of the BUSY bit.
However, the passthrough gate (for passthrough mode) only updates when CSB is de-asserted, not on SPI clocks.

## JEDEC_CC
JEDEC Continuation Code configuration register.

Read JEDEC ID must return the continuation code if the manufacturer ID
is not shown in the first page of JEDEC table. This register controls
the Continuation Code.
- Offset: `0x2c`
- Reset default: `0x7f`
- Reset mask: `0xffff`

### Fields

```wavejson
{"reg": [{"name": "cc", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "num_cc", "bits": 8, "attr": ["rw"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                               |
|:------:|:------:|:-------:|:-------|:------------------------------------------|
| 31:16  |        |         |        | Reserved                                  |
|  15:8  |   rw   |   0x0   | num_cc | The number that Continuation Code repeats |
|  7:0   |   rw   |  0x7f   | cc     | Continuation Code byte                    |

## JEDEC_ID
JEDEC ID register.
- Offset: `0x30`
- Reset default: `0x0`
- Reset mask: `0xffffff`

### Fields

```wavejson
{"reg": [{"name": "id", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "mf", "bits": 8, "attr": ["rw"], "rotate": 0}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
| 31:24  |        |         |        | Reserved        |
| 23:16  |   rw   |   0x0   | mf     | Manufacturer ID |
|  15:0  |   rw   |   0x0   | id     | Device ID       |

## READ_THRESHOLD
Read Buffer threshold register.

- Offset: `0x34`
- Reset default: `0x0`
- Reset mask: `0x3ff`

### Fields

```wavejson
{"reg": [{"name": "threshold", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 22}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                                                                                                                            |
|:------:|:------:|:-------:|:----------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:10  |        |         |           | Reserved                                                                                                                                                               |
|  9:0   |   rw   |   0x0   | threshold | If 0, disable the watermark. If non-zero, when the host access above or equal to the threshold, it reports an interrupt. The value is byte-granularity not SRAM index. |

## MAILBOX_ADDR
Mailbox Base address register.

The mailbox size is fixed. In this version of IP, the size is 1kB.
Lower 10 bits of the Mailbox address is tied to 0.
- Offset: `0x38`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "addr", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                |
|:------:|:------:|:-------:|:-------|:-------------------------------------------|
|  31:0  |   rw   |   0x0   | addr   | Mailbox Address. Lower 10 bits are ignored |

## UPLOAD_STATUS
Upload module status register.
- Offset: `0x3c`
- Reset default: `0x0`
- Reset mask: `0x9f9f`

### Fields

```wavejson
{"reg": [{"name": "cmdfifo_depth", "bits": 5, "attr": ["ro"], "rotate": -90}, {"bits": 2}, {"name": "cmdfifo_notempty", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "addrfifo_depth", "bits": 5, "attr": ["ro"], "rotate": -90}, {"bits": 2}, {"name": "addrfifo_notempty", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                   |
|:------:|:------:|:-------:|:------------------|:------------------------------|
| 31:16  |        |         |                   | Reserved                      |
|   15   |   ro   |   0x0   | addrfifo_notempty | Upload Address FIFO Not Empty |
| 14:13  |        |         |                   | Reserved                      |
|  12:8  |   ro   |   0x0   | addrfifo_depth    | Address FIFO Entry            |
|   7    |   ro   |   0x0   | cmdfifo_notempty  | Upload Command FIFO Not Empty |
|  6:5   |        |         |                   | Reserved                      |
|  4:0   |   ro   |   0x0   | cmdfifo_depth     | Command FIFO Entry            |

## UPLOAD_STATUS2
Upload module status 2 register.

This register contains payload related status. payload_depth indicates
the payload size (from 0 to 256 bytes).

payload_start_idx indicates the start of the 256B. This stays 0
usually. However, when the SPI host system issues more than 256B of
payload in a command, this field may not be 0. For example, if the
system issues 258B payload, the payload_depth is 256 (as the IP only
holds 256B of payload), the payload_start_idx is 2. SW should read from
2 to 255 then 0 and 1.
- Offset: `0x40`
- Reset default: `0x0`
- Reset mask: `0xff01ff`

### Fields

```wavejson
{"reg": [{"name": "payload_depth", "bits": 9, "attr": ["ro"], "rotate": 0}, {"bits": 7}, {"name": "payload_start_idx", "bits": 8, "attr": ["ro"], "rotate": -90}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name              | Description          |
|:------:|:------:|:-------:|:------------------|:---------------------|
| 31:24  |        |         |                   | Reserved             |
| 23:16  |   ro   |   0x0   | payload_start_idx | Payload Start Index  |
|  15:9  |        |         |                   | Reserved             |
|  8:0   |   ro   |   0x0   | payload_depth     | Payload buffer depth |

## UPLOAD_CMDFIFO
Command Fifo Read Port.
- Offset: `0x44`
- Reset default: `0x0`
- Reset mask: `0xe0ff`

### Fields

```wavejson
{"reg": [{"name": "data", "bits": 8, "attr": ["ro"], "rotate": 0}, {"bits": 5}, {"name": "busy", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "wel", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "addr4b_mode", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                |
|:------:|:------:|:-------:|:------------|:-----------------------------------------------------------|
| 31:16  |        |         |             | Reserved                                                   |
|   15   |   ro   |    x    | addr4b_mode | 1 if address mode at command time is 4 Bytes, else 3 Bytes |
|   14   |   ro   |    x    | wel         | State of WEL bit at command time                           |
|   13   |   ro   |    x    | busy        | State of BUSY bit at command time                          |
|  12:8  |        |         |             | Reserved                                                   |
|  7:0   |   ro   |    x    | data        | command opcode                                             |

## UPLOAD_ADDRFIFO
Address Fifo Read Port.
- Offset: `0x48`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "data", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:0  |   ro   |    x    | data   | read data     |

## CMD_FILTER_0
Command Filter

If a bit in this CSR is 1, then corresponding SPI command w.r.t the
bit position among 256 bit is dropped in SPI Passthrough mode.
- Offset: `0x4c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "filter_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_4", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_5", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_6", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_7", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_8", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_9", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_10", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_11", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_12", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_13", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_14", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_15", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_16", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_17", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_18", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_19", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_20", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_21", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_22", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_23", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_24", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_25", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_26", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_27", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_28", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_29", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_30", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_31", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                    |
|:------:|:------:|:-------:|:----------|:-------------------------------|
|   31   |   rw   |   0x0   | filter_31 | If 1, command will be filtered |
|   30   |   rw   |   0x0   | filter_30 | If 1, command will be filtered |
|   29   |   rw   |   0x0   | filter_29 | If 1, command will be filtered |
|   28   |   rw   |   0x0   | filter_28 | If 1, command will be filtered |
|   27   |   rw   |   0x0   | filter_27 | If 1, command will be filtered |
|   26   |   rw   |   0x0   | filter_26 | If 1, command will be filtered |
|   25   |   rw   |   0x0   | filter_25 | If 1, command will be filtered |
|   24   |   rw   |   0x0   | filter_24 | If 1, command will be filtered |
|   23   |   rw   |   0x0   | filter_23 | If 1, command will be filtered |
|   22   |   rw   |   0x0   | filter_22 | If 1, command will be filtered |
|   21   |   rw   |   0x0   | filter_21 | If 1, command will be filtered |
|   20   |   rw   |   0x0   | filter_20 | If 1, command will be filtered |
|   19   |   rw   |   0x0   | filter_19 | If 1, command will be filtered |
|   18   |   rw   |   0x0   | filter_18 | If 1, command will be filtered |
|   17   |   rw   |   0x0   | filter_17 | If 1, command will be filtered |
|   16   |   rw   |   0x0   | filter_16 | If 1, command will be filtered |
|   15   |   rw   |   0x0   | filter_15 | If 1, command will be filtered |
|   14   |   rw   |   0x0   | filter_14 | If 1, command will be filtered |
|   13   |   rw   |   0x0   | filter_13 | If 1, command will be filtered |
|   12   |   rw   |   0x0   | filter_12 | If 1, command will be filtered |
|   11   |   rw   |   0x0   | filter_11 | If 1, command will be filtered |
|   10   |   rw   |   0x0   | filter_10 | If 1, command will be filtered |
|   9    |   rw   |   0x0   | filter_9  | If 1, command will be filtered |
|   8    |   rw   |   0x0   | filter_8  | If 1, command will be filtered |
|   7    |   rw   |   0x0   | filter_7  | If 1, command will be filtered |
|   6    |   rw   |   0x0   | filter_6  | If 1, command will be filtered |
|   5    |   rw   |   0x0   | filter_5  | If 1, command will be filtered |
|   4    |   rw   |   0x0   | filter_4  | If 1, command will be filtered |
|   3    |   rw   |   0x0   | filter_3  | If 1, command will be filtered |
|   2    |   rw   |   0x0   | filter_2  | If 1, command will be filtered |
|   1    |   rw   |   0x0   | filter_1  | If 1, command will be filtered |
|   0    |   rw   |   0x0   | filter_0  | If 1, command will be filtered |

## CMD_FILTER_1
Command Filter

If a bit in this CSR is 1, then corresponding SPI command w.r.t the
bit position among 256 bit is dropped in SPI Passthrough mode.
- Offset: `0x50`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "filter_32", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_33", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_34", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_35", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_36", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_37", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_38", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_39", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_40", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_41", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_42", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_43", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_44", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_45", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_46", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_47", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_48", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_49", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_50", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_51", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_52", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_53", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_54", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_55", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_56", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_57", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_58", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_59", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_60", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_61", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_62", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_63", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description     |
|:------:|:------:|:-------:|:----------|:----------------|
|   31   |   rw   |   0x0   | filter_63 | For SPI_DEVICE1 |
|   30   |   rw   |   0x0   | filter_62 | For SPI_DEVICE1 |
|   29   |   rw   |   0x0   | filter_61 | For SPI_DEVICE1 |
|   28   |   rw   |   0x0   | filter_60 | For SPI_DEVICE1 |
|   27   |   rw   |   0x0   | filter_59 | For SPI_DEVICE1 |
|   26   |   rw   |   0x0   | filter_58 | For SPI_DEVICE1 |
|   25   |   rw   |   0x0   | filter_57 | For SPI_DEVICE1 |
|   24   |   rw   |   0x0   | filter_56 | For SPI_DEVICE1 |
|   23   |   rw   |   0x0   | filter_55 | For SPI_DEVICE1 |
|   22   |   rw   |   0x0   | filter_54 | For SPI_DEVICE1 |
|   21   |   rw   |   0x0   | filter_53 | For SPI_DEVICE1 |
|   20   |   rw   |   0x0   | filter_52 | For SPI_DEVICE1 |
|   19   |   rw   |   0x0   | filter_51 | For SPI_DEVICE1 |
|   18   |   rw   |   0x0   | filter_50 | For SPI_DEVICE1 |
|   17   |   rw   |   0x0   | filter_49 | For SPI_DEVICE1 |
|   16   |   rw   |   0x0   | filter_48 | For SPI_DEVICE1 |
|   15   |   rw   |   0x0   | filter_47 | For SPI_DEVICE1 |
|   14   |   rw   |   0x0   | filter_46 | For SPI_DEVICE1 |
|   13   |   rw   |   0x0   | filter_45 | For SPI_DEVICE1 |
|   12   |   rw   |   0x0   | filter_44 | For SPI_DEVICE1 |
|   11   |   rw   |   0x0   | filter_43 | For SPI_DEVICE1 |
|   10   |   rw   |   0x0   | filter_42 | For SPI_DEVICE1 |
|   9    |   rw   |   0x0   | filter_41 | For SPI_DEVICE1 |
|   8    |   rw   |   0x0   | filter_40 | For SPI_DEVICE1 |
|   7    |   rw   |   0x0   | filter_39 | For SPI_DEVICE1 |
|   6    |   rw   |   0x0   | filter_38 | For SPI_DEVICE1 |
|   5    |   rw   |   0x0   | filter_37 | For SPI_DEVICE1 |
|   4    |   rw   |   0x0   | filter_36 | For SPI_DEVICE1 |
|   3    |   rw   |   0x0   | filter_35 | For SPI_DEVICE1 |
|   2    |   rw   |   0x0   | filter_34 | For SPI_DEVICE1 |
|   1    |   rw   |   0x0   | filter_33 | For SPI_DEVICE1 |
|   0    |   rw   |   0x0   | filter_32 | For SPI_DEVICE1 |

## CMD_FILTER_2
Command Filter

If a bit in this CSR is 1, then corresponding SPI command w.r.t the
bit position among 256 bit is dropped in SPI Passthrough mode.
- Offset: `0x54`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "filter_64", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_65", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_66", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_67", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_68", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_69", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_70", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_71", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_72", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_73", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_74", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_75", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_76", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_77", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_78", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_79", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_80", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_81", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_82", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_83", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_84", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_85", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_86", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_87", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_88", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_89", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_90", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_91", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_92", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_93", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_94", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_95", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description     |
|:------:|:------:|:-------:|:----------|:----------------|
|   31   |   rw   |   0x0   | filter_95 | For SPI_DEVICE2 |
|   30   |   rw   |   0x0   | filter_94 | For SPI_DEVICE2 |
|   29   |   rw   |   0x0   | filter_93 | For SPI_DEVICE2 |
|   28   |   rw   |   0x0   | filter_92 | For SPI_DEVICE2 |
|   27   |   rw   |   0x0   | filter_91 | For SPI_DEVICE2 |
|   26   |   rw   |   0x0   | filter_90 | For SPI_DEVICE2 |
|   25   |   rw   |   0x0   | filter_89 | For SPI_DEVICE2 |
|   24   |   rw   |   0x0   | filter_88 | For SPI_DEVICE2 |
|   23   |   rw   |   0x0   | filter_87 | For SPI_DEVICE2 |
|   22   |   rw   |   0x0   | filter_86 | For SPI_DEVICE2 |
|   21   |   rw   |   0x0   | filter_85 | For SPI_DEVICE2 |
|   20   |   rw   |   0x0   | filter_84 | For SPI_DEVICE2 |
|   19   |   rw   |   0x0   | filter_83 | For SPI_DEVICE2 |
|   18   |   rw   |   0x0   | filter_82 | For SPI_DEVICE2 |
|   17   |   rw   |   0x0   | filter_81 | For SPI_DEVICE2 |
|   16   |   rw   |   0x0   | filter_80 | For SPI_DEVICE2 |
|   15   |   rw   |   0x0   | filter_79 | For SPI_DEVICE2 |
|   14   |   rw   |   0x0   | filter_78 | For SPI_DEVICE2 |
|   13   |   rw   |   0x0   | filter_77 | For SPI_DEVICE2 |
|   12   |   rw   |   0x0   | filter_76 | For SPI_DEVICE2 |
|   11   |   rw   |   0x0   | filter_75 | For SPI_DEVICE2 |
|   10   |   rw   |   0x0   | filter_74 | For SPI_DEVICE2 |
|   9    |   rw   |   0x0   | filter_73 | For SPI_DEVICE2 |
|   8    |   rw   |   0x0   | filter_72 | For SPI_DEVICE2 |
|   7    |   rw   |   0x0   | filter_71 | For SPI_DEVICE2 |
|   6    |   rw   |   0x0   | filter_70 | For SPI_DEVICE2 |
|   5    |   rw   |   0x0   | filter_69 | For SPI_DEVICE2 |
|   4    |   rw   |   0x0   | filter_68 | For SPI_DEVICE2 |
|   3    |   rw   |   0x0   | filter_67 | For SPI_DEVICE2 |
|   2    |   rw   |   0x0   | filter_66 | For SPI_DEVICE2 |
|   1    |   rw   |   0x0   | filter_65 | For SPI_DEVICE2 |
|   0    |   rw   |   0x0   | filter_64 | For SPI_DEVICE2 |

## CMD_FILTER_3
Command Filter

If a bit in this CSR is 1, then corresponding SPI command w.r.t the
bit position among 256 bit is dropped in SPI Passthrough mode.
- Offset: `0x58`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "filter_96", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_97", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_98", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_99", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_100", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_101", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_102", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_103", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_104", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_105", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_106", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_107", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_108", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_109", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_110", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_111", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_112", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_113", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_114", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_115", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_116", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_117", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_118", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_119", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_120", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_121", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_122", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_123", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_124", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_125", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_126", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_127", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description     |
|:------:|:------:|:-------:|:-----------|:----------------|
|   31   |   rw   |   0x0   | filter_127 | For SPI_DEVICE3 |
|   30   |   rw   |   0x0   | filter_126 | For SPI_DEVICE3 |
|   29   |   rw   |   0x0   | filter_125 | For SPI_DEVICE3 |
|   28   |   rw   |   0x0   | filter_124 | For SPI_DEVICE3 |
|   27   |   rw   |   0x0   | filter_123 | For SPI_DEVICE3 |
|   26   |   rw   |   0x0   | filter_122 | For SPI_DEVICE3 |
|   25   |   rw   |   0x0   | filter_121 | For SPI_DEVICE3 |
|   24   |   rw   |   0x0   | filter_120 | For SPI_DEVICE3 |
|   23   |   rw   |   0x0   | filter_119 | For SPI_DEVICE3 |
|   22   |   rw   |   0x0   | filter_118 | For SPI_DEVICE3 |
|   21   |   rw   |   0x0   | filter_117 | For SPI_DEVICE3 |
|   20   |   rw   |   0x0   | filter_116 | For SPI_DEVICE3 |
|   19   |   rw   |   0x0   | filter_115 | For SPI_DEVICE3 |
|   18   |   rw   |   0x0   | filter_114 | For SPI_DEVICE3 |
|   17   |   rw   |   0x0   | filter_113 | For SPI_DEVICE3 |
|   16   |   rw   |   0x0   | filter_112 | For SPI_DEVICE3 |
|   15   |   rw   |   0x0   | filter_111 | For SPI_DEVICE3 |
|   14   |   rw   |   0x0   | filter_110 | For SPI_DEVICE3 |
|   13   |   rw   |   0x0   | filter_109 | For SPI_DEVICE3 |
|   12   |   rw   |   0x0   | filter_108 | For SPI_DEVICE3 |
|   11   |   rw   |   0x0   | filter_107 | For SPI_DEVICE3 |
|   10   |   rw   |   0x0   | filter_106 | For SPI_DEVICE3 |
|   9    |   rw   |   0x0   | filter_105 | For SPI_DEVICE3 |
|   8    |   rw   |   0x0   | filter_104 | For SPI_DEVICE3 |
|   7    |   rw   |   0x0   | filter_103 | For SPI_DEVICE3 |
|   6    |   rw   |   0x0   | filter_102 | For SPI_DEVICE3 |
|   5    |   rw   |   0x0   | filter_101 | For SPI_DEVICE3 |
|   4    |   rw   |   0x0   | filter_100 | For SPI_DEVICE3 |
|   3    |   rw   |   0x0   | filter_99  | For SPI_DEVICE3 |
|   2    |   rw   |   0x0   | filter_98  | For SPI_DEVICE3 |
|   1    |   rw   |   0x0   | filter_97  | For SPI_DEVICE3 |
|   0    |   rw   |   0x0   | filter_96  | For SPI_DEVICE3 |

## CMD_FILTER_4
Command Filter

If a bit in this CSR is 1, then corresponding SPI command w.r.t the
bit position among 256 bit is dropped in SPI Passthrough mode.
- Offset: `0x5c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "filter_128", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_129", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_130", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_131", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_132", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_133", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_134", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_135", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_136", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_137", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_138", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_139", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_140", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_141", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_142", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_143", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_144", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_145", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_146", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_147", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_148", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_149", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_150", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_151", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_152", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_153", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_154", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_155", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_156", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_157", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_158", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_159", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description     |
|:------:|:------:|:-------:|:-----------|:----------------|
|   31   |   rw   |   0x0   | filter_159 | For SPI_DEVICE4 |
|   30   |   rw   |   0x0   | filter_158 | For SPI_DEVICE4 |
|   29   |   rw   |   0x0   | filter_157 | For SPI_DEVICE4 |
|   28   |   rw   |   0x0   | filter_156 | For SPI_DEVICE4 |
|   27   |   rw   |   0x0   | filter_155 | For SPI_DEVICE4 |
|   26   |   rw   |   0x0   | filter_154 | For SPI_DEVICE4 |
|   25   |   rw   |   0x0   | filter_153 | For SPI_DEVICE4 |
|   24   |   rw   |   0x0   | filter_152 | For SPI_DEVICE4 |
|   23   |   rw   |   0x0   | filter_151 | For SPI_DEVICE4 |
|   22   |   rw   |   0x0   | filter_150 | For SPI_DEVICE4 |
|   21   |   rw   |   0x0   | filter_149 | For SPI_DEVICE4 |
|   20   |   rw   |   0x0   | filter_148 | For SPI_DEVICE4 |
|   19   |   rw   |   0x0   | filter_147 | For SPI_DEVICE4 |
|   18   |   rw   |   0x0   | filter_146 | For SPI_DEVICE4 |
|   17   |   rw   |   0x0   | filter_145 | For SPI_DEVICE4 |
|   16   |   rw   |   0x0   | filter_144 | For SPI_DEVICE4 |
|   15   |   rw   |   0x0   | filter_143 | For SPI_DEVICE4 |
|   14   |   rw   |   0x0   | filter_142 | For SPI_DEVICE4 |
|   13   |   rw   |   0x0   | filter_141 | For SPI_DEVICE4 |
|   12   |   rw   |   0x0   | filter_140 | For SPI_DEVICE4 |
|   11   |   rw   |   0x0   | filter_139 | For SPI_DEVICE4 |
|   10   |   rw   |   0x0   | filter_138 | For SPI_DEVICE4 |
|   9    |   rw   |   0x0   | filter_137 | For SPI_DEVICE4 |
|   8    |   rw   |   0x0   | filter_136 | For SPI_DEVICE4 |
|   7    |   rw   |   0x0   | filter_135 | For SPI_DEVICE4 |
|   6    |   rw   |   0x0   | filter_134 | For SPI_DEVICE4 |
|   5    |   rw   |   0x0   | filter_133 | For SPI_DEVICE4 |
|   4    |   rw   |   0x0   | filter_132 | For SPI_DEVICE4 |
|   3    |   rw   |   0x0   | filter_131 | For SPI_DEVICE4 |
|   2    |   rw   |   0x0   | filter_130 | For SPI_DEVICE4 |
|   1    |   rw   |   0x0   | filter_129 | For SPI_DEVICE4 |
|   0    |   rw   |   0x0   | filter_128 | For SPI_DEVICE4 |

## CMD_FILTER_5
Command Filter

If a bit in this CSR is 1, then corresponding SPI command w.r.t the
bit position among 256 bit is dropped in SPI Passthrough mode.
- Offset: `0x60`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "filter_160", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_161", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_162", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_163", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_164", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_165", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_166", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_167", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_168", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_169", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_170", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_171", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_172", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_173", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_174", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_175", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_176", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_177", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_178", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_179", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_180", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_181", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_182", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_183", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_184", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_185", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_186", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_187", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_188", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_189", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_190", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_191", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description     |
|:------:|:------:|:-------:|:-----------|:----------------|
|   31   |   rw   |   0x0   | filter_191 | For SPI_DEVICE5 |
|   30   |   rw   |   0x0   | filter_190 | For SPI_DEVICE5 |
|   29   |   rw   |   0x0   | filter_189 | For SPI_DEVICE5 |
|   28   |   rw   |   0x0   | filter_188 | For SPI_DEVICE5 |
|   27   |   rw   |   0x0   | filter_187 | For SPI_DEVICE5 |
|   26   |   rw   |   0x0   | filter_186 | For SPI_DEVICE5 |
|   25   |   rw   |   0x0   | filter_185 | For SPI_DEVICE5 |
|   24   |   rw   |   0x0   | filter_184 | For SPI_DEVICE5 |
|   23   |   rw   |   0x0   | filter_183 | For SPI_DEVICE5 |
|   22   |   rw   |   0x0   | filter_182 | For SPI_DEVICE5 |
|   21   |   rw   |   0x0   | filter_181 | For SPI_DEVICE5 |
|   20   |   rw   |   0x0   | filter_180 | For SPI_DEVICE5 |
|   19   |   rw   |   0x0   | filter_179 | For SPI_DEVICE5 |
|   18   |   rw   |   0x0   | filter_178 | For SPI_DEVICE5 |
|   17   |   rw   |   0x0   | filter_177 | For SPI_DEVICE5 |
|   16   |   rw   |   0x0   | filter_176 | For SPI_DEVICE5 |
|   15   |   rw   |   0x0   | filter_175 | For SPI_DEVICE5 |
|   14   |   rw   |   0x0   | filter_174 | For SPI_DEVICE5 |
|   13   |   rw   |   0x0   | filter_173 | For SPI_DEVICE5 |
|   12   |   rw   |   0x0   | filter_172 | For SPI_DEVICE5 |
|   11   |   rw   |   0x0   | filter_171 | For SPI_DEVICE5 |
|   10   |   rw   |   0x0   | filter_170 | For SPI_DEVICE5 |
|   9    |   rw   |   0x0   | filter_169 | For SPI_DEVICE5 |
|   8    |   rw   |   0x0   | filter_168 | For SPI_DEVICE5 |
|   7    |   rw   |   0x0   | filter_167 | For SPI_DEVICE5 |
|   6    |   rw   |   0x0   | filter_166 | For SPI_DEVICE5 |
|   5    |   rw   |   0x0   | filter_165 | For SPI_DEVICE5 |
|   4    |   rw   |   0x0   | filter_164 | For SPI_DEVICE5 |
|   3    |   rw   |   0x0   | filter_163 | For SPI_DEVICE5 |
|   2    |   rw   |   0x0   | filter_162 | For SPI_DEVICE5 |
|   1    |   rw   |   0x0   | filter_161 | For SPI_DEVICE5 |
|   0    |   rw   |   0x0   | filter_160 | For SPI_DEVICE5 |

## CMD_FILTER_6
Command Filter

If a bit in this CSR is 1, then corresponding SPI command w.r.t the
bit position among 256 bit is dropped in SPI Passthrough mode.
- Offset: `0x64`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "filter_192", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_193", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_194", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_195", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_196", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_197", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_198", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_199", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_200", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_201", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_202", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_203", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_204", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_205", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_206", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_207", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_208", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_209", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_210", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_211", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_212", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_213", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_214", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_215", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_216", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_217", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_218", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_219", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_220", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_221", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_222", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_223", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description     |
|:------:|:------:|:-------:|:-----------|:----------------|
|   31   |   rw   |   0x0   | filter_223 | For SPI_DEVICE6 |
|   30   |   rw   |   0x0   | filter_222 | For SPI_DEVICE6 |
|   29   |   rw   |   0x0   | filter_221 | For SPI_DEVICE6 |
|   28   |   rw   |   0x0   | filter_220 | For SPI_DEVICE6 |
|   27   |   rw   |   0x0   | filter_219 | For SPI_DEVICE6 |
|   26   |   rw   |   0x0   | filter_218 | For SPI_DEVICE6 |
|   25   |   rw   |   0x0   | filter_217 | For SPI_DEVICE6 |
|   24   |   rw   |   0x0   | filter_216 | For SPI_DEVICE6 |
|   23   |   rw   |   0x0   | filter_215 | For SPI_DEVICE6 |
|   22   |   rw   |   0x0   | filter_214 | For SPI_DEVICE6 |
|   21   |   rw   |   0x0   | filter_213 | For SPI_DEVICE6 |
|   20   |   rw   |   0x0   | filter_212 | For SPI_DEVICE6 |
|   19   |   rw   |   0x0   | filter_211 | For SPI_DEVICE6 |
|   18   |   rw   |   0x0   | filter_210 | For SPI_DEVICE6 |
|   17   |   rw   |   0x0   | filter_209 | For SPI_DEVICE6 |
|   16   |   rw   |   0x0   | filter_208 | For SPI_DEVICE6 |
|   15   |   rw   |   0x0   | filter_207 | For SPI_DEVICE6 |
|   14   |   rw   |   0x0   | filter_206 | For SPI_DEVICE6 |
|   13   |   rw   |   0x0   | filter_205 | For SPI_DEVICE6 |
|   12   |   rw   |   0x0   | filter_204 | For SPI_DEVICE6 |
|   11   |   rw   |   0x0   | filter_203 | For SPI_DEVICE6 |
|   10   |   rw   |   0x0   | filter_202 | For SPI_DEVICE6 |
|   9    |   rw   |   0x0   | filter_201 | For SPI_DEVICE6 |
|   8    |   rw   |   0x0   | filter_200 | For SPI_DEVICE6 |
|   7    |   rw   |   0x0   | filter_199 | For SPI_DEVICE6 |
|   6    |   rw   |   0x0   | filter_198 | For SPI_DEVICE6 |
|   5    |   rw   |   0x0   | filter_197 | For SPI_DEVICE6 |
|   4    |   rw   |   0x0   | filter_196 | For SPI_DEVICE6 |
|   3    |   rw   |   0x0   | filter_195 | For SPI_DEVICE6 |
|   2    |   rw   |   0x0   | filter_194 | For SPI_DEVICE6 |
|   1    |   rw   |   0x0   | filter_193 | For SPI_DEVICE6 |
|   0    |   rw   |   0x0   | filter_192 | For SPI_DEVICE6 |

## CMD_FILTER_7
Command Filter

If a bit in this CSR is 1, then corresponding SPI command w.r.t the
bit position among 256 bit is dropped in SPI Passthrough mode.
- Offset: `0x68`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "filter_224", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_225", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_226", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_227", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_228", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_229", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_230", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_231", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_232", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_233", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_234", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_235", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_236", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_237", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_238", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_239", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_240", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_241", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_242", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_243", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_244", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_245", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_246", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_247", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_248", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_249", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_250", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_251", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_252", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_253", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_254", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "filter_255", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description     |
|:------:|:------:|:-------:|:-----------|:----------------|
|   31   |   rw   |   0x0   | filter_255 | For SPI_DEVICE7 |
|   30   |   rw   |   0x0   | filter_254 | For SPI_DEVICE7 |
|   29   |   rw   |   0x0   | filter_253 | For SPI_DEVICE7 |
|   28   |   rw   |   0x0   | filter_252 | For SPI_DEVICE7 |
|   27   |   rw   |   0x0   | filter_251 | For SPI_DEVICE7 |
|   26   |   rw   |   0x0   | filter_250 | For SPI_DEVICE7 |
|   25   |   rw   |   0x0   | filter_249 | For SPI_DEVICE7 |
|   24   |   rw   |   0x0   | filter_248 | For SPI_DEVICE7 |
|   23   |   rw   |   0x0   | filter_247 | For SPI_DEVICE7 |
|   22   |   rw   |   0x0   | filter_246 | For SPI_DEVICE7 |
|   21   |   rw   |   0x0   | filter_245 | For SPI_DEVICE7 |
|   20   |   rw   |   0x0   | filter_244 | For SPI_DEVICE7 |
|   19   |   rw   |   0x0   | filter_243 | For SPI_DEVICE7 |
|   18   |   rw   |   0x0   | filter_242 | For SPI_DEVICE7 |
|   17   |   rw   |   0x0   | filter_241 | For SPI_DEVICE7 |
|   16   |   rw   |   0x0   | filter_240 | For SPI_DEVICE7 |
|   15   |   rw   |   0x0   | filter_239 | For SPI_DEVICE7 |
|   14   |   rw   |   0x0   | filter_238 | For SPI_DEVICE7 |
|   13   |   rw   |   0x0   | filter_237 | For SPI_DEVICE7 |
|   12   |   rw   |   0x0   | filter_236 | For SPI_DEVICE7 |
|   11   |   rw   |   0x0   | filter_235 | For SPI_DEVICE7 |
|   10   |   rw   |   0x0   | filter_234 | For SPI_DEVICE7 |
|   9    |   rw   |   0x0   | filter_233 | For SPI_DEVICE7 |
|   8    |   rw   |   0x0   | filter_232 | For SPI_DEVICE7 |
|   7    |   rw   |   0x0   | filter_231 | For SPI_DEVICE7 |
|   6    |   rw   |   0x0   | filter_230 | For SPI_DEVICE7 |
|   5    |   rw   |   0x0   | filter_229 | For SPI_DEVICE7 |
|   4    |   rw   |   0x0   | filter_228 | For SPI_DEVICE7 |
|   3    |   rw   |   0x0   | filter_227 | For SPI_DEVICE7 |
|   2    |   rw   |   0x0   | filter_226 | For SPI_DEVICE7 |
|   1    |   rw   |   0x0   | filter_225 | For SPI_DEVICE7 |
|   0    |   rw   |   0x0   | filter_224 | For SPI_DEVICE7 |

## ADDR_SWAP_MASK
Address Swap Mask register.

This register is used in the SPI passthrough mode. If any of bits in
this register is set, the corresponding address bit in the SPI Read
commands is replaced with the data from [`ADDR_SWAP_DATA.`](#addr_swap_data)

If 3B address mode is active, upper 8bit [31:24] is ignored.
- Offset: `0x6c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "mask", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                 |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | mask   | When a bit is 1, the SPI read address to the downstream SPI Flash device is swapped to [`ADDR_SWAP_DATA.`](#addr_swap_data) |

## ADDR_SWAP_DATA
The address value for the address swap feature.
- Offset: `0x70`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "data", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                            |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------------|
|  31:0  |   rw   |   0x0   | data   | Desired value to be swapped for the SPI read commands. |

## PAYLOAD_SWAP_MASK
Write Data Swap in the passthrough mode.

PAYLOAD_SWAP_MASK CSR provides the SW to change certain bits in the
first 4 bytes of the write payload in the passthrough mode.
- Offset: `0x74`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "mask", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:0  |   rw   |   0x0   | mask   | byte mask     |

## PAYLOAD_SWAP_DATA
Write Data Swap in the passthrough mode.

PAYLOAD_SWAP_DATA combined with PAYLOAD_SWAP_MASK provides the SW to
change certain bits in the first 4 bytes of the write payload in the
passthrough mode.

The register should be written in Little-Endian order. [7:0] bits are
processed in the first received payload byte. [31:24] bits for the 4th
byte.
- Offset: `0x78`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "data", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:0  |   rw   |   0x0   | data   | replaced data |

## CMD_INFO
Command Info register.

- Reset default: `0x7000`
- Reset mask: `0x83ffffff`

### Instances

| Name        | Offset   |
|:------------|:---------|
| CMD_INFO_0  | 0x7c     |
| CMD_INFO_1  | 0x80     |
| CMD_INFO_2  | 0x84     |
| CMD_INFO_3  | 0x88     |
| CMD_INFO_4  | 0x8c     |
| CMD_INFO_5  | 0x90     |
| CMD_INFO_6  | 0x94     |
| CMD_INFO_7  | 0x98     |
| CMD_INFO_8  | 0x9c     |
| CMD_INFO_9  | 0xa0     |
| CMD_INFO_10 | 0xa4     |
| CMD_INFO_11 | 0xa8     |
| CMD_INFO_12 | 0xac     |
| CMD_INFO_13 | 0xb0     |
| CMD_INFO_14 | 0xb4     |
| CMD_INFO_15 | 0xb8     |
| CMD_INFO_16 | 0xbc     |
| CMD_INFO_17 | 0xc0     |
| CMD_INFO_18 | 0xc4     |
| CMD_INFO_19 | 0xc8     |
| CMD_INFO_20 | 0xcc     |
| CMD_INFO_21 | 0xd0     |
| CMD_INFO_22 | 0xd4     |
| CMD_INFO_23 | 0xd8     |


### Fields

```wavejson
{"reg": [{"name": "opcode", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "addr_mode", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "addr_swap_en", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "mbyte_en", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "dummy_size", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "dummy_en", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "payload_en", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "payload_dir", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "payload_swap_en", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "read_pipeline_mode", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "upload", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "busy", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 5}, {"name": "valid", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name                                                |
|:------:|:------:|:-------:|:----------------------------------------------------|
|   31   |   rw   |   0x0   | [valid](#cmd_info--valid)                           |
| 30:26  |        |         | Reserved                                            |
|   25   |   rw   |   0x0   | [busy](#cmd_info--busy)                             |
|   24   |   rw   |   0x0   | [upload](#cmd_info--upload)                         |
| 23:22  |   rw   |   0x0   | [read_pipeline_mode](#cmd_info--read_pipeline_mode) |
|   21   |   rw   |   0x0   | [payload_swap_en](#cmd_info--payload_swap_en)       |
|   20   |   rw   |   0x0   | [payload_dir](#cmd_info--payload_dir)               |
| 19:16  |   rw   |   0x0   | [payload_en](#cmd_info--payload_en)                 |
|   15   |   rw   |   0x0   | [dummy_en](#cmd_info--dummy_en)                     |
| 14:12  |   rw   |   0x7   | [dummy_size](#cmd_info--dummy_size)                 |
|   11   |   rw   |   0x0   | [mbyte_en](#cmd_info--mbyte_en)                     |
|   10   |   rw   |   0x0   | [addr_swap_en](#cmd_info--addr_swap_en)             |
|  9:8   |   rw   |   0x0   | [addr_mode](#cmd_info--addr_mode)                   |
|  7:0   |   rw   |   0x0   | [opcode](#cmd_info--opcode)                         |

### CMD_INFO . valid
Set to 1 if the config in the register is valid

### CMD_INFO . busy
Set to 1 to set the BUSY bit in the FLASH_STATUS when the
command is received.  This bit is active only when `upload` bit is
set.

### CMD_INFO . upload
Set to 1 to upload the command.

If upload field in the command info entry is set, the cmdparse
activates the upload submodule when the opcode is received.
`addr_en`, `addr_4B_affected`, and `addr_4b_forced` (TBD) affect
the upload functionality. The three address related configs
defines the command address field size.

The logic assumes the following SPI input stream as payload,
which max size is 256B. If the command exceeds the maximum
payload size 256B, the logic wraps the payload and overwrites.

### CMD_INFO . read_pipeline_mode
Add 2-stage pipeline to read payload.

If `read_pipeline_mode` is not set to `zero_stages`, the read logic adds a 2-stage pipeline to the read data for this command.
This read pipeline enables higher throughput for certain read commands in passthrough mode.

`payload_dir` must be set to PayloadOut: `payload_pipeline_en` only works with read data.
It may be used with any IO mode, but general host compatibility is likely limited to Quad Read.
If this pipeline is used for passthrough, the internal SFDP should report 2 additional dummy cycles compared to the downstream flash.
SFDP read commands should be processed internally, and `dummy_size` should still reflect the downstream device's dummy cycle count.

| Value   | Name                  | Description                                                                                                                                                                                                                                                                                                                                                                       |
|:--------|:----------------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0x0     | zero_stages           | Bypass the 2-stage read pipeline. This mode is for ordinary SPI flash operation. Passthrough read data flows combinatorially from input pads to output pads.                                                                                                                                                                                                                      |
| 0x1     | two_stages_half_cycle | 2-stage read pipeline with half-cycle sampling. In this mode, the 2-stage read pipeline is enabled. Read data appears 2 cycles later than the `zero_stages` option. In addition, read data originating from the downstream flash is first sampled on the normal sampling edge for half-cycle sampling.                                                                            |
| 0x2     | two_stages_full_cycle | 2-stage read pipeline with full-cycle sampling. In this mode, the 2-stage read pipeline is enabled. Read data appears 2 cycles later than the `zero_stages` option. In addition, read data originating from the downstream flash is first sampled on the next launch edge. In other words, the internal pipeline performs full-cycle sampling of the downstream flash's response. |

Other values are reserved.

### CMD_INFO . payload_swap_en
Swap the first byte of the write payload.

If `payload_swap_en` is set, the passthrough logic swaps the first byte of the write payload with DATA_SWAP CSR.

`payload_swap_en` only works with write data and SingleIO mode. `payload_en` must be 4'b 0001 and `paylod_dir` to be PayloadIn.

### CMD_INFO . payload_dir
Set to 1 if the command returns data. If 0, the payload
sends to the downstream Flash device.

| Value   | Name       | Description                                  |
|:--------|:-----------|:---------------------------------------------|
| 0x0     | PayloadIn  | From host to the downstream flash device     |
| 0x1     | PayloadOut | From the downstream flash device to the host |


### CMD_INFO . payload_en
Payload Enable per SPI lane.

Set to non-zero if the command has payload at the end of the
protocol. This field has four bits. Each bit represents the SPI
line. If a command is a Single IO command and returns data to the
host system, the data is returned on the MISO line (IO[1]). In
this case, SW sets payload_en to 4'b 0010.

### CMD_INFO . dummy_en
Set to 1 if the command has a dummy cycle following the address field.

### CMD_INFO . dummy_size
The number of dummy cycles -1 for the command

### CMD_INFO . mbyte_en
If 1, the command has a MByte field following the
address field. This is set to 1 for DualIO, QuadIO commands.

### CMD_INFO . addr_swap_en
This field is used in the passthrough logic.
If this field is set to 1, the address in the passthrough command
is replaced to the preconfigured value.

### CMD_INFO . addr_mode
Command address mode

A command can have four modes:

- 0: Command does not have an address field
- 1: CFG.addr_4b_en decides the address size (3B/4B)
- 2: Address size is always 3B regardless of CFG.addr_4b_en
- 3: Address size is always 4B regardless of CFG.addr_4b_en

| Value   | Name         | Description                                |
|:--------|:-------------|:-------------------------------------------|
| 0x0     | AddrDisabled | Address field does not exist               |
| 0x1     | AddrCfg      | CFG.addr_4b_en determines the address size |
| 0x2     | Addr3B       | Address size in the command is always 3B.  |
| 0x3     | Addr4B       | Address size in the command is always 4B.  |


### CMD_INFO . opcode
Command Opcode

## CMD_INFO_EN4B
Opcode for EN4B.

If the register is active, it affects in flash / passthrough modes.
- Offset: `0xdc`
- Reset default: `0x0`
- Reset mask: `0x800000ff`

### Fields

```wavejson
{"reg": [{"name": "opcode", "bits": 8, "attr": ["rw"], "rotate": 0}, {"bits": 23}, {"name": "valid", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description          |
|:------:|:------:|:-------:|:-------|:---------------------|
|   31   |   rw   |   0x0   | valid  | If 1, Opcode affects |
|  30:8  |        |         |        | Reserved             |
|  7:0   |   rw   |   0x0   | opcode | EN4B opcode          |

## CMD_INFO_EX4B
Opcode for EX4B
- Offset: `0xe0`
- Reset default: `0x0`
- Reset mask: `0x800000ff`

### Fields

```wavejson
{"reg": [{"name": "opcode", "bits": 8, "attr": ["rw"], "rotate": 0}, {"bits": 23}, {"name": "valid", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description          |
|:------:|:------:|:-------:|:-------|:---------------------|
|   31   |   rw   |   0x0   | valid  | If 1, Opcode affects |
|  30:8  |        |         |        | Reserved             |
|  7:0   |   rw   |   0x0   | opcode | EX4B opcode          |

## CMD_INFO_WREN
Opcode for Write Enable (WREN)
- Offset: `0xe4`
- Reset default: `0x0`
- Reset mask: `0x800000ff`

### Fields

```wavejson
{"reg": [{"name": "opcode", "bits": 8, "attr": ["rw"], "rotate": 0}, {"bits": 23}, {"name": "valid", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description          |
|:------:|:------:|:-------:|:-------|:---------------------|
|   31   |   rw   |   0x0   | valid  | If 1, opcode affects |
|  30:8  |        |         |        | Reserved             |
|  7:0   |   rw   |   0x0   | opcode | WREN opcode          |

## CMD_INFO_WRDI
Opcode for Write Disable (WRDI)
- Offset: `0xe8`
- Reset default: `0x0`
- Reset mask: `0x800000ff`

### Fields

```wavejson
{"reg": [{"name": "opcode", "bits": 8, "attr": ["rw"], "rotate": 0}, {"bits": 23}, {"name": "valid", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description          |
|:------:|:------:|:-------:|:-------|:---------------------|
|   31   |   rw   |   0x0   | valid  | If 1, opcode affects |
|  30:8  |        |         |        | Reserved             |
|  7:0   |   rw   |   0x0   | opcode | WRDI opcode          |

## TPM_CAP
TPM HWIP Capability register.

This register shows the features the current TPM HWIP supports.
- Offset: `0x800`
- Reset default: `0x660100`
- Reset mask: `0x7701ff`

### Fields

```wavejson
{"reg": [{"name": "rev", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "locality", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 7}, {"name": "max_wr_size", "bits": 3, "attr": ["ro"], "rotate": -90}, {"bits": 1}, {"name": "max_rd_size", "bits": 3, "attr": ["ro"], "rotate": -90}, {"bits": 9}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name                                 |
|:------:|:------:|:-------:|:-------------------------------------|
| 31:23  |        |         | Reserved                             |
| 22:20  |   ro   |   0x6   | [max_rd_size](#tpm_cap--max_rd_size) |
|   19   |        |         | Reserved                             |
| 18:16  |   ro   |   0x6   | [max_wr_size](#tpm_cap--max_wr_size) |
|  15:9  |        |         | Reserved                             |
|   8    |   ro   |   0x1   | [locality](#tpm_cap--locality)       |
|  7:0   |   ro   |   0x0   | [rev](#tpm_cap--rev)                 |

### TPM_CAP . max_rd_size
The maximum read size in bytes the TPM submodule supports.
The value is the exponent of the 2.

- 3'b 010: Support up to 4B
- 3'b 011: Support up to 8B
- 3'b 100: Support up to 16B
- 3'b 101: Support up to 32B
- 3'b 110: Support up to 64B

All other values are reserved.

It is not recommended for SW to advertise TPM supporting more than `max_rd_size` to the South Bridge.

### TPM_CAP . max_wr_size
The maximum write size in bytes the TPM submodule supports.
The value is the exponent of the 2.

- 3'b 010: Support up to 4B
- 3'b 011: Support up to 8B
- 3'b 100: Support up to 16B
- 3'b 101: Support up to 32B
- 3'b 110: Support up to 64B

All other values are reserved.

It is not recommended for SW to advertise TPM supporting more than `max_wr_size` to the South Bridge.

### TPM_CAP . locality
If 1, the TPM submodule supports 5 Locality.
If 0, only one Locality is provided

### TPM_CAP . rev
Revision of the TPM submodule

## TPM_CFG
TPM Configuration register.
- Offset: `0x804`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "en", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "tpm_mode", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "hw_reg_dis", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "tpm_reg_chk_dis", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "invalid_locality", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name                                           |
|:------:|:------:|:-------:|:-----------------------------------------------|
|  31:5  |        |         | Reserved                                       |
|   4    |   rw   |   0x0   | [invalid_locality](#tpm_cfg--invalid_locality) |
|   3    |   rw   |   0x0   | [tpm_reg_chk_dis](#tpm_cfg--tpm_reg_chk_dis)   |
|   2    |   rw   |   0x0   | [hw_reg_dis](#tpm_cfg--hw_reg_dis)             |
|   1    |   rw   |   0x0   | [tpm_mode](#tpm_cfg--tpm_mode)                 |
|   0    |   rw   |   0x0   | [en](#tpm_cfg--en)                             |

### TPM_CFG . invalid_locality
If 1, TPM submodule returns the invalid data (0xFF) for the
out of the max Locality request.
If it is a write request, HW still uploads the command and address.
SW needs to process the incoming invalid command.

If 0, TPM submodule uploads the TPM command and address. The SW may
write 0xFF to the read FIFO.

Note: The TPM submodule uploads the TPM commands that do not fall
into the FIFO registers (0xD4_XXXX) regardless of
`invalid_locality` bit.

### TPM_CFG . tpm_reg_chk_dis
If 1, the logic does not compare the upper 8 bit of the
received address with the TpmAddr constant, D4h.

If this field is 0, the HW uploads the command, address, and write
payload to the buffers in case of address that is not 0xD4_XXXX.

### TPM_CFG . hw_reg_dis
If 0, TPM submodule directly returns the return-by-HW registers for the read requests.

If 1, TPM submodule uploads the TPM command regardless of the address, and the SW may return the value through the read FIFO.

### TPM_CFG . tpm_mode
Configure the TPM mode. 1 for CRB, 0 for FIFO.

If the SW set this field to 1, the HW logic always pushes the
command/addr and write data to buffers. The logic does not compare
the incoming address to the list of managed-by-HW register
addresses.

The invalid locality check still runs based on the invalid_locality
configuration.

### TPM_CFG . en
If 1, TPM submodule accepts the transactions over SPI

## TPM_STATUS
TPM submodule state register.

The TPM_STATUS CSR provides the current TPM status, mostly the buffer and FIFO status.
- Offset: `0x808`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "cmdaddr_notempty", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "wrfifo_pending", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"name": "rdfifo_aborted", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name                                              |
|:------:|:------:|:-------:|:--------------------------------------------------|
|  31:3  |        |         | Reserved                                          |
|   2    |   ro   |    x    | [rdfifo_aborted](#tpm_status--rdfifo_aborted)     |
|   1    |  rw0c  |    x    | [wrfifo_pending](#tpm_status--wrfifo_pending)     |
|   0    |   ro   |    x    | [cmdaddr_notempty](#tpm_status--cmdaddr_notempty) |

### TPM_STATUS . rdfifo_aborted
If 1, the last Read FIFO command was aborted.

This bit becomes 1 when a Read FIFO command became active, but the transaction did not complete.
An aborted transaction occurs when the host de-asserts CSB without clocking all the requested data.
This bit remains 1 until reset, or it will clear automatically after the next valid command is read from TPM_CMD_ADDR.

### TPM_STATUS . wrfifo_pending
If 1, the Write FIFO is reserved for software processing.

This bit becomes 1 when a complete write command is received.
While it remains 1, subsequent write commands will block at the wait state until it is cleared.
Write 0 to release the Write FIFO back to the TPM module.

### TPM_STATUS . cmdaddr_notempty
If 1, the TPM_CMD_ADDR has a valid data. This status is reported via the interrupt also.

## TPM_ACCESS_0
TPM_ACCESS_x register.
- Offset: `0x80c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "access_0", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "access_1", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "access_2", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "access_3", "bits": 8, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description   |
|:------:|:------:|:-------:|:---------|:--------------|
| 31:24  |   rw   |   0x0   | access_3 | TPM_ACCESS    |
| 23:16  |   rw   |   0x0   | access_2 | TPM_ACCESS    |
|  15:8  |   rw   |   0x0   | access_1 | TPM_ACCESS    |
|  7:0   |   rw   |   0x0   | access_0 | TPM_ACCESS    |

## TPM_ACCESS_1
TPM_ACCESS_x register.
- Offset: `0x810`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "access_4", "bits": 8, "attr": ["rw"], "rotate": 0}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description   |
|:------:|:------:|:-------:|:---------|:--------------|
|  31:8  |        |         |          | Reserved      |
|  7:0   |   rw   |   0x0   | access_4 | For TPM1      |

## TPM_STS
TPM_STS_x register.

The register is mirrored to all Localities.
The value is returned to the host system only when the activeLocality
in the TPM_ACCESS_x is matched to the current received Locality.
- Offset: `0x814`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "sts", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:0  |   rw   |   0x0   | sts    | TPM_STS_x     |

## TPM_INTF_CAPABILITY
TPM_INTF_CAPABILITY
- Offset: `0x818`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "intf_capability", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name            | Description         |
|:------:|:------:|:-------:|:----------------|:--------------------|
|  31:0  |   rw   |   0x0   | intf_capability | TPM_INTF_CAPABILITY |

## TPM_INT_ENABLE
TPM_INT_ENABLE
- Offset: `0x81c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "int_enable", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description    |
|:------:|:------:|:-------:|:-----------|:---------------|
|  31:0  |   rw   |   0x0   | int_enable | TPM_INT_ENABLE |

## TPM_INT_VECTOR
TPM_INT_VECTOR
- Offset: `0x820`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "int_vector", "bits": 8, "attr": ["rw"], "rotate": 0}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description    |
|:------:|:------:|:-------:|:-----------|:---------------|
|  31:8  |        |         |            | Reserved       |
|  7:0   |   rw   |   0x0   | int_vector | TPM_INT_VECTOR |

## TPM_INT_STATUS
TPM_INT_STATUS
- Offset: `0x824`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "int_status", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description    |
|:------:|:------:|:-------:|:-----------|:---------------|
|  31:0  |   rw   |   0x0   | int_status | TPM_INT_STATUS |

## TPM_DID_VID
TPM_DID/ TPM_VID register
- Offset: `0x828`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "vid", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "did", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
| 31:16  |   rw   |   0x0   | did    | TPM_DID       |
|  15:0  |   rw   |   0x0   | vid    | TPM_VID       |

## TPM_RID
TPM_RID
- Offset: `0x82c`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "rid", "bits": 8, "attr": ["rw"], "rotate": 0}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:8  |        |         |        | Reserved      |
|  7:0   |   rw   |   0x0   | rid    | TPM_RID       |

## TPM_CMD_ADDR
TPM Command and Address buffer

The SW may get the received TPM command and address by readin gthis CSR.
- Offset: `0x830`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "addr", "bits": 24, "attr": ["ro"], "rotate": 0}, {"name": "cmd", "bits": 8, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description      |
|:------:|:------:|:-------:|:-------|:-----------------|
| 31:24  |   ro   |    x    | cmd    | received command |
|  23:0  |   ro   |    x    | addr   | received address |

## TPM_READ_FIFO
TPM Read command return data FIFO.

The write port of the read command FIFO.
- Offset: `0x834`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "value", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                 |
|:------:|:------:|:-------:|:-------|:----------------------------|
|  31:0  |   wo   |    x    | value  | write port of the read FIFO |

## egress_buffer
SPI internal egress buffer.

The lower 2 kB is for Read content emulating eFlash.
The next 1 kB is for the Mailbox buffer.
Then the next 256 B is for the SFDP buffer.
Finally, the buffer spaces end with a 64 B TPM Read FIFO.

- Word Aligned Offset Range: `0x1000`to`0x1d3c`
- Size (words): `848`
- Access: `wo`
- Byte writes are *not* supported.

## ingress_buffer
SPI internal ingress buffer.

The layout is as follows (starting from offset 0):
- 256 B SFDP buffer
- 32 B CmdFIFO
- 32 B AddrFIFO
- 256 B payload FIFO
- 64 B TPM Write FIFO

- Word Aligned Offset Range: `0x1e00`to`0x1fbc`
- Size (words): `112`
- Access: `ro`
- Byte writes are *not* supported.


<!-- END CMDGEN -->
