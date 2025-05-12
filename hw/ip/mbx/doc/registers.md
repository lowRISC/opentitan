# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/mbx/data/mbx.hjson -->
## Summary of the **`core`** interface's registers

| Name                                                    | Offset   |   Length | Description                                                                                                               |
|:--------------------------------------------------------|:---------|---------:|:--------------------------------------------------------------------------------------------------------------------------|
| mbx.[`INTR_STATE`](#intr_state)                         | 0x0      |        4 | Interrupt State Register                                                                                                  |
| mbx.[`INTR_ENABLE`](#intr_enable)                       | 0x4      |        4 | Interrupt Enable Register                                                                                                 |
| mbx.[`INTR_TEST`](#intr_test)                           | 0x8      |        4 | Interrupt Test Register                                                                                                   |
| mbx.[`ALERT_TEST`](#alert_test)                         | 0xc      |        4 | Alert Test Register                                                                                                       |
| mbx.[`CONTROL`](#control)                               | 0x10     |        4 | DOE mailbox control register visible to OpenTitan                                                                         |
| mbx.[`STATUS`](#status)                                 | 0x14     |        4 | DOE mailbox status register visible to OpenTitan                                                                          |
| mbx.[`ADDRESS_RANGE_REGWEN`](#address_range_regwen)     | 0x18     |        4 | Used to lock the inbound/outbound base/limit configuration registers.                                                     |
| mbx.[`ADDRESS_RANGE_VALID`](#address_range_valid)       | 0x1c     |        4 | Used to mark the inbound/outbound base/limit configuration registers to have a valid configuration.                       |
| mbx.[`INBOUND_BASE_ADDRESS`](#inbound_base_address)     | 0x20     |        4 | Base address of SRAM region, which is used to back up the inbound mailbox data.                                           |
| mbx.[`INBOUND_LIMIT_ADDRESS`](#inbound_limit_address)   | 0x24     |        4 | Inclusive end address of the inbound mailbox memory range in the private SRAM.                                            |
| mbx.[`INBOUND_WRITE_PTR`](#inbound_write_ptr)           | 0x28     |        4 | Write pointer for the next inbound DWORD write (32 bits).                                                                 |
| mbx.[`OUTBOUND_BASE_ADDRESS`](#outbound_base_address)   | 0x2c     |        4 | Base address of SRAM region, which is used to buffer the outbound mailbox data.                                           |
| mbx.[`OUTBOUND_LIMIT_ADDRESS`](#outbound_limit_address) | 0x30     |        4 | Inclusive end address of the outbound mailbox memory range in the private SRAM.                                           |
| mbx.[`OUTBOUND_READ_PTR`](#outbound_read_ptr)           | 0x34     |        4 | Read pointer for the next outbound DWORD read.                                                                            |
| mbx.[`OUTBOUND_OBJECT_SIZE`](#outbound_object_size)     | 0x38     |        4 | Indicates the size of the data object to be transferred out.                                                              |
| mbx.[`DOE_INTR_MSG_ADDR`](#doe_intr_msg_addr)           | 0x3c     |        4 | Software read-only alias of the DOE_INTR_MSG_ADDR register of the SoC interface for convenient access of the OT firmware. |
| mbx.[`DOE_INTR_MSG_DATA`](#doe_intr_msg_data)           | 0x40     |        4 | Software read-only alias of the DOE_INTR_MSG_DATA register of the SoC interface for convenient access of the OT firmware. |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "mbx_ready", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "mbx_abort", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "mbx_error", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                       |
|:------:|:------:|:-------:|:----------|:--------------------------------------------------|
|  31:3  |        |         |           | Reserved                                          |
|   2    |  rw1c  |   0x0   | mbx_error | The mailbox instance generated an error.          |
|   1    |  rw1c  |   0x0   | mbx_abort | An abort request was received from the requester. |
|   0    |  rw1c  |   0x0   | mbx_ready | A new object was received in the inbound mailbox. |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "mbx_ready", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "mbx_abort", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "mbx_error", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                         |
|:------:|:------:|:-------:|:----------|:--------------------------------------------------------------------|
|  31:3  |        |         |           | Reserved                                                            |
|   2    |   rw   |   0x0   | mbx_error | Enable interrupt when [`INTR_STATE.mbx_error`](#intr_state) is set. |
|   1    |   rw   |   0x0   | mbx_abort | Enable interrupt when [`INTR_STATE.mbx_abort`](#intr_state) is set. |
|   0    |   rw   |   0x0   | mbx_ready | Enable interrupt when [`INTR_STATE.mbx_ready`](#intr_state) is set. |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "mbx_ready", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "mbx_abort", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "mbx_error", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                  |
|:------:|:------:|:-------:|:----------|:-------------------------------------------------------------|
|  31:3  |        |         |           | Reserved                                                     |
|   2    |   wo   |   0x0   | mbx_error | Write 1 to force [`INTR_STATE.mbx_error`](#intr_state) to 1. |
|   1    |   wo   |   0x0   | mbx_abort | Write 1 to force [`INTR_STATE.mbx_abort`](#intr_state) to 1. |
|   0    |   wo   |   0x0   | mbx_ready | Write 1 to force [`INTR_STATE.mbx_ready`](#intr_state) to 1. |

## ALERT_TEST
Alert Test Register
- Offset: `0xc`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "fatal_fault", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "recov_fault", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                      |
|:------:|:------:|:-------:|:------------|:-------------------------------------------------|
|  31:2  |        |         |             | Reserved                                         |
|   1    |   wo   |   0x0   | recov_fault | Write 1 to trigger one alert event of this kind. |
|   0    |   wo   |   0x0   | fatal_fault | Write 1 to trigger one alert event of this kind. |

## CONTROL
DOE mailbox control register visible to OpenTitan
- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0xb`

### Fields

```wavejson
{"reg": [{"name": "abort", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "error", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 1}, {"name": "sys_async_msg", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                                                                                                                                                                     |
|:------:|:------:|:-------:|:--------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:4  |        |         |               | Reserved                                                                                                                                                                                                        |
|   3    |   wo   |   0x0   | sys_async_msg | Indicates an async message request                                                                                                                                                                              |
|   2    |        |         |               | Reserved                                                                                                                                                                                                        |
|   1    |   rw   |   0x0   | error         | Set by firmware to signal an error, e.g. unable to provide a response to request. Set by hardware, on SYS.WDATA or SYS.RDATA performing an invalid access. Cleared by the hardware when SYS sets CONTROL.ABORT. |
|   0    |   rw   |   0x0   | abort         | Alias of the DoE mailbox abort bit                                                                                                                                                                              |

## STATUS
DOE mailbox status register visible to OpenTitan
- Offset: `0x14`
- Reset default: `0x1`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "busy", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "sys_intr_state", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "sys_intr_enable", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "sys_async_enable", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                               |
|:------:|:------:|:-------:|:-----------------|:----------------------------------------------------------|
|  31:4  |        |         |                  | Reserved                                                  |
|   3    |   ro   |   0x0   | sys_async_enable | Alias of the DoE mailbox async message support enable bit |
|   2    |   ro   |   0x0   | sys_intr_enable  | Alias of the DoE mailbox interrupt enable bit             |
|   1    |   ro   |   0x0   | sys_intr_state   | Alias of the DoE mailbox interrupt status bit             |
|   0    |   ro   |   0x1   | busy             | Alias of the DoE mailbox busy bit                         |

## ADDRESS_RANGE_REGWEN
Used to lock the inbound/outbound base/limit configuration registers.
- Offset: `0x18`
- Reset default: `0x6`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "regwen", "bits": 4, "attr": ["rw0c"], "rotate": 0}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                  |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:4  |        |         |        | Reserved                                                                                                                                                     |
|  3:0   |  rw0c  |   0x6   | regwen | Once cleared the mailbox inbound/outbound base/limit registers will be locked until the next reset. Default Value = kMultiBitBool4True -> Unlocked at reset. |

## ADDRESS_RANGE_VALID
Used to mark the inbound/outbound base/limit configuration registers to have a valid configuration.
- Offset: `0x1c`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "range_valid", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                           |
|:------:|:------:|:-------:|:------------|:----------------------------------------------------------------------|
|  31:1  |        |         |             | Reserved                                                              |
|   0    |   rw   |   0x0   | range_valid | Once set the mailbox inbound/outbound base/limit registers are valid. |

## INBOUND_BASE_ADDRESS
Base address of SRAM region, which is used to back up the inbound mailbox data.
This address is 4-byte aligned, the lower 2 bits are ignored.
- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0xfffffffc`
- Register enable: [`ADDRESS_RANGE_REGWEN`](#address_range_regwen)

### Fields

```wavejson
{"reg": [{"bits": 2}, {"name": "base_address", "bits": 30, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                                                     |
|:------:|:------:|:-------:|:-------------|:--------------------------------------------------------------------------------|
|  31:2  |   rw   |   0x0   | base_address | Base address of SRAM region, which is used to back up the inbound mailbox data. |
|  1:0   |        |         |              | Reserved                                                                        |

## INBOUND_LIMIT_ADDRESS
Inclusive end address of the inbound mailbox memory range in the private SRAM.
This address is 4-byte aligned and it specifies the start address of the final valid
DWORD location. The lower 2 bits are ignored.
- Offset: `0x24`
- Reset default: `0x0`
- Reset mask: `0xfffffffc`
- Register enable: [`ADDRESS_RANGE_REGWEN`](#address_range_regwen)

### Fields

```wavejson
{"reg": [{"bits": 2}, {"name": "limit", "bits": 30, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                            |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------------|
|  31:2  |   rw   |   0x0   | limit  | Limit Address to mark the end of the inbound mailbox memory range in the private SRAM. |
|  1:0   |        |         |        | Reserved                                                                               |

## INBOUND_WRITE_PTR
Write pointer for the next inbound DWORD write (32 bits).
Pointer is initialized to the Inbox memory base address before the start of a transfer.
Inbox handler maintains the updated pointer as data DWORDs are received by the DOE inbox.
This pointer is 4-byte aligned; the lower 2 bits are always zero.
- Offset: `0x28`
- Reset default: `0x0`
- Reset mask: `0xfffffffc`

### Fields

```wavejson
{"reg": [{"bits": 2}, {"name": "inbound_write_ptr", "bits": 30, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                                    |
|:------:|:------:|:-------:|:------------------|:-----------------------------------------------|
|  31:2  |   ro   |   0x0   | inbound_write_ptr | Write pointer for the next inbound data write. |
|  1:0   |        |         |                   | Reserved                                       |

## OUTBOUND_BASE_ADDRESS
Base address of SRAM region, which is used to buffer the outbound mailbox data.
This address is 4-byte aligned, the lower 2 bits are ignored.
- Offset: `0x2c`
- Reset default: `0x0`
- Reset mask: `0xfffffffc`
- Register enable: [`ADDRESS_RANGE_REGWEN`](#address_range_regwen)

### Fields

```wavejson
{"reg": [{"bits": 2}, {"name": "base_address", "bits": 30, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                                                     |
|:------:|:------:|:-------:|:-------------|:--------------------------------------------------------------------------------|
|  31:2  |   rw   |   0x0   | base_address | Base address of SRAM region, which is used to buffer the outbound mailbox data. |
|  1:0   |        |         |              | Reserved                                                                        |

## OUTBOUND_LIMIT_ADDRESS
Inclusive end address of the outbound mailbox memory range in the private SRAM.
This address is 4-byte aligned and it specifies the start address of the final valid
DWORD location. The lower 2 bits are ignored.
- Offset: `0x30`
- Reset default: `0x0`
- Reset mask: `0xfffffffc`
- Register enable: [`ADDRESS_RANGE_REGWEN`](#address_range_regwen)

### Fields

```wavejson
{"reg": [{"bits": 2}, {"name": "limit", "bits": 30, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                             |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------|
|  31:2  |   rw   |   0x0   | limit  | Limit Address to mark the end of the outbound mailbox memory range in the private SRAM. |
|  1:0   |        |         |        | Reserved                                                                                |

## OUTBOUND_READ_PTR
Read pointer for the next outbound DWORD read.
Pointer is initialized to the Outbox memory base address before the start of an outgoing
object transfer. Outbox handler maintains the updated pointer as data DWORDs are read
from the DOE instance by the requester.
This pointer is 4-byte aligned; the lower 2 bits are always zero.
- Offset: `0x34`
- Reset default: `0x0`
- Reset mask: `0xfffffffc`

### Fields

```wavejson
{"reg": [{"bits": 2}, {"name": "outbound_read_ptr", "bits": 30, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                                   |
|:------:|:------:|:-------:|:------------------|:----------------------------------------------|
|  31:2  |   ro   |   0x0   | outbound_read_ptr | Read pointer for the next outbound data read. |
|  1:0   |        |         |                   | Reserved                                      |

## OUTBOUND_OBJECT_SIZE
Indicates the size of the data object to be transferred out.
Note that this size specifies the number of DWORDs (32 bits).
Maximum size supported by any OT DOE instance is 1024 DWORDs.
- Offset: `0x38`
- Reset default: `0x0`
- Reset mask: `0x7ff`

### Fields

```wavejson
{"reg": [{"name": "cnt", "bits": 11, "attr": ["rw"], "rotate": 0}, {"bits": 21}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                  |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------|
| 31:11  |        |         |        | Reserved                                                                     |
|  10:0  |   rw   |   0x0   | cnt    | Indicates the size of the data object to be transferred out in 4-byte words. |

## DOE_INTR_MSG_ADDR
Software read-only alias of the DOE_INTR_MSG_ADDR register of the SoC interface for convenient access of the OT firmware.
Defined only for FW-to-FW mailboxes.
- Offset: `0x3c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "doe_intr_msg_addr", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                                                                                                            |
|:------:|:------:|:-------:|:------------------|:-----------------------------------------------------------------------------------------------------------------------|
|  31:0  |   ro   |   0x0   | doe_intr_msg_addr | Utilized by the mailbox responder to send an interrupt message to the requester via a write to the configured address. |

## DOE_INTR_MSG_DATA
Software read-only alias of the DOE_INTR_MSG_DATA register of the SoC interface for convenient access of the OT firmware.
Defined only for FW-to-FW mailboxes.
- Offset: `0x40`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "doe_intr_msg_data", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                                                                                    |
|:------:|:------:|:-------:|:------------------|:-----------------------------------------------------------------------------------------------|
|  31:0  |   ro   |   0x0   | doe_intr_msg_data | Interrupt message data to be sent to the address configured in the DOE_INTR_MSG_ADDR register. |

## Summary of the **`soc`** interface's registers

| Name                                                  | Offset   |   Length | Description                                                                                                            |
|:------------------------------------------------------|:---------|---------:|:-----------------------------------------------------------------------------------------------------------------------|
| mbx.[`SOC_CONTROL`](#soc_control)                     | 0x8      |        4 | DOE mailbox control register.                                                                                          |
| mbx.[`SOC_STATUS`](#soc_status)                       | 0xc      |        4 | DOE mailbox status register                                                                                            |
| mbx.[`WDATA`](#wdata)                                 | 0x10     |        4 | DOE mailbox write data register.                                                                                       |
| mbx.[`RDATA`](#rdata)                                 | 0x14     |        4 | DOE mailbox read data register                                                                                         |
| mbx.[`SOC_DOE_INTR_MSG_ADDR`](#soc_doe_intr_msg_addr) | 0x18     |        4 | Utilized by the mailbox responder to send an interrupt message to the requester via a write to the configured address. |
| mbx.[`SOC_DOE_INTR_MSG_DATA`](#soc_doe_intr_msg_data) | 0x1c     |        4 | Interrupt message data to be sent to the address configured in the DOE_INTR_MSG_ADDR register.                         |

## SOC_CONTROL
DOE mailbox control register.
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x8000000b`

### Fields

```wavejson
{"reg": [{"name": "abort", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "doe_intr_en", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 1}, {"name": "doe_async_msg_en", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}, {"name": "go", "bits": 1, "attr": ["wo"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                                                                                                                                                                                                            |
|:------:|:------:|:-------:|:-----------------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|   31   |   wo   |   0x0   | go               | A write of 1 to this bit indicates to the DOE instance that it can start consuming the data object transferred through the DOE Write Data Mailbox register.                                                                                            |
|  30:4  |        |         |                  | Reserved                                                                                                                                                                                                                                               |
|   3    |   rw   |   0x0   | doe_async_msg_en | If DOE Async Message Support is Set, this bit, when Set, enables the use of the DOE Async Message mechanism. When this bit is set, it allows the DOE instance to raise the SOC_STATUS.doe_async_msg_status, indicating an asnchronous message request. |
|   2    |        |         |                  | Reserved                                                                                                                                                                                                                                               |
|   1    |   rw   |   0x0   | doe_intr_en      | If DOE interrupt support is set, when this bit is set and MSI/MSI-X is enabled in MSI capability registers, the DOE instance must issue an MSI/MSI-X interrupt.                                                                                        |
|   0    |   wo   |   0x0   | abort            | A write of 1 to this bit causes all data object transfer operations associated with this DOE instance to be aborted.                                                                                                                                   |

## SOC_STATUS
DOE mailbox status register
- Offset: `0xc`
- Reset default: `0x1`
- Reset mask: `0x8000000f`

### Fields

```wavejson
{"reg": [{"name": "busy", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "doe_intr_status", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "error", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "doe_async_msg_status", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 27}, {"name": "ready", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                                                      |
|:------:|:------:|:-------:|:----------------------------------------------------------|
|   31   |   ro   |   0x0   | [ready](#soc_status--ready)                               |
|  30:4  |        |         | Reserved                                                  |
|   3    |   ro   |   0x0   | [doe_async_msg_status](#soc_status--doe_async_msg_status) |
|   2    |   ro   |   0x0   | [error](#soc_status--error)                               |
|   1    |  rw1c  |   0x0   | [doe_intr_status](#soc_status--doe_intr_status)           |
|   0    |   ro   |   0x1   | [busy](#soc_status--busy)                                 |

### SOC_STATUS . ready
When Set, this bit indicates the DOE instance has a data object available to be read by SoC firmware/software.
The transition of this bit from Clear to Set is an interrupt-triggering event.

### SOC_STATUS . doe_async_msg_status
This bit, when Set, indicates the DOE instance has one or more asynchronous messages to transfer.
The transition of this bit from Clear to Set is an interrupt-triggering event.
This bit is set when an interrupt event occurs.

### SOC_STATUS . error
When Set, this bit indicates that there has been an internal error associated with data object received, or that a data object has been received for which the DOE instance is unable to provide a response.
The transition of this bit from Clear to Set is an interrupt-triggering event.

### SOC_STATUS . doe_intr_status
This bit is set when an interrupt event occurs. Writing a value of 1 to this bit clears the status bit.

### SOC_STATUS . busy
When Set, this bit indicates the DOE instance is temporarily unable to receive a new data object through the DOE Write Data Mailbox register.
This bit is also set by the DOE instance when processing an abort command and remains set until abort handling is complete.

## WDATA
DOE mailbox write data register.
The DOE instance receives data objects via writes to this register.
A successful write adds one DWORD to the data object being assembled in the DOE instance.
A write of 1 to the DOE Go bit in the DOE Control Register marks the completion of the data transfer, i.e, final DWORD for the object has been written.

- Word Aligned Offset Range: `0x10`to`0x10`
- Size (words): `1`
- Access: `wo`
- Byte writes are *not* supported.

## RDATA
DOE mailbox read data register
If the Data Object Ready bit is Set, a read of this register returns the current DWORD of the data object.
A write of any value to this register indicates a successful read of the current DWORD.
The next read to this register shall return the next DWORD from the data object being read.
If Data Object Ready bit is clear, writes of any value to this register must have no effect and reads from this register return zero.

- Word Aligned Offset Range: `0x14`to`0x14`
- Size (words): `1`
- Access: `rw`
- Byte writes are *not* supported.

## SOC_DOE_INTR_MSG_ADDR
Utilized by the mailbox responder to send an interrupt message to the requester via a write to the configured address.
Defined only for FW-to-FW mailboxes.
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "doe_intr_msg_addr", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                                                                                                            |
|:------:|:------:|:-------:|:------------------|:-----------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | doe_intr_msg_addr | Utilized by the mailbox responder to send an interrupt message to the requester via a write to the configured address. |

## SOC_DOE_INTR_MSG_DATA
Interrupt message data to be sent to the address configured in the DOE_INTR_MSG_ADDR register.
Defined only for FW-to-FW mailboxes.
- Offset: `0x1c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "doe_intr_msg_data", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                                                                                    |
|:------:|:------:|:-------:|:------------------|:-----------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | doe_intr_msg_data | Interrupt message data to be sent to the address configured in the DOE_INTR_MSG_ADDR register. |


<!-- END CMDGEN -->
