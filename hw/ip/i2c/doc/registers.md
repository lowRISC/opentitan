# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/i2c/data/i2c.hjson -->
## Summary

| Name                                          | Offset   |   Length | Description                                                                          |
|:----------------------------------------------|:---------|---------:|:-------------------------------------------------------------------------------------|
| i2c.[`INTR_STATE`](#intr_state)               | 0x0      |        4 | Interrupt State Register                                                             |
| i2c.[`INTR_ENABLE`](#intr_enable)             | 0x4      |        4 | Interrupt Enable Register                                                            |
| i2c.[`INTR_TEST`](#intr_test)                 | 0x8      |        4 | Interrupt Test Register                                                              |
| i2c.[`ALERT_TEST`](#alert_test)               | 0xc      |        4 | Alert Test Register                                                                  |
| i2c.[`CTRL`](#ctrl)                           | 0x10     |        4 | I2C Control Register                                                                 |
| i2c.[`STATUS`](#status)                       | 0x14     |        4 | I2C Live Status Register                                                             |
| i2c.[`RDATA`](#rdata)                         | 0x18     |        4 | I2C Read Data                                                                        |
| i2c.[`FDATA`](#fdata)                         | 0x1c     |        4 | I2C Format Data                                                                      |
| i2c.[`FIFO_CTRL`](#fifo_ctrl)                 | 0x20     |        4 | I2C FIFO control register                                                            |
| i2c.[`FIFO_STATUS`](#fifo_status)             | 0x24     |        4 | I2C FIFO status register                                                             |
| i2c.[`OVRD`](#ovrd)                           | 0x28     |        4 | I2C Override Control Register                                                        |
| i2c.[`VAL`](#val)                             | 0x2c     |        4 | Oversampled RX values                                                                |
| i2c.[`TIMING0`](#timing0)                     | 0x30     |        4 | Detailed I2C Timings (directly corresponding to table 10 in the I2C Specification).  |
| i2c.[`TIMING1`](#timing1)                     | 0x34     |        4 | Detailed I2C Timings (directly corresponding to table 10 in the I2C Specification).  |
| i2c.[`TIMING2`](#timing2)                     | 0x38     |        4 | Detailed I2C Timings (directly corresponding to table 10 in the I2C Specification).  |
| i2c.[`TIMING3`](#timing3)                     | 0x3c     |        4 | Detailed I2C Timings (directly corresponding to table 10, in the I2C Specification). |
| i2c.[`TIMING4`](#timing4)                     | 0x40     |        4 | Detailed I2C Timings (directly corresponding to table 10, in the I2C Specification). |
| i2c.[`TIMEOUT_CTRL`](#timeout_ctrl)           | 0x44     |        4 | I2C clock stretching timeout control                                                 |
| i2c.[`TARGET_ID`](#target_id)                 | 0x48     |        4 | I2C target address and mask pairs                                                    |
| i2c.[`ACQDATA`](#acqdata)                     | 0x4c     |        4 | I2C target acquired data                                                             |
| i2c.[`TXDATA`](#txdata)                       | 0x50     |        4 | I2C target transmit data                                                             |
| i2c.[`HOST_TIMEOUT_CTRL`](#host_timeout_ctrl) | 0x54     |        4 | I2C host clock generation timeout value (in units of input clock frequency)          |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x7fff`

### Fields

```wavejson
{"reg": [{"name": "fmt_threshold", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "rx_threshold", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "fmt_overflow", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "rx_overflow", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "nak", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "scl_interference", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "sda_interference", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "stretch_timeout", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "sda_unstable", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "cmd_complete", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "tx_stretch", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "tx_overflow", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "acq_full", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "unexp_stop", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "host_timeout", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 17}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                                                                                                                                                                          |
|:------:|:------:|:-------:|:-----------------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:15  |        |         |                  | Reserved                                                                                                                                                                                                             |
|   14   |  rw1c  |   0x0   | host_timeout     | target mode interrupt: raised if the host stops sending the clock during an ongoing transaction.                                                                                                                     |
|   13   |  rw1c  |   0x0   | unexp_stop       | target mode interrupt: raised if STOP is received without a preceding NACK during an external host read.                                                                                                             |
|   12   |   ro   |   0x0   | acq_full         | target mode interrupt: raised if ACQ FIFO becomes full.  This is a level status interrupt.                                                                                                                           |
|   11   |  rw1c  |   0x0   | tx_overflow      | target mode interrupt: raised if TX FIFO has overflowed.                                                                                                                                                             |
|   10   |   ro   |   0x0   | tx_stretch       | target mode interrupt: raised if the target is stretching clocks for a read command.  This is a level status interrupt.                                                                                              |
|   9    |  rw1c  |   0x0   | cmd_complete     | host and target mode interrupt. In host mode, raised if the host issues a repeated START or terminates the transaction by issuing STOP. In target mode, raised if the external host issues a STOP or repeated START. |
|   8    |  rw1c  |   0x0   | sda_unstable     | host mode interrupt: raised if the target does not assert a constant value of SDA during transmission.                                                                                                               |
|   7    |  rw1c  |   0x0   | stretch_timeout  | host mode interrupt: raised if target stretches the clock beyond the allowed timeout period                                                                                                                          |
|   6    |  rw1c  |   0x0   | sda_interference | host mode interrupt: raised if the SDA line goes low when host is trying to assert high                                                                                                                              |
|   5    |  rw1c  |   0x0   | scl_interference | host mode interrupt: raised if the SCL line drops early (not supported without clock synchronization).                                                                                                               |
|   4    |  rw1c  |   0x0   | nak              | host mode interrupt: raised if there is no ACK in response to an address or data write                                                                                                                               |
|   3    |  rw1c  |   0x0   | rx_overflow      | host mode interrupt: raised if the RX FIFO has overflowed.                                                                                                                                                           |
|   2    |  rw1c  |   0x0   | fmt_overflow     | host mode interrupt: raised if the FMT FIFO has overflowed.                                                                                                                                                          |
|   1    |  rw1c  |   0x0   | rx_threshold     | host mode interrupt: raised if the RX FIFO is greater than the high threshold.                                                                                                                                       |
|   0    |  rw1c  |   0x0   | fmt_threshold    | host mode interrupt: raised when the FMT FIFO depth is less than the low threshold.                                                                                                                                  |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x7fff`

### Fields

```wavejson
{"reg": [{"name": "fmt_threshold", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rx_threshold", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "fmt_overflow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rx_overflow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "nak", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "scl_interference", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "sda_interference", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "stretch_timeout", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "sda_unstable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "cmd_complete", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "tx_stretch", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "tx_overflow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "acq_full", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "unexp_stop", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "host_timeout", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 17}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                                |
|:------:|:------:|:-------:|:-----------------|:---------------------------------------------------------------------------|
| 31:15  |        |         |                  | Reserved                                                                   |
|   14   |   rw   |   0x0   | host_timeout     | Enable interrupt when [`INTR_STATE.host_timeout`](#intr_state) is set.     |
|   13   |   rw   |   0x0   | unexp_stop       | Enable interrupt when [`INTR_STATE.unexp_stop`](#intr_state) is set.       |
|   12   |   rw   |   0x0   | acq_full         | Enable interrupt when [`INTR_STATE.acq_full`](#intr_state) is set.         |
|   11   |   rw   |   0x0   | tx_overflow      | Enable interrupt when [`INTR_STATE.tx_overflow`](#intr_state) is set.      |
|   10   |   rw   |   0x0   | tx_stretch       | Enable interrupt when [`INTR_STATE.tx_stretch`](#intr_state) is set.       |
|   9    |   rw   |   0x0   | cmd_complete     | Enable interrupt when [`INTR_STATE.cmd_complete`](#intr_state) is set.     |
|   8    |   rw   |   0x0   | sda_unstable     | Enable interrupt when [`INTR_STATE.sda_unstable`](#intr_state) is set.     |
|   7    |   rw   |   0x0   | stretch_timeout  | Enable interrupt when [`INTR_STATE.stretch_timeout`](#intr_state) is set.  |
|   6    |   rw   |   0x0   | sda_interference | Enable interrupt when [`INTR_STATE.sda_interference`](#intr_state) is set. |
|   5    |   rw   |   0x0   | scl_interference | Enable interrupt when [`INTR_STATE.scl_interference`](#intr_state) is set. |
|   4    |   rw   |   0x0   | nak              | Enable interrupt when [`INTR_STATE.nak`](#intr_state) is set.              |
|   3    |   rw   |   0x0   | rx_overflow      | Enable interrupt when [`INTR_STATE.rx_overflow`](#intr_state) is set.      |
|   2    |   rw   |   0x0   | fmt_overflow     | Enable interrupt when [`INTR_STATE.fmt_overflow`](#intr_state) is set.     |
|   1    |   rw   |   0x0   | rx_threshold     | Enable interrupt when [`INTR_STATE.rx_threshold`](#intr_state) is set.     |
|   0    |   rw   |   0x0   | fmt_threshold    | Enable interrupt when [`INTR_STATE.fmt_threshold`](#intr_state) is set.    |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x7fff`

### Fields

```wavejson
{"reg": [{"name": "fmt_threshold", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rx_threshold", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fmt_overflow", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rx_overflow", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "nak", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "scl_interference", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "sda_interference", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "stretch_timeout", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "sda_unstable", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "cmd_complete", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "tx_stretch", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "tx_overflow", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "acq_full", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "unexp_stop", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "host_timeout", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 17}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                         |
|:------:|:------:|:-------:|:-----------------|:--------------------------------------------------------------------|
| 31:15  |        |         |                  | Reserved                                                            |
|   14   |   wo   |   0x0   | host_timeout     | Write 1 to force [`INTR_STATE.host_timeout`](#intr_state) to 1.     |
|   13   |   wo   |   0x0   | unexp_stop       | Write 1 to force [`INTR_STATE.unexp_stop`](#intr_state) to 1.       |
|   12   |   wo   |   0x0   | acq_full         | Write 1 to force [`INTR_STATE.acq_full`](#intr_state) to 1.         |
|   11   |   wo   |   0x0   | tx_overflow      | Write 1 to force [`INTR_STATE.tx_overflow`](#intr_state) to 1.      |
|   10   |   wo   |   0x0   | tx_stretch       | Write 1 to force [`INTR_STATE.tx_stretch`](#intr_state) to 1.       |
|   9    |   wo   |   0x0   | cmd_complete     | Write 1 to force [`INTR_STATE.cmd_complete`](#intr_state) to 1.     |
|   8    |   wo   |   0x0   | sda_unstable     | Write 1 to force [`INTR_STATE.sda_unstable`](#intr_state) to 1.     |
|   7    |   wo   |   0x0   | stretch_timeout  | Write 1 to force [`INTR_STATE.stretch_timeout`](#intr_state) to 1.  |
|   6    |   wo   |   0x0   | sda_interference | Write 1 to force [`INTR_STATE.sda_interference`](#intr_state) to 1. |
|   5    |   wo   |   0x0   | scl_interference | Write 1 to force [`INTR_STATE.scl_interference`](#intr_state) to 1. |
|   4    |   wo   |   0x0   | nak              | Write 1 to force [`INTR_STATE.nak`](#intr_state) to 1.              |
|   3    |   wo   |   0x0   | rx_overflow      | Write 1 to force [`INTR_STATE.rx_overflow`](#intr_state) to 1.      |
|   2    |   wo   |   0x0   | fmt_overflow     | Write 1 to force [`INTR_STATE.fmt_overflow`](#intr_state) to 1.     |
|   1    |   wo   |   0x0   | rx_threshold     | Write 1 to force [`INTR_STATE.rx_threshold`](#intr_state) to 1.     |
|   0    |   wo   |   0x0   | fmt_threshold    | Write 1 to force [`INTR_STATE.fmt_threshold`](#intr_state) to 1.    |

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

## CTRL
I2C Control Register
- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "ENABLEHOST", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ENABLETARGET", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "LLPBK", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                                                                                |
|:------:|:------:|:-------:|:-------------|:-----------------------------------------------------------------------------------------------------------|
|  31:3  |        |         |              | Reserved                                                                                                   |
|   2    |   rw   |   0x0   | LLPBK        | Enable I2C line loopback test If line loopback is enabled, the internal design sees ACQ and RX data as "1" |
|   1    |   rw   |   0x0   | ENABLETARGET | Enable Target I2C functionality                                                                            |
|   0    |   rw   |   0x0   | ENABLEHOST   | Enable Host I2C functionality                                                                              |

## STATUS
I2C Live Status Register
- Offset: `0x14`
- Reset default: `0x33c`
- Reset mask: `0x3ff`

### Fields

```wavejson
{"reg": [{"name": "FMTFULL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "RXFULL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FMTEMPTY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "HOSTIDLE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TARGETIDLE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "RXEMPTY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TXFULL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ACQFULL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TXEMPTY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ACQEMPTY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 22}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                        |
|:------:|:------:|:-------:|:-----------|:-------------------------------------------------------------------|
| 31:10  |        |         |            | Reserved                                                           |
|   9    |   ro   |   0x1   | ACQEMPTY   | ACQ FIFO is empty                                                  |
|   8    |   ro   |   0x1   | TXEMPTY    | TX FIFO is empty                                                   |
|   7    |   ro   |    x    | ACQFULL    | ACQ FIFO is full                                                   |
|   6    |   ro   |    x    | TXFULL     | TX FIFO is full                                                    |
|   5    |   ro   |   0x1   | RXEMPTY    | RX FIFO is empty                                                   |
|   4    |   ro   |   0x1   | TARGETIDLE | Target functionality is idle. No Target transaction is in progress |
|   3    |   ro   |   0x1   | HOSTIDLE   | Host functionality is idle. No Host transaction is in progress     |
|   2    |   ro   |   0x1   | FMTEMPTY   | FMT FIFO is empty                                                  |
|   1    |   ro   |    x    | RXFULL     | RX FIFO is full                                                    |
|   0    |   ro   |    x    | FMTFULL    | FMT FIFO is full                                                   |

## RDATA
I2C Read Data
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "RDATA", "bits": 8, "attr": ["ro"], "rotate": 0}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:8  |        |         |        | Reserved      |
|  7:0   |   ro   |    x    | RDATA  |               |

## FDATA
I2C Format Data
- Offset: `0x1c`
- Reset default: `0x0`
- Reset mask: `0x1fff`

### Fields

```wavejson
{"reg": [{"name": "FBYTE", "bits": 8, "attr": ["wo"], "rotate": 0}, {"name": "START", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "STOP", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "READB", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "RCONT", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "NAKOK", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 19}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                     |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------|
| 31:13  |        |         |        | Reserved                                                        |
|   12   |   wo   |   0x0   | NAKOK  | Do not signal an exception if the current byte is not ACK'd     |
|   11   |   wo   |   0x0   | RCONT  | Do not NACK the last byte read, let the read operation continue |
|   10   |   wo   |   0x0   | READB  | Read BYTE bytes from I2C. (256 if BYTE==0)                      |
|   9    |   wo   |   0x0   | STOP   | Issue a STOP condition after this operation                     |
|   8    |   wo   |   0x0   | START  | Issue a START condition before transmitting BYTE.               |
|  7:0   |   wo   |   0x0   | FBYTE  | Format Byte. Directly transmitted if no flags are set.          |

## FIFO_CTRL
I2C FIFO control register
- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0x1ff`

### Fields

```wavejson
{"reg": [{"name": "RXRST", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "FMTRST", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "RXILVL", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "FMTILVL", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "ACQRST", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "TXRST", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 23}], "config": {"lanes": 1, "fontsize": 10, "vspace": 90}}
```

|  Bits  |  Type  |  Reset  | Name                           |
|:------:|:------:|:-------:|:-------------------------------|
|  31:9  |        |         | Reserved                       |
|   8    |   wo   |   0x0   | [TXRST](#fifo_ctrl--txrst)     |
|   7    |   wo   |   0x0   | [ACQRST](#fifo_ctrl--acqrst)   |
|  6:5   |   rw   |   0x0   | [FMTILVL](#fifo_ctrl--fmtilvl) |
|  4:2   |   rw   |   0x0   | [RXILVL](#fifo_ctrl--rxilvl)   |
|   1    |   wo   |   0x0   | [FMTRST](#fifo_ctrl--fmtrst)   |
|   0    |   wo   |   0x0   | [RXRST](#fifo_ctrl--rxrst)     |

### FIFO_CTRL . TXRST
TX FIFO reset. Write 1 to the register resets it. Read returns 0

### FIFO_CTRL . ACQRST
ACQ FIFO reset. Write 1 to the register resets it. Read returns 0

### FIFO_CTRL . FMTILVL
Trigger level for FMT interrupts. If the FIFO depth falls below
this setting, it raises fmt_threshold interrupt.

| Value   | Name     | Description   |
|:--------|:---------|:--------------|
| 0x0     | fmtlvl1  | 1 character   |
| 0x1     | fmtlvl4  | 4 characters  |
| 0x2     | fmtlvl8  | 8 characters  |
| 0x3     | fmtlvl16 | 16 characters |


### FIFO_CTRL . RXILVL
Trigger level for RX interrupts. If the FIFO depth exceeds
this setting, it raises rx_threshold interrupt.

| Value   | Name    | Description   |
|:--------|:--------|:--------------|
| 0x0     | rxlvl1  | 1 character   |
| 0x1     | rxlvl4  | 4 characters  |
| 0x2     | rxlvl8  | 8 characters  |
| 0x3     | rxlvl16 | 16 characters |
| 0x4     | rxlvl30 | 30 characters |

Other values are reserved.

### FIFO_CTRL . FMTRST
FMT fifo reset. Write 1 to the register resets FMT_FIFO. Read returns 0

### FIFO_CTRL . RXRST
RX fifo reset. Write 1 to the register resets RX_FIFO. Read returns 0

## FIFO_STATUS
I2C FIFO status register
- Offset: `0x24`
- Reset default: `0x0`
- Reset mask: `0x7f7f7f7f`

### Fields

```wavejson
{"reg": [{"name": "FMTLVL", "bits": 7, "attr": ["ro"], "rotate": 0}, {"bits": 1}, {"name": "TXLVL", "bits": 7, "attr": ["ro"], "rotate": 0}, {"bits": 1}, {"name": "RXLVL", "bits": 7, "attr": ["ro"], "rotate": 0}, {"bits": 1}, {"name": "ACQLVL", "bits": 7, "attr": ["ro"], "rotate": 0}, {"bits": 1}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                    |
|:------:|:------:|:-------:|:-------|:-------------------------------|
|   31   |        |         |        | Reserved                       |
| 30:24  |   ro   |    x    | ACQLVL | Current fill level of ACQ fifo |
|   23   |        |         |        | Reserved                       |
| 22:16  |   ro   |    x    | RXLVL  | Current fill level of RX fifo  |
|   15   |        |         |        | Reserved                       |
|  14:8  |   ro   |    x    | TXLVL  | Current fill level of TX fifo  |
|   7    |        |         |        | Reserved                       |
|  6:0   |   ro   |    x    | FMTLVL | Current fill level of FMT fifo |

## OVRD
I2C Override Control Register
- Offset: `0x28`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "TXOVRDEN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "SCLVAL", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "SDAVAL", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                               |
|:------:|:------:|:-------:|:---------|:--------------------------------------------------------------------------|
|  31:3  |        |         |          | Reserved                                                                  |
|   2    |   rw   |   0x0   | SDAVAL   | Value for SDA Override. Set to 0 to drive TX Low, and set to 1 for high-Z |
|   1    |   rw   |   0x0   | SCLVAL   | Value for SCL Override. Set to 0 to drive TX Low, and set to 1 for high-Z |
|   0    |   rw   |   0x0   | TXOVRDEN | Override the SDA and SCL TX signals.                                      |

## VAL
Oversampled RX values
- Offset: `0x2c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "SCL_RX", "bits": 16, "attr": ["ro"], "rotate": 0}, {"name": "SDA_RX", "bits": 16, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                              |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------------------------------|
| 31:16  |   ro   |    x    | SDA_RX | Last 16 oversampled values of SDA. Most recent bit is bit 16, oldest 31. |
|  15:0  |   ro   |    x    | SCL_RX | Last 16 oversampled values of SCL. Most recent bit is bit 0, oldest 15.  |

## TIMING0
Detailed I2C Timings (directly corresponding to table 10 in the I2C Specification).
All values are expressed in units of the input clock period.
These must be greater than 2 in order for the change in SCL to propagate to the input of the FSM so that acknowledgements are detected correctly.
- Offset: `0x30`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "THIGH", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "TLOW", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                           |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:16  |   rw   |   0x0   | TLOW   | The actual time to hold SCL low between any two SCL pulses                                                                                            |
|  15:0  |   rw   |   0x0   | THIGH  | The actual time to hold SCL high in a given pulse: in host mode, when there is no stretching this value is 3 cycles longer as tracked in issue #18962 |

## TIMING1
Detailed I2C Timings (directly corresponding to table 10 in the I2C Specification).
All values are expressed in units of the input clock period.
- Offset: `0x34`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "T_R", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "T_F", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                          |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:16  |   rw   |   0x0   | T_F    | The nominal fall time to anticipate for the bus (influences SDA hold times): this is currently counted twice in host mode as tracked in issue #18958 |
|  15:0  |   rw   |   0x0   | T_R    | The nominal rise time to anticipate for the bus (depends on capacitance)                                                                             |

## TIMING2
Detailed I2C Timings (directly corresponding to table 10 in the I2C Specification).
All values are expressed in units of the input clock period.
- Offset: `0x38`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "TSU_STA", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "THD_STA", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name    | Description                                  |
|:------:|:------:|:-------:|:--------|:---------------------------------------------|
| 31:16  |   rw   |   0x0   | THD_STA | Actual hold time for start signals           |
|  15:0  |   rw   |   0x0   | TSU_STA | Actual setup time for repeated start signals |

## TIMING3
Detailed I2C Timings (directly corresponding to table 10, in the I2C Specification).
All values are expressed in units of the input clock period.
- Offset: `0x3c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "TSU_DAT", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "THD_DAT", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name    | Description                                                                                                       |
|:------:|:------:|:-------:|:--------|:------------------------------------------------------------------------------------------------------------------|
| 31:16  |   rw   |   0x0   | THD_DAT | Actual hold time for data (or ack) bits (Note, where required, the parameters TVD_DAT is taken to be THD_DAT+T_F) |
|  15:0  |   rw   |   0x0   | TSU_DAT | Actual setup time for data (or ack) bits                                                                          |

## TIMING4
Detailed I2C Timings (directly corresponding to table 10, in the I2C Specification).
All values are expressed in units of the input clock period.
- Offset: `0x40`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "TSU_STO", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "T_BUF", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name    | Description                                                         |
|:------:|:------:|:-------:|:--------|:--------------------------------------------------------------------|
| 31:16  |   rw   |   0x0   | T_BUF   | Actual time between each STOP signal and the following START signal |
|  15:0  |   rw   |   0x0   | TSU_STO | Actual setup time for stop signals                                  |

## TIMEOUT_CTRL
I2C clock stretching timeout control
- Offset: `0x44`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 31, "attr": ["rw"], "rotate": 0}, {"name": "EN", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                        |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------------------------|
|   31   |   rw   |   0x0   | EN     | Enable timeout feature                                             |
|  30:0  |   rw   |   0x0   | VAL    | Clock stretching timeout value (in units of input clock frequency) |

## TARGET_ID
I2C target address and mask pairs
- Offset: `0x48`
- Reset default: `0x0`
- Reset mask: `0xfffffff`

### Fields

```wavejson
{"reg": [{"name": "ADDRESS0", "bits": 7, "attr": ["rw"], "rotate": 0}, {"name": "MASK0", "bits": 7, "attr": ["rw"], "rotate": 0}, {"name": "ADDRESS1", "bits": 7, "attr": ["rw"], "rotate": 0}, {"name": "MASK1", "bits": 7, "attr": ["rw"], "rotate": 0}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                 |
|:------:|:------:|:-------:|:---------|:----------------------------|
| 31:28  |        |         |          | Reserved                    |
| 27:21  |   rw   |   0x0   | MASK1    | I2C target mask number 1    |
| 20:14  |   rw   |   0x0   | ADDRESS1 | I2C target address number 1 |
|  13:7  |   rw   |   0x0   | MASK0    | I2C target mask number 0    |
|  6:0   |   rw   |   0x0   | ADDRESS0 | I2C target address number 0 |

## ACQDATA
I2C target acquired data
- Offset: `0x4c`
- Reset default: `0x0`
- Reset mask: `0x3ff`

### Fields

```wavejson
{"reg": [{"name": "ABYTE", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "SIGNAL", "bits": 2, "attr": ["ro"], "rotate": -90}, {"bits": 22}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                       |
|:------:|:------:|:-------:|:---------------------------|
| 31:10  |        |         | Reserved                   |
|  9:8   |   ro   |    x    | [SIGNAL](#acqdata--signal) |
|  7:0   |   ro   |    x    | [ABYTE](#acqdata--abyte)   |

### ACQDATA . SIGNAL
Host issued a START before transmitting ABYTE, a STOP or a RESTART after the preceeding ABYTE

| Value   | Name    | Description                                         |
|:--------|:--------|:----------------------------------------------------|
| 0x0     | NONE    | ABYTE contains ordinary data byte as received       |
| 0x1     | START   | ABYTE contains the 8-bit I2C address (R/W in lsb)   |
| 0x2     | STOP    | ABYTE contains junk                                 |
| 0x3     | RESTART | ABYTE contains junk, START with address will follow |


### ACQDATA . ABYTE
Address for accepted transaction or acquired byte

## TXDATA
I2C target transmit data
- Offset: `0x50`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "TXDATA", "bits": 8, "attr": ["wo"], "rotate": 0}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:8  |        |         |        | Reserved      |
|  7:0   |   wo   |   0x0   | TXDATA |               |

## HOST_TIMEOUT_CTRL
I2C host clock generation timeout value (in units of input clock frequency)
- Offset: `0x54`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "HOST_TIMEOUT_CTRL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name              | Description   |
|:------:|:------:|:-------:|:------------------|:--------------|
|  31:0  |   rw   |   0x0   | HOST_TIMEOUT_CTRL |               |


<!-- END CMDGEN -->
