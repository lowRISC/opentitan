# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/i2c/data/i2c.hjson -->
## Summary

| Name                                                          | Offset   |   Length | Description                                                                                        |
|:--------------------------------------------------------------|:---------|---------:|:---------------------------------------------------------------------------------------------------|
| i2c.[`INTR_STATE`](#intr_state)                               | 0x0      |        4 | Interrupt State Register                                                                           |
| i2c.[`INTR_ENABLE`](#intr_enable)                             | 0x4      |        4 | Interrupt Enable Register                                                                          |
| i2c.[`INTR_TEST`](#intr_test)                                 | 0x8      |        4 | Interrupt Test Register                                                                            |
| i2c.[`ALERT_TEST`](#alert_test)                               | 0xc      |        4 | Alert Test Register                                                                                |
| i2c.[`CTRL`](#ctrl)                                           | 0x10     |        4 | I2C Control Register                                                                               |
| i2c.[`STATUS`](#status)                                       | 0x14     |        4 | I2C Live Status Register for Host and Target modes                                                 |
| i2c.[`RDATA`](#rdata)                                         | 0x18     |        4 | I2C Read Data                                                                                      |
| i2c.[`FDATA`](#fdata)                                         | 0x1c     |        4 | I2C Host Format Data                                                                               |
| i2c.[`FIFO_CTRL`](#fifo_ctrl)                                 | 0x20     |        4 | I2C FIFO control register                                                                          |
| i2c.[`HOST_FIFO_CONFIG`](#host_fifo_config)                   | 0x24     |        4 | Host mode FIFO configuration                                                                       |
| i2c.[`TARGET_FIFO_CONFIG`](#target_fifo_config)               | 0x28     |        4 | Target mode FIFO configuration                                                                     |
| i2c.[`HOST_FIFO_STATUS`](#host_fifo_status)                   | 0x2c     |        4 | Host mode FIFO status register                                                                     |
| i2c.[`TARGET_FIFO_STATUS`](#target_fifo_status)               | 0x30     |        4 | Target mode FIFO status register                                                                   |
| i2c.[`OVRD`](#ovrd)                                           | 0x34     |        4 | I2C Override Control Register                                                                      |
| i2c.[`VAL`](#val)                                             | 0x38     |        4 | Oversampled RX values                                                                              |
| i2c.[`TIMING0`](#timing0)                                     | 0x3c     |        4 | Detailed I2C Timings (directly corresponding to table 10 in the I2C Specification).                |
| i2c.[`TIMING1`](#timing1)                                     | 0x40     |        4 | Detailed I2C Timings (directly corresponding to table 10 in the I2C Specification).                |
| i2c.[`TIMING2`](#timing2)                                     | 0x44     |        4 | Detailed I2C Timings (directly corresponding to table 10 in the I2C Specification).                |
| i2c.[`TIMING3`](#timing3)                                     | 0x48     |        4 | Detailed I2C Timings (directly corresponding to table 10, in the I2C Specification).               |
| i2c.[`TIMING4`](#timing4)                                     | 0x4c     |        4 | Detailed I2C Timings (directly corresponding to table 10, in the I2C Specification).               |
| i2c.[`TIMEOUT_CTRL`](#timeout_ctrl)                           | 0x50     |        4 | I2C clock stretching timeout control.                                                              |
| i2c.[`TARGET_ID`](#target_id)                                 | 0x54     |        4 | I2C target address and mask pairs                                                                  |
| i2c.[`ACQDATA`](#acqdata)                                     | 0x58     |        4 | I2C target acquired data                                                                           |
| i2c.[`TXDATA`](#txdata)                                       | 0x5c     |        4 | I2C target transmit data                                                                           |
| i2c.[`HOST_TIMEOUT_CTRL`](#host_timeout_ctrl)                 | 0x60     |        4 | I2C host clock generation timeout value (in units of input clock frequency).                       |
| i2c.[`TARGET_TIMEOUT_CTRL`](#target_timeout_ctrl)             | 0x64     |        4 | I2C target internal stretching timeout control.                                                    |
| i2c.[`TARGET_NACK_COUNT`](#target_nack_count)                 | 0x68     |        4 | Number of times the I2C target has NACK'ed a new transaction since the last read of this register. |
| i2c.[`HOST_NACK_HANDLER_TIMEOUT`](#host_nack_handler_timeout) | 0x6c     |        4 | Timeout in Host-Mode for an unhandled NACK before hardware automatically ends the transaction.     |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x7fff`

### Fields

```wavejson
{"reg": [{"name": "fmt_threshold", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "rx_threshold", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "acq_threshold", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "rx_overflow", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "nak", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "scl_interference", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "sda_interference", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "stretch_timeout", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "sda_unstable", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "cmd_complete", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "tx_stretch", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "tx_threshold", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "acq_full", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "unexp_stop", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "host_timeout", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 17}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                                                                                                                                                                          |
|:------:|:------:|:-------:|:-----------------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:15  |        |         |                  | Reserved                                                                                                                                                                                                             |
|   14   |  rw1c  |   0x0   | host_timeout     | target mode interrupt: raised if the host stops sending the clock during an ongoing transaction.                                                                                                                     |
|   13   |  rw1c  |   0x0   | unexp_stop       | target mode interrupt: raised if STOP is received without a preceding NACK during an external host read.                                                                                                             |
|   12   |   ro   |   0x0   | acq_full         | target mode interrupt: raised if ACQ FIFO becomes full. This is a level status interrupt.                                                                                                                            |
|   11   |   ro   |   0x0   | tx_threshold     | target mode interrupt: asserted whilst the TX FIFO level is below the low threshold. This is a level status interrupt.                                                                                               |
|   10   |   ro   |   0x0   | tx_stretch       | target mode interrupt: raised if the target is stretching clocks for a read command. This is a level status interrupt.                                                                                               |
|   9    |  rw1c  |   0x0   | cmd_complete     | host and target mode interrupt. In host mode, raised if the host issues a repeated START or terminates the transaction by issuing STOP. In target mode, raised if the external host issues a STOP or repeated START. |
|   8    |  rw1c  |   0x0   | sda_unstable     | host mode interrupt: raised if the target does not assert a constant value of SDA during transmission.                                                                                                               |
|   7    |  rw1c  |   0x0   | stretch_timeout  | host mode interrupt: raised if target stretches the clock beyond the allowed timeout period                                                                                                                          |
|   6    |  rw1c  |   0x0   | sda_interference | host mode interrupt: raised if the SDA line goes low when host is trying to assert high                                                                                                                              |
|   5    |  rw1c  |   0x0   | scl_interference | host mode interrupt: raised if the SCL line drops early (not supported without clock synchronization).                                                                                                               |
|   4    |  rw1c  |   0x0   | nak              | host mode interrupt: raised if there is no ACK in response to an address or data write                                                                                                                               |
|   3    |  rw1c  |   0x0   | rx_overflow      | host mode interrupt: raised if the RX FIFO has overflowed.                                                                                                                                                           |
|   2    |   ro   |   0x0   | acq_threshold    | target mode interrupt: asserted whilst the ACQ FIFO level is above the high threshold. This is a level status interrupt.                                                                                             |
|   1    |   ro   |   0x0   | rx_threshold     | host mode interrupt: asserted whilst the RX FIFO level is above the high threshold. This is a level status interrupt.                                                                                                |
|   0    |   ro   |   0x0   | fmt_threshold    | host mode interrupt: asserted whilst the FMT FIFO level is below the low threshold. This is a level status interrupt.                                                                                                |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x7fff`

### Fields

```wavejson
{"reg": [{"name": "fmt_threshold", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rx_threshold", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "acq_threshold", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rx_overflow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "nak", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "scl_interference", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "sda_interference", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "stretch_timeout", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "sda_unstable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "cmd_complete", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "tx_stretch", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "tx_threshold", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "acq_full", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "unexp_stop", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "host_timeout", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 17}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                                |
|:------:|:------:|:-------:|:-----------------|:---------------------------------------------------------------------------|
| 31:15  |        |         |                  | Reserved                                                                   |
|   14   |   rw   |   0x0   | host_timeout     | Enable interrupt when [`INTR_STATE.host_timeout`](#intr_state) is set.     |
|   13   |   rw   |   0x0   | unexp_stop       | Enable interrupt when [`INTR_STATE.unexp_stop`](#intr_state) is set.       |
|   12   |   rw   |   0x0   | acq_full         | Enable interrupt when [`INTR_STATE.acq_full`](#intr_state) is set.         |
|   11   |   rw   |   0x0   | tx_threshold     | Enable interrupt when [`INTR_STATE.tx_threshold`](#intr_state) is set.     |
|   10   |   rw   |   0x0   | tx_stretch       | Enable interrupt when [`INTR_STATE.tx_stretch`](#intr_state) is set.       |
|   9    |   rw   |   0x0   | cmd_complete     | Enable interrupt when [`INTR_STATE.cmd_complete`](#intr_state) is set.     |
|   8    |   rw   |   0x0   | sda_unstable     | Enable interrupt when [`INTR_STATE.sda_unstable`](#intr_state) is set.     |
|   7    |   rw   |   0x0   | stretch_timeout  | Enable interrupt when [`INTR_STATE.stretch_timeout`](#intr_state) is set.  |
|   6    |   rw   |   0x0   | sda_interference | Enable interrupt when [`INTR_STATE.sda_interference`](#intr_state) is set. |
|   5    |   rw   |   0x0   | scl_interference | Enable interrupt when [`INTR_STATE.scl_interference`](#intr_state) is set. |
|   4    |   rw   |   0x0   | nak              | Enable interrupt when [`INTR_STATE.nak`](#intr_state) is set.              |
|   3    |   rw   |   0x0   | rx_overflow      | Enable interrupt when [`INTR_STATE.rx_overflow`](#intr_state) is set.      |
|   2    |   rw   |   0x0   | acq_threshold    | Enable interrupt when [`INTR_STATE.acq_threshold`](#intr_state) is set.    |
|   1    |   rw   |   0x0   | rx_threshold     | Enable interrupt when [`INTR_STATE.rx_threshold`](#intr_state) is set.     |
|   0    |   rw   |   0x0   | fmt_threshold    | Enable interrupt when [`INTR_STATE.fmt_threshold`](#intr_state) is set.    |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x7fff`

### Fields

```wavejson
{"reg": [{"name": "fmt_threshold", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rx_threshold", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "acq_threshold", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rx_overflow", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "nak", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "scl_interference", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "sda_interference", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "stretch_timeout", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "sda_unstable", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "cmd_complete", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "tx_stretch", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "tx_threshold", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "acq_full", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "unexp_stop", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "host_timeout", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 17}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                         |
|:------:|:------:|:-------:|:-----------------|:--------------------------------------------------------------------|
| 31:15  |        |         |                  | Reserved                                                            |
|   14   |   wo   |   0x0   | host_timeout     | Write 1 to force [`INTR_STATE.host_timeout`](#intr_state) to 1.     |
|   13   |   wo   |   0x0   | unexp_stop       | Write 1 to force [`INTR_STATE.unexp_stop`](#intr_state) to 1.       |
|   12   |   wo   |   0x0   | acq_full         | Write 1 to force [`INTR_STATE.acq_full`](#intr_state) to 1.         |
|   11   |   wo   |   0x0   | tx_threshold     | Write 1 to force [`INTR_STATE.tx_threshold`](#intr_state) to 1.     |
|   10   |   wo   |   0x0   | tx_stretch       | Write 1 to force [`INTR_STATE.tx_stretch`](#intr_state) to 1.       |
|   9    |   wo   |   0x0   | cmd_complete     | Write 1 to force [`INTR_STATE.cmd_complete`](#intr_state) to 1.     |
|   8    |   wo   |   0x0   | sda_unstable     | Write 1 to force [`INTR_STATE.sda_unstable`](#intr_state) to 1.     |
|   7    |   wo   |   0x0   | stretch_timeout  | Write 1 to force [`INTR_STATE.stretch_timeout`](#intr_state) to 1.  |
|   6    |   wo   |   0x0   | sda_interference | Write 1 to force [`INTR_STATE.sda_interference`](#intr_state) to 1. |
|   5    |   wo   |   0x0   | scl_interference | Write 1 to force [`INTR_STATE.scl_interference`](#intr_state) to 1. |
|   4    |   wo   |   0x0   | nak              | Write 1 to force [`INTR_STATE.nak`](#intr_state) to 1.              |
|   3    |   wo   |   0x0   | rx_overflow      | Write 1 to force [`INTR_STATE.rx_overflow`](#intr_state) to 1.      |
|   2    |   wo   |   0x0   | acq_threshold    | Write 1 to force [`INTR_STATE.acq_threshold`](#intr_state) to 1.    |
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
I2C Live Status Register for Host and Target modes
- Offset: `0x14`
- Reset default: `0x33c`
- Reset mask: `0x7ff`

### Fields

```wavejson
{"reg": [{"name": "FMTFULL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "RXFULL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FMTEMPTY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "HOSTIDLE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TARGETIDLE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "RXEMPTY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TXFULL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ACQFULL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TXEMPTY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ACQEMPTY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "HOST_DISABLED_NACK_TIMEOUT", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 21}], "config": {"lanes": 1, "fontsize": 10, "vspace": 280}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                                                                                                                                                                                  |
|:------:|:------:|:-------:|:---------------------------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:11  |        |         |                            | Reserved                                                                                                                                                                                                                     |
|   10   |   ro   |    x    | HOST_DISABLED_NACK_TIMEOUT | A Host-Mode active transaction has been ended by the [`HOST_NACK_HANDLER_TIMEOUT`](#host_nack_handler_timeout) mechanism. This bit is cleared when [`CTRL.ENABLEHOST`](#ctrl) is set by software to start a new transaction. |
|   9    |   ro   |   0x1   | ACQEMPTY                   | Target mode receive FIFO is empty                                                                                                                                                                                            |
|   8    |   ro   |   0x1   | TXEMPTY                    | Target mode TX FIFO is empty                                                                                                                                                                                                 |
|   7    |   ro   |    x    | ACQFULL                    | Target mode receive FIFO is full                                                                                                                                                                                             |
|   6    |   ro   |    x    | TXFULL                     | Target mode TX FIFO is full                                                                                                                                                                                                  |
|   5    |   ro   |   0x1   | RXEMPTY                    | Host mode RX FIFO is empty                                                                                                                                                                                                   |
|   4    |   ro   |   0x1   | TARGETIDLE                 | Target functionality is idle. No Target transaction is in progress                                                                                                                                                           |
|   3    |   ro   |   0x1   | HOSTIDLE                   | Host functionality is idle. No Host transaction is in progress                                                                                                                                                               |
|   2    |   ro   |   0x1   | FMTEMPTY                   | Host mode FMT FIFO is empty                                                                                                                                                                                                  |
|   1    |   ro   |    x    | RXFULL                     | Host mode RX FIFO is full                                                                                                                                                                                                    |
|   0    |   ro   |    x    | FMTFULL                    | Host mode FMT FIFO is full                                                                                                                                                                                                   |

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
I2C Host Format Data
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
- Reset mask: `0x183`

### Fields

```wavejson
{"reg": [{"name": "RXRST", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "FMTRST", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 5}, {"name": "ACQRST", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "TXRST", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 23}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                             |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------------------|
|  31:9  |        |         |        | Reserved                                                                |
|   8    |   wo   |   0x0   | TXRST  | TX FIFO reset. Write 1 to the register resets it. Read returns 0        |
|   7    |   wo   |   0x0   | ACQRST | ACQ FIFO reset. Write 1 to the register resets it. Read returns 0       |
|  6:2   |        |         |        | Reserved                                                                |
|   1    |   wo   |   0x0   | FMTRST | FMT fifo reset. Write 1 to the register resets FMT_FIFO. Read returns 0 |
|   0    |   wo   |   0x0   | RXRST  | RX fifo reset. Write 1 to the register resets RX_FIFO. Read returns 0   |

## HOST_FIFO_CONFIG
Host mode FIFO configuration
- Offset: `0x24`
- Reset default: `0x0`
- Reset mask: `0xfff0fff`

### Fields

```wavejson
{"reg": [{"name": "RX_THRESH", "bits": 12, "attr": ["rw"], "rotate": 0}, {"bits": 4}, {"name": "FMT_THRESH", "bits": 12, "attr": ["rw"], "rotate": 0}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                                                                                                                |
|:------:|:------:|:-------:|:-----------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:28  |        |         |            | Reserved                                                                                                                                                   |
| 27:16  |   rw   |   0x0   | FMT_THRESH | Threshold level for FMT interrupts. Whilst the number of used entries in the FMT FIFO is below this setting, the fmt_threshold interrupt will be asserted. |
| 15:12  |        |         |            | Reserved                                                                                                                                                   |
|  11:0  |   rw   |   0x0   | RX_THRESH  | Threshold level for RX interrupts. Whilst the level of data in the RX FIFO is above this setting, the rx_threshold interrupt will be asserted.             |

## TARGET_FIFO_CONFIG
Target mode FIFO configuration
- Offset: `0x28`
- Reset default: `0x0`
- Reset mask: `0xfff8fff`

### Fields

```wavejson
{"reg": [{"name": "TX_THRESH", "bits": 12, "attr": ["rw"], "rotate": 0}, {"bits": 3}, {"name": "TXRST_ON_COND", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ACQ_THRESH", "bits": 12, "attr": ["rw"], "rotate": 0}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                                                                                                                                                                                                    |
|:------:|:------:|:-------:|:--------------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:28  |        |         |               | Reserved                                                                                                                                                                                                                                       |
| 27:16  |   rw   |   0x0   | ACQ_THRESH    | Threshold level for ACQ interrupts. Whilst the level of data in the ACQ FIFO is above this setting, the acq_threshold interrupt will be asserted.                                                                                              |
|   15   |   rw   |   0x0   | TXRST_ON_COND | If set, automatically reset the TX FIFO (TXRST) upon seeing a RSTART/STOP condition during an active transaction in Target Mode. This may be useful if the remaining data in the TX FIFO becomes no longer applicable to the next transaction. |
| 14:12  |        |         |               | Reserved                                                                                                                                                                                                                                       |
|  11:0  |   rw   |   0x0   | TX_THRESH     | Threshold level for TX interrupts. Whilst the number of used entries in the TX FIFO is below this setting, the tx_threshold interrupt will be asserted.                                                                                        |

## HOST_FIFO_STATUS
Host mode FIFO status register
- Offset: `0x2c`
- Reset default: `0x0`
- Reset mask: `0xfff0fff`

### Fields

```wavejson
{"reg": [{"name": "FMTLVL", "bits": 12, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "RXLVL", "bits": 12, "attr": ["ro"], "rotate": 0}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                    |
|:------:|:------:|:-------:|:-------|:-------------------------------|
| 31:28  |        |         |        | Reserved                       |
| 27:16  |   ro   |    x    | RXLVL  | Current fill level of RX fifo  |
| 15:12  |        |         |        | Reserved                       |
|  11:0  |   ro   |    x    | FMTLVL | Current fill level of FMT fifo |

## TARGET_FIFO_STATUS
Target mode FIFO status register
- Offset: `0x30`
- Reset default: `0x0`
- Reset mask: `0xfff0fff`

### Fields

```wavejson
{"reg": [{"name": "TXLVL", "bits": 12, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "ACQLVL", "bits": 12, "attr": ["ro"], "rotate": 0}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                    |
|:------:|:------:|:-------:|:-------|:-------------------------------|
| 31:28  |        |         |        | Reserved                       |
| 27:16  |   ro   |    x    | ACQLVL | Current fill level of ACQ fifo |
| 15:12  |        |         |        | Reserved                       |
|  11:0  |   ro   |    x    | TXLVL  | Current fill level of TX fifo  |

## OVRD
I2C Override Control Register
- Offset: `0x34`
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
- Offset: `0x38`
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
- Offset: `0x3c`
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
- Offset: `0x40`
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
- Offset: `0x44`
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
- Offset: `0x48`
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
- Offset: `0x4c`
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
I2C clock stretching timeout control.
This is used in I2C host mode to detect whether a connected target is stretching for too long.
- Offset: `0x50`
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
- Offset: `0x54`
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
- Offset: `0x58`
- Reset default: `0x0`
- Reset mask: `0x7ff`

### Fields

```wavejson
{"reg": [{"name": "ABYTE", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "SIGNAL", "bits": 3, "attr": ["ro"], "rotate": -90}, {"bits": 21}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                       |
|:------:|:------:|:-------:|:---------------------------|
| 31:11  |        |         | Reserved                   |
|  10:8  |   ro   |    x    | [SIGNAL](#acqdata--signal) |
|  7:0   |   ro   |    x    | [ABYTE](#acqdata--abyte)   |

### ACQDATA . SIGNAL
Host issued a START before transmitting ABYTE, a STOP or a RESTART after the preceeding ABYTE

| Value   | Name      | Description                                                                                                                                              |
|:--------|:----------|:---------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0x0     | NONE      | ABYTE contains ordinary data byte as received                                                                                                            |
| 0x1     | START     | ABYTE contains the 8-bit I2C address (R/W in lsb)                                                                                                        |
| 0x2     | STOP      | ABYTE contains junk                                                                                                                                      |
| 0x3     | RESTART   | ABYTE contains junk, START with address will follow                                                                                                      |
| 0x4     | NACK      | ABYTE contains either the address or data that was NACK'ed                                                                                               |
| 0x5     | NACKSTART | ABYTE contains the I2C address which was ACK'ed, but the block will continue and NACK the next data byte that was received: this only happens for writes |

Other values are reserved.

### ACQDATA . ABYTE
Address for accepted transaction or acquired byte

## TXDATA
I2C target transmit data
- Offset: `0x5c`
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
I2C host clock generation timeout value (in units of input clock frequency).

In an active transaction in Target-Mode, if the Controller ceases to send SCL pulses
for this number of cycles then the "host_timeout" interrupt will be asserted.

Set this CSR to 0 to disable this behaviour.
- Offset: `0x60`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "HOST_TIMEOUT_CTRL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name              | Description   |
|:------:|:------:|:-------:|:------------------|:--------------|
|  31:0  |   rw   |   0x0   | HOST_TIMEOUT_CTRL |               |

## TARGET_TIMEOUT_CTRL
I2C target internal stretching timeout control.
When the target has stretched beyond this time it will send a NACK.
- Offset: `0x64`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 31, "attr": ["rw"], "rotate": 0}, {"name": "EN", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                            |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------|
|   31   |   rw   |   0x0   | EN     | Enable timeout feature and send NACK once the timeout has been reached |
|  30:0  |   rw   |   0x0   | VAL    | Clock stretching timeout value (in units of input clock frequency)     |

## TARGET_NACK_COUNT
Number of times the I2C target has NACK'ed a new transaction since the last read of this register.
Reading this register clears it.
This is useful because when the ACQ FIFO is full the software know that a NACK has occurred, but without this register would not know how many transactions it missed.
When it reaches its maximum value it will stay at that value.
- Offset: `0x68`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "TARGET_NACK_COUNT", "bits": 8, "attr": ["rc"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name              | Description   |
|:------:|:------:|:-------:|:------------------|:--------------|
|  31:8  |        |         |                   | Reserved      |
|  7:0   |   rc   |   0x0   | TARGET_NACK_COUNT |               |

## HOST_NACK_HANDLER_TIMEOUT
Timeout in Host-Mode for an unhandled NACK before hardware automatically ends the transaction.
(in units of input clock frequency)

In Host-Mode during an active Controller-Transmitter transfer, if the Target NACKs a byte
the 'nak' interrupt is asserted and the Byte-Formatted Programming Mode FSM halts awaiting
software intervention. Software must acknowledge the interrupt (CIP 'Event-Type') to allow
the state machine to continue, typically after clearing out the FMTFIFO to start a new transfer.
While halted, the active transaction is not ended (no STOP (P) condition is created), and the
block releases both SCL and SDA.

This timeout can be used to automatically disable the block if software does not handle the
'nak' interrupt in a timely manner. If the timeout expires, ([`CTRL.HOSTMODE`](#ctrl)) will be disabled
which creates a STOP (P) condition on the bus ending the active transaction. Additionally, the
[`STATUS.HOST_DISABLED_NACK_TIMEOUT`](#status) bit is set to alert software.

The enable bit must be set for this feature to operate.
- Offset: `0x6c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 31, "attr": ["rw"], "rotate": 0}, {"name": "EN", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                     |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------|
|   31   |   rw   |   0x0   | EN     | Timeout enable                                                  |
|  30:0  |   rw   |   0x0   | VAL    | Unhandled NAK timeout value (in units of input clock frequency) |


<!-- END CMDGEN -->
