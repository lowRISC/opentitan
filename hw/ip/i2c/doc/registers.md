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
| i2c.[`TARGET_ACK_CTRL`](#target_ack_ctrl)                     | 0x6c     |        4 | Controls for mid-transfer (N)ACK phase handling                                                    |
| i2c.[`ACQ_FIFO_NEXT_DATA`](#acq_fifo_next_data)               | 0x70     |        4 | The data byte pending to be written to the ACQ FIFO.                                               |
| i2c.[`HOST_NACK_HANDLER_TIMEOUT`](#host_nack_handler_timeout) | 0x74     |        4 | Timeout in Host-Mode for an unhandled NACK before hardware automatically ends the transaction.     |
| i2c.[`CONTROLLER_EVENTS`](#controller_events)                 | 0x78     |        4 | Latched events that explain why the controller halted.                                             |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x7fff`

### Fields

```wavejson
{"reg": [{"name": "fmt_threshold", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "rx_threshold", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "acq_threshold", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "rx_overflow", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "controller_halt", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "scl_interference", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "sda_interference", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "stretch_timeout", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "sda_unstable", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "cmd_complete", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "tx_stretch", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "tx_threshold", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "acq_stretch", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "unexp_stop", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "host_timeout", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 17}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                                                                                                                                                                                                                        |
|:------:|:------:|:-------:|:-----------------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:15  |        |         |                  | Reserved                                                                                                                                                                                                                                                           |
|   14   |  rw1c  |   0x0   | host_timeout     | target mode interrupt: raised if the host stops sending the clock during an ongoing transaction.                                                                                                                                                                   |
|   13   |  rw1c  |   0x0   | unexp_stop       | target mode interrupt: raised if STOP is received without a preceding NACK during an external host read.                                                                                                                                                           |
|   12   |   ro   |   0x0   | acq_stretch      | target mode interrupt: raised if the target is stretching clocks due to full ACQ FIFO or zero count in [`TARGET_ACK_CTRL.NBYTES`](#target_ack_ctrl) (if enabled). This is a level status interrupt.                                                                |
|   11   |   ro   |   0x0   | tx_threshold     | target mode interrupt: asserted whilst the TX FIFO level is below the low threshold. This is a level status interrupt.                                                                                                                                             |
|   10   |   ro   |   0x0   | tx_stretch       | target mode interrupt: raised if the target is stretching clocks for a read command. This is a level status interrupt.                                                                                                                                             |
|   9    |  rw1c  |   0x0   | cmd_complete     | host and target mode interrupt. In host mode, raised if the host issues a repeated START or terminates the transaction by issuing STOP. In target mode, raised if the external host issues a STOP or repeated START.                                               |
|   8    |  rw1c  |   0x0   | sda_unstable     | host mode interrupt: raised if the target does not assert a constant value of SDA during transmission.                                                                                                                                                             |
|   7    |  rw1c  |   0x0   | stretch_timeout  | host mode interrupt: raised if target stretches the clock beyond the allowed timeout period                                                                                                                                                                        |
|   6    |  rw1c  |   0x0   | sda_interference | host mode interrupt: raised if the SDA line goes low when host is trying to assert high                                                                                                                                                                            |
|   5    |  rw1c  |   0x0   | scl_interference | host mode interrupt: raised if the SCL line drops early (not supported without clock synchronization).                                                                                                                                                             |
|   4    |   ro   |   0x0   | controller_halt  | host mode interrupt: raised if the controller FSM is halted, such as on an unexpected NACK. Check [`CONTROLLER_EVENTS`](#controller_events) for the reason. The interrupt will be released when the bits in [`CONTROLLER_EVENTS`](#controller_events) are cleared. |
|   3    |  rw1c  |   0x0   | rx_overflow      | host mode interrupt: raised if the RX FIFO has overflowed.                                                                                                                                                                                                         |
|   2    |   ro   |   0x0   | acq_threshold    | target mode interrupt: asserted whilst the ACQ FIFO level is above the high threshold. This is a level status interrupt.                                                                                                                                           |
|   1    |   ro   |   0x0   | rx_threshold     | host mode interrupt: asserted whilst the RX FIFO level is above the high threshold. This is a level status interrupt.                                                                                                                                              |
|   0    |   ro   |   0x0   | fmt_threshold    | host mode interrupt: asserted whilst the FMT FIFO level is below the low threshold. This is a level status interrupt.                                                                                                                                              |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x7fff`

### Fields

```wavejson
{"reg": [{"name": "fmt_threshold", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rx_threshold", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "acq_threshold", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rx_overflow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "controller_halt", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "scl_interference", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "sda_interference", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "stretch_timeout", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "sda_unstable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "cmd_complete", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "tx_stretch", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "tx_threshold", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "acq_stretch", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "unexp_stop", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "host_timeout", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 17}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                                |
|:------:|:------:|:-------:|:-----------------|:---------------------------------------------------------------------------|
| 31:15  |        |         |                  | Reserved                                                                   |
|   14   |   rw   |   0x0   | host_timeout     | Enable interrupt when [`INTR_STATE.host_timeout`](#intr_state) is set.     |
|   13   |   rw   |   0x0   | unexp_stop       | Enable interrupt when [`INTR_STATE.unexp_stop`](#intr_state) is set.       |
|   12   |   rw   |   0x0   | acq_stretch      | Enable interrupt when [`INTR_STATE.acq_stretch`](#intr_state) is set.      |
|   11   |   rw   |   0x0   | tx_threshold     | Enable interrupt when [`INTR_STATE.tx_threshold`](#intr_state) is set.     |
|   10   |   rw   |   0x0   | tx_stretch       | Enable interrupt when [`INTR_STATE.tx_stretch`](#intr_state) is set.       |
|   9    |   rw   |   0x0   | cmd_complete     | Enable interrupt when [`INTR_STATE.cmd_complete`](#intr_state) is set.     |
|   8    |   rw   |   0x0   | sda_unstable     | Enable interrupt when [`INTR_STATE.sda_unstable`](#intr_state) is set.     |
|   7    |   rw   |   0x0   | stretch_timeout  | Enable interrupt when [`INTR_STATE.stretch_timeout`](#intr_state) is set.  |
|   6    |   rw   |   0x0   | sda_interference | Enable interrupt when [`INTR_STATE.sda_interference`](#intr_state) is set. |
|   5    |   rw   |   0x0   | scl_interference | Enable interrupt when [`INTR_STATE.scl_interference`](#intr_state) is set. |
|   4    |   rw   |   0x0   | controller_halt  | Enable interrupt when [`INTR_STATE.controller_halt`](#intr_state) is set.  |
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
{"reg": [{"name": "fmt_threshold", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rx_threshold", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "acq_threshold", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rx_overflow", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "controller_halt", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "scl_interference", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "sda_interference", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "stretch_timeout", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "sda_unstable", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "cmd_complete", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "tx_stretch", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "tx_threshold", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "acq_stretch", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "unexp_stop", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "host_timeout", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 17}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                         |
|:------:|:------:|:-------:|:-----------------|:--------------------------------------------------------------------|
| 31:15  |        |         |                  | Reserved                                                            |
|   14   |   wo   |   0x0   | host_timeout     | Write 1 to force [`INTR_STATE.host_timeout`](#intr_state) to 1.     |
|   13   |   wo   |   0x0   | unexp_stop       | Write 1 to force [`INTR_STATE.unexp_stop`](#intr_state) to 1.       |
|   12   |   wo   |   0x0   | acq_stretch      | Write 1 to force [`INTR_STATE.acq_stretch`](#intr_state) to 1.      |
|   11   |   wo   |   0x0   | tx_threshold     | Write 1 to force [`INTR_STATE.tx_threshold`](#intr_state) to 1.     |
|   10   |   wo   |   0x0   | tx_stretch       | Write 1 to force [`INTR_STATE.tx_stretch`](#intr_state) to 1.       |
|   9    |   wo   |   0x0   | cmd_complete     | Write 1 to force [`INTR_STATE.cmd_complete`](#intr_state) to 1.     |
|   8    |   wo   |   0x0   | sda_unstable     | Write 1 to force [`INTR_STATE.sda_unstable`](#intr_state) to 1.     |
|   7    |   wo   |   0x0   | stretch_timeout  | Write 1 to force [`INTR_STATE.stretch_timeout`](#intr_state) to 1.  |
|   6    |   wo   |   0x0   | sda_interference | Write 1 to force [`INTR_STATE.sda_interference`](#intr_state) to 1. |
|   5    |   wo   |   0x0   | scl_interference | Write 1 to force [`INTR_STATE.scl_interference`](#intr_state) to 1. |
|   4    |   wo   |   0x0   | controller_halt  | Write 1 to force [`INTR_STATE.controller_halt`](#intr_state) to 1.  |
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
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "ENABLEHOST", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ENABLETARGET", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "LLPBK", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "NACK_ADDR_AFTER_TIMEOUT", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ACK_CTRL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 250}}
```

|  Bits  |  Type  |  Reset  | Name                                                      |
|:------:|:------:|:-------:|:----------------------------------------------------------|
|  31:5  |        |         | Reserved                                                  |
|   4    |   rw   |   0x0   | [ACK_CTRL_EN](#ctrl--ack_ctrl_en)                         |
|   3    |   rw   |   0x0   | [NACK_ADDR_AFTER_TIMEOUT](#ctrl--nack_addr_after_timeout) |
|   2    |   rw   |   0x0   | [LLPBK](#ctrl--llpbk)                                     |
|   1    |   rw   |   0x0   | [ENABLETARGET](#ctrl--enabletarget)                       |
|   0    |   rw   |   0x0   | [ENABLEHOST](#ctrl--enablehost)                           |

### CTRL . ACK_CTRL_EN
Enable I2C Target ACK Control Mode.

ACK Control Mode works together with [`TARGET_ACK_CTRL.NBYTES`](#target_ack_ctrl) to allow software to control upper-layer protocol (N)ACKing (e.g. as in SMBus).
This bit enables the mode when 1, and [`TARGET_ACK_CTRL.NBYTES`](#target_ack_ctrl) limits how many bytes may be automatically ACK'd while the ACQ FIFO has space.
If it is 0, the decision to ACK or NACK is made only from stretching timeouts and [`CTRL.NACK_ADDR_AFTER_TIMEOUT.`](#ctrl)

### CTRL . NACK_ADDR_AFTER_TIMEOUT
Enable NACKing the address on a stretch timeout.

This is a Target mode feature.
If enabled (1), a stretch timeout will cause the device to NACK the address byte.
If disabled (0), a stretch timeout will cause the device to ACK the address byte.
SMBus requires that devices always ACK their address, even for read commands.
However, non-SMBus protocols may have a different approach and can choose to NACK instead.

Note that both cases handle data bytes the same way.
For writes, the Target module will NACK all subsequent data bytes until it receives a Stop.
For reads, the Target module will release SDA, causing 0xff to be returned for all data bytes until it receives a Stop.

### CTRL . LLPBK
Enable I2C line loopback test
If line loopback is enabled, the internal design sees ACQ and RX data as "1"

### CTRL . ENABLETARGET
Enable Target I2C functionality

### CTRL . ENABLEHOST
Enable Host I2C functionality

## STATUS
I2C Live Status Register for Host and Target modes
- Offset: `0x14`
- Reset default: `0x33c`
- Reset mask: `0x7ff`

### Fields

```wavejson
{"reg": [{"name": "FMTFULL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "RXFULL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FMTEMPTY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "HOSTIDLE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TARGETIDLE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "RXEMPTY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TXFULL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ACQFULL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TXEMPTY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ACQEMPTY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ACK_CTRL_STRETCH", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 21}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                                                                              |
|:------:|:------:|:-------:|:-----------------|:---------------------------------------------------------------------------------------------------------|
| 31:11  |        |         |                  | Reserved                                                                                                 |
|   10   |   ro   |    x    | ACK_CTRL_STRETCH | Target mode stretching at (N)ACK phase due to zero count in [`TARGET_ACK_CTRL.NBYTES`](#target_ack_ctrl) |
|   9    |   ro   |   0x1   | ACQEMPTY         | Target mode receive FIFO is empty                                                                        |
|   8    |   ro   |   0x1   | TXEMPTY          | Target mode TX FIFO is empty                                                                             |
|   7    |   ro   |    x    | ACQFULL          | Target mode receive FIFO is full                                                                         |
|   6    |   ro   |    x    | TXFULL           | Target mode TX FIFO is full                                                                              |
|   5    |   ro   |   0x1   | RXEMPTY          | Host mode RX FIFO is empty                                                                               |
|   4    |   ro   |   0x1   | TARGETIDLE       | Target functionality is idle. No Target transaction is in progress                                       |
|   3    |   ro   |   0x1   | HOSTIDLE         | Host functionality is idle. No Host transaction is in progress                                           |
|   2    |   ro   |   0x1   | FMTEMPTY         | Host mode FMT FIFO is empty                                                                              |
|   1    |   ro   |    x    | RXFULL           | Host mode RX FIFO is full                                                                                |
|   0    |   ro   |    x    | FMTFULL          | Host mode FMT FIFO is full                                                                               |

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
Indicates any control symbols associated with the ABYTE.

For the STOP symbol, a stretch timeout will cause a NACK_STOP to appear in the ACQ FIFO.
If the ACQ FIFO doesn't have enough space to record a START and a STOP, the transaction will be dropped entirely on a stretch timeout.
In that case, the START byte will not appear (neither as START nor NACK_START), but a standalone NACK_STOP may, if there was space.
Software can discard any standalone NACK_STOP that appears.

See the associated values for more information about the contents.

| Value   | Name       | Description                                                                                                                                                                                                                       |
|:--------|:-----------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0x0     | NONE       | ABYTE contains an ordinary data byte that was received and ACK'd.                                                                                                                                                                 |
| 0x1     | START      | A START condition preceded the ABYTE to start a new transaction. ABYTE contains the 7-bit I2C address plus R/W command bit in the order received on the bus, MSB first.                                                           |
| 0x2     | STOP       | A STOP condition was received for a transaction including a transfer that addressed this Target. No transfers addressing this Target in that transaction were NACK'd. ABYTE contains no data.                                     |
| 0x3     | RESTART    | A repeated START condition preceded the ABYTE, extending the current transaction with a new transfer. ABYTE contains the 7-bit I2C address plus R/W command bit in the order received on the bus, MSB first.                      |
| 0x4     | NACK       | ABYTE contains an ordinary data byte that was received and NACK'd.                                                                                                                                                                |
| 0x5     | NACK_START | A START condition preceded the ABYTE (including repeated START) that was part of a NACK'd transer. The ABYTE contains the matching I2C address and command bit. The ABYTE was ACK'd, but the rest of the transaction was NACK'ed. |
| 0x6     | NACK_STOP  | A STOP condition was received for a transaction including a transfer that addressed this Target. A transfer addressing this Target was NACK'd. ABYTE contains no data.                                                            |

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
When the target has stretched beyond this time it will send a NACK for incoming data bytes or release SDA for outgoing data bytes.
The behavior for the address byte is configurable via [`CTRL.ACK_ADDR_AFTER_TIMEOUT.`](#ctrl)
Note that the count accumulates stretching time over the course of a transaction.
In other words, this is equivalent to the SMBus cumulative target clock extension time.
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

## TARGET_ACK_CTRL
Controls for mid-transfer (N)ACK phase handling
- Offset: `0x6c`
- Reset default: `0x0`
- Reset mask: `0x800001ff`

### Fields

```wavejson
{"reg": [{"name": "NBYTES", "bits": 9, "attr": ["rw"], "rotate": 0}, {"bits": 22}, {"name": "NACK", "bits": 1, "attr": ["wo"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                               |
|:------:|:------:|:-------:|:-----------------------------------|
|   31   |   wo   |    x    | [NACK](#target_ack_ctrl--nack)     |
|  30:9  |        |         | Reserved                           |
|  8:0   |   rw   |    x    | [NBYTES](#target_ack_ctrl--nbytes) |

### TARGET_ACK_CTRL . NACK
When the Target module stretches on the (N)ACK phase of a Write due to [`TARGET_ACK_CTRL.NBYTES`](#target_ack_ctrl) being 0, writing a 1 here will cause it to send a NACK.

If software chooses to NACK, note that the NACKing behavior is the same as if a stretch timeout occurred.
The rest of the transaction will be NACK'd, including subsequent transfers.
For the address byte, the (N)ACK phase of subsequent transfers will follow the behavior specified by [`CTRL.NACK_ADDR_AFTER_TIMEOUT.`](#ctrl)

Automatically clears to 0.

### TARGET_ACK_CTRL . NBYTES
Remaining number of bytes the Target module may ACK automatically.

If [`CTRL.ACK_CTRL_EN`](#ctrl) is set to 1, the Target module will stretch the clock at the (N)ACK phase of a byte if this CSR is 0, awaiting software's instructions.

At the beginning of each Write transfer, this byte count is reset to 0.
Writes to this CSR also are only accepted while the Target module is stretching the clock.
The Target module will always ACK its address if the ACQ FIFO has space.
For data bytes afterwards, it will stop at the (N)ACK phase and stretch the clock when this CSR is 0.
For each data byte that is ACK'd in a transaction, the byte count will decrease by 1.

Note that a full ACQ FIFO can still cause the Target module to halt at the beginning of a new byte.
The ACK Control Mode provides an additional synchronization point, during the (N)ACK phase instead of after.
For both cases, [`TARGET_TIMEOUT_CTRL`](#target_timeout_ctrl) applies, and stretching past the timeout will produce an automatic NACK.

This mode can be used to implement the mid-transfer (N)ACK responses required by various SMBus protocols.

## ACQ_FIFO_NEXT_DATA
The data byte pending to be written to the ACQ FIFO.

This CSR is only valid while the Target module is stretching in the (N)ACK phase, indicated by [`STATUS.ACK_CTRL_STRETCH`](#status) .
It is intended to be used with ACK Control Mode, so software may check the current byte.
- Offset: `0x70`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "ACQ_FIFO_NEXT_DATA", "bits": 8, "attr": ["ro"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description   |
|:------:|:------:|:-------:|:-------------------|:--------------|
|  31:8  |        |         |                    | Reserved      |
|  7:0   |   ro   |    x    | ACQ_FIFO_NEXT_DATA |               |

## HOST_NACK_HANDLER_TIMEOUT
Timeout in Host-Mode for an unhandled NACK before hardware automatically ends the transaction.
(in units of input clock frequency)

If an active Controller-Transmitter transfer receives a NACK from the Target, the [`CONTROLLER_EVENTS.NACK`](#controller_events) bit is set.
In turn, this causes the Controller FSM to halt awaiting software intervention, and the 'controller_halt' interrupt may assert.
Software must clear the [`CONTROLLER_EVENTS.NACK`](#controller_events) bit to allow the state machine to continue, typically after clearing out the FMTFIFO to start a new transfer.
While halted, the active transaction is not ended (no STOP (P) condition is created), and the block asserts SCL and leaves SDA released.

This timeout can be used to automatically produce a STOP condition, whether as a backstop for slow software responses (longer timeout) or as a convenience (short timeout).
If the timeout expires, the Controller FSM will issue a STOP (P) condition on the bus to end the active transaction.
Additionally, the [`CONTROLLER_EVENTS.UNHANDLED_NACK_TIMEOUT`](#controller_events) bit is set to alert software, and the FSM will return to the idle state and halt until the bit is cleared.

The enable bit must be set for this feature to operate.
- Offset: `0x74`
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

## CONTROLLER_EVENTS
Latched events that explain why the controller halted.

Any bits that are set must be written (with a 1) to clear the CONTROLLER_HALT interrupt.
- Offset: `0x78`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "NACK", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "UNHANDLED_NACK_TIMEOUT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 240}}
```

|  Bits  |  Type  |  Reset  | Name                   | Description                                                                                                               |
|:------:|:------:|:-------:|:-----------------------|:--------------------------------------------------------------------------------------------------------------------------|
|  31:2  |        |         |                        | Reserved                                                                                                                  |
|   1    |  rw1c  |   0x0   | UNHANDLED_NACK_TIMEOUT | A Host-Mode active transaction has been ended by the [`HOST_NACK_HANDLER_TIMEOUT`](#host_nack_handler_timeout) mechanism. |
|   0    |  rw1c  |   0x0   | NACK                   | Received an unexpected NACK                                                                                               |


<!-- END CMDGEN -->
