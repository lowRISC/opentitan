# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/spi_host/data/spi_host.hjson -->
## Summary

| Name                                     | Offset   |   Length | Description                                              |
|:-----------------------------------------|:---------|---------:|:---------------------------------------------------------|
| spi_host.[`INTR_STATE`](#intr_state)     | 0x0      |        4 | Interrupt State Register                                 |
| spi_host.[`INTR_ENABLE`](#intr_enable)   | 0x4      |        4 | Interrupt Enable Register                                |
| spi_host.[`INTR_TEST`](#intr_test)       | 0x8      |        4 | Interrupt Test Register                                  |
| spi_host.[`ALERT_TEST`](#alert_test)     | 0xc      |        4 | Alert Test Register                                      |
| spi_host.[`CONTROL`](#control)           | 0x10     |        4 | Control register                                         |
| spi_host.[`STATUS`](#status)             | 0x14     |        4 | Status register                                          |
| spi_host.[`CONFIGOPTS`](#configopts)     | 0x18     |        4 | Configuration options register.                          |
| spi_host.[`CSID`](#csid)                 | 0x1c     |        4 | Chip-Select ID                                           |
| spi_host.[`COMMAND`](#command)           | 0x20     |        4 | Command Register                                         |
| spi_host.[`RXDATA`](#rxdata)             | 0x24     |        4 | SPI Receive Data.                                        |
| spi_host.[`TXDATA`](#txdata)             | 0x28     |        4 | SPI Transmit Data.                                       |
| spi_host.[`ERROR_ENABLE`](#error_enable) | 0x2c     |        4 | Controls which classes of errors raise an interrupt.     |
| spi_host.[`ERROR_STATUS`](#error_status) | 0x30     |        4 | Indicates that any errors that have occurred.            |
| spi_host.[`EVENT_ENABLE`](#event_enable) | 0x34     |        4 | Controls which classes of SPI events raise an interrupt. |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "error", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "spi_event", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                                                     |
|:------:|:------:|:-------:|:----------|:------------------------------------------------------------------------------------------------|
|  31:2  |        |         |           | Reserved                                                                                        |
|   1    |  rw1c  |   0x0   | spi_event | Event-related interrupts, see [`EVENT_ENABLE`](#event_enable) register for more    information. |
|   0    |  rw1c  |   0x0   | error     | Error-related interrupts, see [`ERROR_ENABLE`](#error_enable) register for more    information. |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "error", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "spi_event", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                         |
|:------:|:------:|:-------:|:----------|:--------------------------------------------------------------------|
|  31:2  |        |         |           | Reserved                                                            |
|   1    |   rw   |   0x0   | spi_event | Enable interrupt when [`INTR_STATE.spi_event`](#intr_state) is set. |
|   0    |   rw   |   0x0   | error     | Enable interrupt when [`INTR_STATE.error`](#intr_state) is set.     |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "error", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "spi_event", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                  |
|:------:|:------:|:-------:|:----------|:-------------------------------------------------------------|
|  31:2  |        |         |           | Reserved                                                     |
|   1    |   wo   |   0x0   | spi_event | Write 1 to force [`INTR_STATE.spi_event`](#intr_state) to 1. |
|   0    |   wo   |   0x0   | error     | Write 1 to force [`INTR_STATE.error`](#intr_state) to 1.     |

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
- Reset default: `0x7f`
- Reset mask: `0xe000ffff`

### Fields

```wavejson
{"reg": [{"name": "RX_WATERMARK", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "TX_WATERMARK", "bits": 8, "attr": ["rw"], "rotate": 0}, {"bits": 13}, {"name": "OUTPUT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "SW_RST", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "SPIEN", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name                                   |
|:------:|:------:|:-------:|:---------------------------------------|
|   31   |   rw   |   0x0   | [SPIEN](#control--spien)               |
|   30   |   rw   |   0x0   | [SW_RST](#control--sw_rst)             |
|   29   |   rw   |   0x0   | [OUTPUT_EN](#control--output_en)       |
| 28:16  |        |         | Reserved                               |
|  15:8  |   rw   |   0x0   | [TX_WATERMARK](#control--tx_watermark) |
|  7:0   |   rw   |  0x7f   | [RX_WATERMARK](#control--rx_watermark) |

### CONTROL . SPIEN
Enables the SPI host.  On reset, this field is 0, meaning
   that no transactions can proceed.

### CONTROL . SW_RST
Clears the entire IP to the reset state when set to 1, including
   the FIFOs, the CDC's, the core state machine and the shift register.
   In the current implementation, the CDC FIFOs are drained not reset.
   Therefore software must confirm that both FIFO's empty before releasing
   the IP from reset.

### CONTROL . OUTPUT_EN
Enable the SPI host output buffers for the sck, csb, and sd lines.  This allows
   the SPI_HOST IP to connect to the same bus as other SPI controllers without
   interference.

### CONTROL . TX_WATERMARK
If [`EVENT_ENABLE.TXWM`](#event_enable) is set, the IP will send
   an interrupt when the depth of the TX FIFO drops below
   TX_WATERMARK words (32b each).

### CONTROL . RX_WATERMARK
If [`EVENT_ENABLE.RXWM`](#event_enable) is set, the IP will send
   an interrupt when the depth of the RX FIFO reaches
   RX_WATERMARK words (32b each).

## STATUS
Status register
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0xffdfffff`

### Fields

```wavejson
{"reg": [{"name": "TXQD", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "RXQD", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "CMDQD", "bits": 4, "attr": ["ro"], "rotate": 0}, {"name": "RXWM", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 1}, {"name": "BYTEORDER", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "RXSTALL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "RXEMPTY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "RXFULL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TXWM", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TXSTALL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TXEMPTY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TXFULL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ACTIVE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "READY", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name                            |
|:------:|:------:|:-------:|:--------------------------------|
|   31   |   ro   |   0x0   | [READY](#status--ready)         |
|   30   |   ro   |   0x0   | [ACTIVE](#status--active)       |
|   29   |   ro   |   0x0   | [TXFULL](#status--txfull)       |
|   28   |   ro   |   0x0   | [TXEMPTY](#status--txempty)     |
|   27   |   ro   |   0x0   | [TXSTALL](#status--txstall)     |
|   26   |   ro   |   0x0   | [TXWM](#status--txwm)           |
|   25   |   ro   |   0x0   | [RXFULL](#status--rxfull)       |
|   24   |   ro   |   0x0   | [RXEMPTY](#status--rxempty)     |
|   23   |   ro   |   0x0   | [RXSTALL](#status--rxstall)     |
|   22   |   ro   |   0x0   | [BYTEORDER](#status--byteorder) |
|   21   |        |         | Reserved                        |
|   20   |   ro   |   0x0   | [RXWM](#status--rxwm)           |
| 19:16  |   ro   |   0x0   | [CMDQD](#status--cmdqd)         |
|  15:8  |   ro   |   0x0   | [RXQD](#status--rxqd)           |
|  7:0   |   ro   |   0x0   | [TXQD](#status--txqd)           |

### STATUS . READY
When high, indicates the SPI host is ready to receive
   commands. Writing to COMMAND when READY is low is
   an error, and will trigger an interrupt.

### STATUS . ACTIVE
When high, indicates the SPI host is processing a previously
   issued command.

### STATUS . TXFULL
When high, indicates that the transmit data fifo is full.
   Any further writes to [`RXDATA`](#rxdata) will create an error interrupt.

### STATUS . TXEMPTY
When high, indicates that the transmit data fifo is empty.
   Note, one transmit item can be pending in the internal transmit datapath (inside the spi_host_byte_select module).
   This means the transmit data fifo is empty and TXEMTPY will be high, while there is still one packet that needs to be transmitted.

### STATUS . TXSTALL
If high, signifies that an ongoing transaction has stalled
   due to lack of data in the TX FIFO

### STATUS . TXWM
If high, the amount of data in the TX FIFO has fallen below the
   level of [`CONTROL.TX_WATERMARK`](#control) words (32b each).

### STATUS . RXFULL
When high, indicates that the receive fifo is full.  Any
   ongoing transactions will stall until firmware reads some
   data from [`RXDATA.`](#rxdata)

### STATUS . RXEMPTY
When high, indicates that the receive fifo is empty.
   Any reads from RX FIFO will cause an error interrupt.

### STATUS . RXSTALL
If high, signifies that an ongoing transaction has stalled
   due to lack of available space in the RX FIFO

### STATUS . BYTEORDER
The value of the ByteOrder parameter, provided so that firmware
   can confirm proper IP configuration.

### STATUS . RXWM
If high, the number of 32-bits in the RX FIFO now exceeds the
   [`CONTROL.RX_WATERMARK`](#control) entries (32b each).

### STATUS . CMDQD
Command queue depth. Indicates how many unread 32-bit words are
   currently in the command segment queue.

### STATUS . RXQD
Receive queue depth. Indicates how many unread 32-bit words are
   currently in the RX FIFO.  When active, this result may an
   underestimate due to synchronization delays.

### STATUS . TXQD
Transmit queue depth.
   Indicates how many unsent 32-bit words are currently in the TX FIFO.
   When active, this result may be an overestimate due to synchronization delays.
   It may also be an underestimate by 1 because of one pending transmit packet in the internal transmit datapath (inside the spi_host_byte_select module).

## CONFIGOPTS
Configuration options register.

   Contains options for controlling each peripheral. One register per
   cs_n line
- Reset default: `0x0`
- Reset mask: `0xefffffff`

### Instances

| Name       | Offset   |
|:-----------|:---------|
| CONFIGOPTS | 0x18     |


### Fields

```wavejson
{"reg": [{"name": "CLKDIV", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "CSNIDLE", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "CSNTRAIL", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "CSNLEAD", "bits": 4, "attr": ["rw"], "rotate": -90}, {"bits": 1}, {"name": "FULLCYC", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CPHA", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CPOL", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name                              |
|:------:|:------:|:-------:|:----------------------------------|
|   31   |   rw   |   0x0   | [CPOL](#configopts--cpol)         |
|   30   |   rw   |   0x0   | [CPHA](#configopts--cpha)         |
|   29   |   rw   |   0x0   | [FULLCYC](#configopts--fullcyc)   |
|   28   |        |         | Reserved                          |
| 27:24  |   rw   |   0x0   | [CSNLEAD](#configopts--csnlead)   |
| 23:20  |   rw   |   0x0   | [CSNTRAIL](#configopts--csntrail) |
| 19:16  |   rw   |   0x0   | [CSNIDLE](#configopts--csnidle)   |
|  15:0  |   rw   |   0x0   | [CLKDIV](#configopts--clkdiv)     |

### CONFIGOPTS . CPOL
The polarity of the sck clock signal.  When CPOL is 0,
   sck is low when idle, and emits high pulses.   When CPOL
   is 1, sck is high when idle, and emits a series of low
   pulses.

### CONFIGOPTS . CPHA
The phase of the sck clock signal relative to the data. When
   CPHA = 0, the data changes on the trailing edge of sck
   and is typically sampled on the leading edge.  Conversely
   if CPHA = 1 high, data lines change on the leading edge of
   sck and are typically sampled on the trailing edge.
   CPHA should be chosen to match the phase of the selected
   device.  The sampling behavior is modified by the
   [`CONFIGOPTS.FULLCYC`](#configopts) bit.

### CONFIGOPTS . FULLCYC
Full cycle.  Modifies the CPHA sampling behaviour to allow
   for longer device logic setup times.  Rather than sampling the SD
   bus a half cycle after shifting out data, the data is sampled
   a full cycle after shifting data out.  This means that if
   CPHA = 0, data is shifted out on the trailing edge, and
   sampled a full cycle later.  If CPHA = 1, data is shifted and
   sampled with the trailing edge, also separated by a
   full cycle.

### CONFIGOPTS . CSNLEAD
CS_N Leading Time.  Indicates the number of half sck cycles,
   CSNLEAD+1, to leave between the falling edge of cs_n and
   the first edge of sck.  Setting this register to zero
   corresponds to the minimum delay of one-half sck cycle

### CONFIGOPTS . CSNTRAIL
CS_N Trailing Time.  Indicates the number of half sck cycles,
   CSNTRAIL+1, to leave between last edge of sck and the rising
   edge of cs_n. Setting this register to zero corresponds
   to the minimum delay of one-half sck cycle.

### CONFIGOPTS . CSNIDLE
Minimum idle time between commands. Indicates the minimum
   number of sck half-cycles to hold cs_n high between commands.
   Setting this register to zero creates a minimally-wide CS_N-high
   pulse of one-half sck cycle.

### CONFIGOPTS . CLKDIV
Core clock divider.  Slows down subsequent SPI transactions by a
   factor of (CLKDIV+1) relative to the core clock frequency.  The
   period of sck, T(sck) then becomes `2*(CLK_DIV+1)*T(core)`

## CSID
Chip-Select ID

   Controls which device to target with the next command.  This register
   is passed to the core whenever [`COMMAND`](#command) is written.  The core then
   asserts cio_csb_o[[`CSID`](#csid)] during the execution of the command.
- Offset: `0x1c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "CSID", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description    |
|:------:|:------:|:-------:|:-------|:---------------|
|  31:0  |   rw   |   0x0   | CSID   | Chip Select ID |

## COMMAND
Command Register

   Parameters specific to each command segment.  Unlike the [`CONFIGOPTS`](#configopts) multi-register,
   there is only one command register for controlling all attached SPI devices
- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0x3fff`

### Fields

```wavejson
{"reg": [{"name": "LEN", "bits": 9, "attr": ["wo"], "rotate": 0}, {"name": "CSAAT", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "SPEED", "bits": 2, "attr": ["wo"], "rotate": -90}, {"name": "DIRECTION", "bits": 2, "attr": ["wo"], "rotate": -90}, {"bits": 18}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name                             |
|:------:|:------:|:-------:|:---------------------------------|
| 31:14  |        |         | Reserved                         |
| 13:12  |   wo   |   0x0   | [DIRECTION](#command--direction) |
| 11:10  |   wo   |   0x0   | [SPEED](#command--speed)         |
|   9    |   wo   |   0x0   | [CSAAT](#command--csaat)         |
|  8:0   |   wo   |   0x0   | [LEN](#command--len)             |

### COMMAND . DIRECTION
The direction for the following command: "0" = Dummy cycles
   (no TX/RX). "1" = Rx only, "2" = Tx only, "3" = Bidirectional
   Tx/Rx (Standard SPI mode only).

### COMMAND . SPEED
The speed for this command segment: "0" = Standard SPI. "1" = Dual SPI.
   "2"=Quad SPI,  "3": RESERVED.

### COMMAND . CSAAT
Chip select active after transaction.  If CSAAT = 0, the
   chip select line is raised immediately at the end of the
   command segment.   If [`COMMAND.CSAAT`](#command) = 1, the chip select
   line is left low at the end of the current transaction
   segment.  This allows the creation longer, more
   complete SPI transactions, consisting of several separate
   segments for issuing instructions, pausing for dummy cycles,
   and transmitting or receiving data from the device.

### COMMAND . LEN
Segment Length.

   For read or write segments, this field controls the
   number of 1-byte bursts to transmit and or receive in
   this command segment.  The number of cyles required
   to send or received a byte will depend on [`COMMAND.SPEED.`](#command)
   For dummy segments, ([`COMMAND.DIRECTION`](#command) == 0), this register
   controls the number of dummy cycles to issue.
   The number of bytes (or dummy cycles) in the segment will be
   equal to [`COMMAND.LEN`](#command) + 1.

## RXDATA
SPI Receive Data.

   Reads from this window pull data from the RXFIFO.

   The serial order of bit transmission
   is chosen to match SPI flash devices. Individual bytes
   are always transmitted with the most significant bit first.
   Only four-bute reads are supported. If ByteOrder = 0,
   the first byte received is packed in the MSB of !!RXDATA.
   For some processor architectures, this could lead to shuffling
   of flash data as compared to how it is written in memory.
   In which case, choosing ByteOrder = 1 can reverse the
   byte-order of each data read, causing the first byte
   received to be packed into the LSB of !!RXDATA. (Though within
   each byte the most significant bit is always pulled
   from the bus first.)

- Word Aligned Offset Range: `0x24`to`0x24`
- Size (words): `1`
- Access: `ro`
- Byte writes are *not* supported.

## TXDATA
SPI Transmit Data.

   Data written to this window is placed into the TXFIFO.
   Byte-enables are supported for writes.

   The serial order of bit transmission
   is chosen to match SPI flash devices. Individual bytes
   are always transmitted with the most significant bit first.
   Multi-byte writes are also supported, and if ByteOrder = 0,
   the bits of !!TXDATA are transmitted strictly in order of
   decreasing signficance (i.e. most signicant bit first).
   For some processor architectures, this could lead to shuffling
   of flash data as compared to how it is written in memory.
   In which case, choosing ByteOrder = 1 can reverse the
   byte-order of multi-byte data writes.  (Though within
   each byte the most significant bit is always sent first.)

- Word Aligned Offset Range: `0x28`to`0x28`
- Size (words): `1`
- Access: `wo`
- Byte writes are  supported.

## ERROR_ENABLE
Controls which classes of errors raise an interrupt.
- Offset: `0x2c`
- Reset default: `0x1f`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "CMDBUSY", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "OVERFLOW", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "UNDERFLOW", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CMDINVAL", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CSIDINVAL", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                                                                                                                                                             |
|:------:|:------:|:-------:|:----------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |           | Reserved                                                                                                                                                                                                |
|   4    |   rw   |   0x1   | CSIDINVAL | Invalid CSID: If this bit is set, the block sends an error interrupt whenever    a command is submitted, but CSID exceeds NumCS.                                                                        |
|   3    |   rw   |   0x1   | CMDINVAL  | Invalid Command Errors: If this bit is set, the block sends an    error interrupt whenever a command is sent with invalid values for    [`COMMAND.SPEED`](#command) or [`COMMAND.DIRECTION.`](#command) |
|   2    |   rw   |   0x1   | UNDERFLOW | Underflow Errors: If this bit is set, the block sends an    error interrupt whenever there is a read from [`RXDATA`](#rxdata)    but the RX FIFO is empty.                                              |
|   1    |   rw   |   0x1   | OVERFLOW  | Overflow Errors: If this bit is set, the block sends an    error interrupt whenever the TX FIFO overflows.                                                                                              |
|   0    |   rw   |   0x1   | CMDBUSY   | Command Error: If this bit is set, the block sends an error    interrupt whenever a command is issued while busy (i.e. a 1 is    when [`STATUS.READY`](#status) is not asserted.)                       |

## ERROR_STATUS
Indicates that any errors that have occurred.
   When an error
   occurs, the corresponding bit must be cleared here before
   issuing any further commands.
- Offset: `0x30`
- Reset default: `0x0`
- Reset mask: `0x3f`

### Fields

```wavejson
{"reg": [{"name": "CMDBUSY", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "OVERFLOW", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "UNDERFLOW", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "CMDINVAL", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "CSIDINVAL", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "ACCESSINVAL", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 26}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                                                                                                                                   |
|:------:|:------:|:-------:|:------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:6  |        |         |             | Reserved                                                                                                                                                                      |
|   5    |  rw1c  |   0x0   | ACCESSINVAL | Indicates that TLUL attempted to write to TXDATA with no bytes enabled. Such    'zero byte' writes are not supported.                                                         |
|   4    |  rw1c  |   0x0   | CSIDINVAL   | Indicates a command was attempted with an invalid value for [`CSID.`](#csid)                                                                                                  |
|   3    |  rw1c  |   0x0   | CMDINVAL    | Indicates an invalid command segment, meaning either an invalid value of    [`COMMAND.SPEED`](#command) or a request for bidirectional data transfer at dual or quad    speed |
|   2    |  rw1c  |   0x0   | UNDERFLOW   | Indicates that firmware has attempted to read from    [`RXDATA`](#rxdata) when the RX FIFO is empty.                                                                          |
|   1    |  rw1c  |   0x0   | OVERFLOW    | Indicates that firmware has overflowed the TX FIFO                                                                                                                            |
|   0    |  rw1c  |   0x0   | CMDBUSY     | Indicates a write to [`COMMAND`](#command) when [`STATUS.READY`](#status) = 0.                                                                                                |

## EVENT_ENABLE
Controls which classes of SPI events raise an interrupt.
- Offset: `0x34`
- Reset default: `0x0`
- Reset mask: `0x3f`

### Fields

```wavejson
{"reg": [{"name": "RXFULL", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TXEMPTY", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "RXWM", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TXWM", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "READY", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "IDLE", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 26}], "config": {"lanes": 1, "fontsize": 10, "vspace": 90}}
```

|  Bits  |  Type  |  Reset  | Name                              |
|:------:|:------:|:-------:|:----------------------------------|
|  31:6  |        |         | Reserved                          |
|   5    |   rw   |   0x0   | [IDLE](#event_enable--idle)       |
|   4    |   rw   |   0x0   | [READY](#event_enable--ready)     |
|   3    |   rw   |   0x0   | [TXWM](#event_enable--txwm)       |
|   2    |   rw   |   0x0   | [RXWM](#event_enable--rxwm)       |
|   1    |   rw   |   0x0   | [TXEMPTY](#event_enable--txempty) |
|   0    |   rw   |   0x0   | [RXFULL](#event_enable--rxfull)   |

### EVENT_ENABLE . IDLE
Assert to send a spi_event interrupt whenever [`STATUS.ACTIVE`](#status)
   goes low

### EVENT_ENABLE . READY
Assert to send a spi_event interrupt whenever [`STATUS.READY`](#status)
   goes high

### EVENT_ENABLE . TXWM
Assert to send a spi_event interrupt whenever the number of 32-bit words in
   the TX FIFO is less than [`CONTROL.TX_WATERMARK.`](#control)  To prevent the
   reassertion of this interrupt add more data to the TX FIFO, or
   reduce [`CONTROL.TX_WATERMARK.`](#control)

### EVENT_ENABLE . RXWM
Assert to send a spi_event interrupt whenever the number of 32-bit words in
   the RX FIFO is greater than [`CONTROL.RX_WATERMARK.`](#control) To prevent the
   reassertion of this interrupt, read more data from the RX FIFO, or
   increase [`CONTROL.RX_WATERMARK.`](#control)

### EVENT_ENABLE . TXEMPTY
Assert to send a spi_event interrupt whenever [`STATUS.TXEMPTY`](#status)
   goes high

### EVENT_ENABLE . RXFULL
Assert to send a spi_event interrupt whenever [`STATUS.RXFULL`](#status)
   goes high


<!-- END CMDGEN -->
