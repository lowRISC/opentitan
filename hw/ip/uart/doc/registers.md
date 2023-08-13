# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/uart/data/uart.hjson -->
## Summary

| Name                                 | Offset   |   Length | Description                                                        |
|:-------------------------------------|:---------|---------:|:-------------------------------------------------------------------|
| uart.[`INTR_STATE`](#intr_state)     | 0x0      |        4 | Interrupt State Register                                           |
| uart.[`INTR_ENABLE`](#intr_enable)   | 0x4      |        4 | Interrupt Enable Register                                          |
| uart.[`INTR_TEST`](#intr_test)       | 0x8      |        4 | Interrupt Test Register                                            |
| uart.[`ALERT_TEST`](#alert_test)     | 0xc      |        4 | Alert Test Register                                                |
| uart.[`CTRL`](#ctrl)                 | 0x10     |        4 | UART control register                                              |
| uart.[`STATUS`](#status)             | 0x14     |        4 | UART live status register                                          |
| uart.[`RDATA`](#rdata)               | 0x18     |        4 | UART read data                                                     |
| uart.[`WDATA`](#wdata)               | 0x1c     |        4 | UART write data                                                    |
| uart.[`FIFO_CTRL`](#fifo_ctrl)       | 0x20     |        4 | UART FIFO control register                                         |
| uart.[`FIFO_STATUS`](#fifo_status)   | 0x24     |        4 | UART FIFO status register                                          |
| uart.[`OVRD`](#ovrd)                 | 0x28     |        4 | TX pin override control. Gives direct SW control over TX pin state |
| uart.[`VAL`](#val)                   | 0x2c     |        4 | UART oversampled values                                            |
| uart.[`TIMEOUT_CTRL`](#timeout_ctrl) | 0x30     |        4 | UART RX timeout control                                            |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "tx_watermark", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "rx_watermark", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "tx_empty", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "rx_overflow", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "rx_frame_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "rx_break_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "rx_timeout", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "rx_parity_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                                                                    |
|:------:|:------:|:-------:|:--------------|:---------------------------------------------------------------------------------------------------------------|
|  31:8  |        |         |               | Reserved                                                                                                       |
|   7    |  rw1c  |   0x0   | rx_parity_err | raised if the receiver has detected a parity error.                                                            |
|   6    |  rw1c  |   0x0   | rx_timeout    | raised if RX FIFO has characters remaining in the FIFO without being retrieved for the programmed time period. |
|   5    |  rw1c  |   0x0   | rx_break_err  | raised if break condition has been detected on receive.                                                        |
|   4    |  rw1c  |   0x0   | rx_frame_err  | raised if a framing error has been detected on receive.                                                        |
|   3    |  rw1c  |   0x0   | rx_overflow   | raised if the receive FIFO has overflowed.                                                                     |
|   2    |  rw1c  |   0x0   | tx_empty      | raised if the transmit FIFO has emptied and no transmit is ongoing.                                            |
|   1    |  rw1c  |   0x0   | rx_watermark  | raised if the receive FIFO is past the high-water mark.                                                        |
|   0    |  rw1c  |   0x0   | tx_watermark  | raised if the transmit FIFO is past the high-water mark.                                                       |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "tx_watermark", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rx_watermark", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "tx_empty", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rx_overflow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rx_frame_err", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rx_break_err", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rx_timeout", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rx_parity_err", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                             |
|:------:|:------:|:-------:|:--------------|:------------------------------------------------------------------------|
|  31:8  |        |         |               | Reserved                                                                |
|   7    |   rw   |   0x0   | rx_parity_err | Enable interrupt when [`INTR_STATE.rx_parity_err`](#intr_state) is set. |
|   6    |   rw   |   0x0   | rx_timeout    | Enable interrupt when [`INTR_STATE.rx_timeout`](#intr_state) is set.    |
|   5    |   rw   |   0x0   | rx_break_err  | Enable interrupt when [`INTR_STATE.rx_break_err`](#intr_state) is set.  |
|   4    |   rw   |   0x0   | rx_frame_err  | Enable interrupt when [`INTR_STATE.rx_frame_err`](#intr_state) is set.  |
|   3    |   rw   |   0x0   | rx_overflow   | Enable interrupt when [`INTR_STATE.rx_overflow`](#intr_state) is set.   |
|   2    |   rw   |   0x0   | tx_empty      | Enable interrupt when [`INTR_STATE.tx_empty`](#intr_state) is set.      |
|   1    |   rw   |   0x0   | rx_watermark  | Enable interrupt when [`INTR_STATE.rx_watermark`](#intr_state) is set.  |
|   0    |   rw   |   0x0   | tx_watermark  | Enable interrupt when [`INTR_STATE.tx_watermark`](#intr_state) is set.  |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "tx_watermark", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rx_watermark", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "tx_empty", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rx_overflow", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rx_frame_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rx_break_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rx_timeout", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rx_parity_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                      |
|:------:|:------:|:-------:|:--------------|:-----------------------------------------------------------------|
|  31:8  |        |         |               | Reserved                                                         |
|   7    |   wo   |   0x0   | rx_parity_err | Write 1 to force [`INTR_STATE.rx_parity_err`](#intr_state) to 1. |
|   6    |   wo   |   0x0   | rx_timeout    | Write 1 to force [`INTR_STATE.rx_timeout`](#intr_state) to 1.    |
|   5    |   wo   |   0x0   | rx_break_err  | Write 1 to force [`INTR_STATE.rx_break_err`](#intr_state) to 1.  |
|   4    |   wo   |   0x0   | rx_frame_err  | Write 1 to force [`INTR_STATE.rx_frame_err`](#intr_state) to 1.  |
|   3    |   wo   |   0x0   | rx_overflow   | Write 1 to force [`INTR_STATE.rx_overflow`](#intr_state) to 1.   |
|   2    |   wo   |   0x0   | tx_empty      | Write 1 to force [`INTR_STATE.tx_empty`](#intr_state) to 1.      |
|   1    |   wo   |   0x0   | rx_watermark  | Write 1 to force [`INTR_STATE.rx_watermark`](#intr_state) to 1.  |
|   0    |   wo   |   0x0   | tx_watermark  | Write 1 to force [`INTR_STATE.tx_watermark`](#intr_state) to 1.  |

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
UART control register
- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0xffff03f7`

### Fields

```wavejson
{"reg": [{"name": "TX", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "RX", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "NF", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 1}, {"name": "SLPBK", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "LLPBK", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "PARITY_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "PARITY_ODD", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "RXBLVL", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 6}, {"name": "NCO", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name                            |
|:------:|:------:|:-------:|:--------------------------------|
| 31:16  |   rw   |   0x0   | [NCO](#ctrl--nco)               |
| 15:10  |        |         | Reserved                        |
|  9:8   |   rw   |   0x0   | [RXBLVL](#ctrl--rxblvl)         |
|   7    |   rw   |   0x0   | [PARITY_ODD](#ctrl--parity_odd) |
|   6    |   rw   |   0x0   | [PARITY_EN](#ctrl--parity_en)   |
|   5    |   rw   |   0x0   | [LLPBK](#ctrl--llpbk)           |
|   4    |   rw   |   0x0   | [SLPBK](#ctrl--slpbk)           |
|   3    |        |         | Reserved                        |
|   2    |   rw   |   0x0   | [NF](#ctrl--nf)                 |
|   1    |   rw   |   0x0   | [RX](#ctrl--rx)                 |
|   0    |   rw   |   0x0   | [TX](#ctrl--tx)                 |

### CTRL . NCO
BAUD clock rate control.

### CTRL . RXBLVL
Trigger level for RX break detection. Sets the number of character
times the line must be low to detect a break.

| Value   | Name    | Description   |
|:--------|:--------|:--------------|
| 0x0     | break2  | 2 characters  |
| 0x1     | break4  | 4 characters  |
| 0x2     | break8  | 8 characters  |
| 0x3     | break16 | 16 characters |


### CTRL . PARITY_ODD
If PARITY_EN is true, this determines the type, 1 for odd parity, 0 for even.

### CTRL . PARITY_EN
If true, parity is enabled in both RX and TX directions.

### CTRL . LLPBK
Line loopback enable.

If this bit is turned on, incoming bits are forwarded to TX for testing purpose.
See Block Diagram. Note that the internal design sees RX value as 1 always if line
loopback is enabled.

### CTRL . SLPBK
System loopback enable.

If this bit is turned on, any outgoing bits to TX are received through RX.
See Block Diagram. Note that the TX line goes 1 if System loopback is enabled.

### CTRL . NF
RX noise filter enable.
If the noise filter is enabled, RX line goes through the 3-tap
repetition code. It ignores single IP clock period noise.

### CTRL . RX
RX enable

### CTRL . TX
TX enable

## STATUS
UART live status register
- Offset: `0x14`
- Reset default: `0x3c`
- Reset mask: `0x3f`

### Fields

```wavejson
{"reg": [{"name": "TXFULL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "RXFULL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TXEMPTY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TXIDLE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "RXIDLE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "RXEMPTY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 26}], "config": {"lanes": 1, "fontsize": 10, "vspace": 90}}
```

|  Bits  |  Type  |  Reset  | Name    | Description                                         |
|:------:|:------:|:-------:|:--------|:----------------------------------------------------|
|  31:6  |        |         |         | Reserved                                            |
|   5    |   ro   |   0x1   | RXEMPTY | RX FIFO is empty                                    |
|   4    |   ro   |   0x1   | RXIDLE  | RX is idle                                          |
|   3    |   ro   |   0x1   | TXIDLE  | TX FIFO is empty and all bits have been transmitted |
|   2    |   ro   |   0x1   | TXEMPTY | TX FIFO is empty                                    |
|   1    |   ro   |    x    | RXFULL  | RX buffer is full                                   |
|   0    |   ro   |    x    | TXFULL  | TX buffer is full                                   |

## RDATA
UART read data
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

## WDATA
UART write data
- Offset: `0x1c`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "WDATA", "bits": 8, "attr": ["wo"], "rotate": 0}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:8  |        |         |        | Reserved      |
|  7:0   |   wo   |   0x0   | WDATA  |               |

## FIFO_CTRL
UART FIFO control register
- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "RXRST", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "TXRST", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "RXILVL", "bits": 3, "attr": ["rw"], "rotate": -90}, {"name": "TXILVL", "bits": 3, "attr": ["rw"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                         |
|:------:|:------:|:-------:|:-----------------------------|
|  31:8  |        |         | Reserved                     |
|  7:5   |   rw   |   0x0   | [TXILVL](#fifo_ctrl--txilvl) |
|  4:2   |   rw   |   0x0   | [RXILVL](#fifo_ctrl--rxilvl) |
|   1    |   wo   |   0x0   | [TXRST](#fifo_ctrl--txrst)   |
|   0    |   wo   |   0x0   | [RXRST](#fifo_ctrl--rxrst)   |

### FIFO_CTRL . TXILVL
Trigger level for TX interrupts. If the FIFO depth is less than the setting, it
raises tx_watermark interrupt.

| Value   | Name    | Description   |
|:--------|:--------|:--------------|
| 0x0     | txlvl1  | 1 character   |
| 0x1     | txlvl2  | 2 characters  |
| 0x2     | txlvl4  | 4 characters  |
| 0x3     | txlvl8  | 8 characters  |
| 0x4     | txlvl16 | 16 characters |
| 0x5     | txlvl32 | 32 characters |
| 0x6     | txlvl64 | 64 characters |

Other values are reserved.

### FIFO_CTRL . RXILVL
Trigger level for RX interrupts. If the FIFO depth is greater than or equal to
the setting, it raises rx_watermark interrupt.

| Value   | Name     | Description    |
|:--------|:---------|:---------------|
| 0x0     | rxlvl1   | 1 character    |
| 0x1     | rxlvl2   | 2 characters   |
| 0x2     | rxlvl4   | 4 characters   |
| 0x3     | rxlvl8   | 8 characters   |
| 0x4     | rxlvl16  | 16 characters  |
| 0x5     | rxlvl32  | 32 characters  |
| 0x6     | rxlvl64  | 64 characters  |
| 0x7     | rxlvl126 | 126 characters |


### FIFO_CTRL . TXRST
TX fifo reset. Write 1 to the register resets TX_FIFO. Read returns 0

### FIFO_CTRL . RXRST
RX fifo reset. Write 1 to the register resets RX_FIFO. Read returns 0

## FIFO_STATUS
UART FIFO status register
- Offset: `0x24`
- Reset default: `0x0`
- Reset mask: `0xff00ff`

### Fields

```wavejson
{"reg": [{"name": "TXLVL", "bits": 8, "attr": ["ro"], "rotate": 0}, {"bits": 8}, {"name": "RXLVL", "bits": 8, "attr": ["ro"], "rotate": 0}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                   |
|:------:|:------:|:-------:|:-------|:------------------------------|
| 31:24  |        |         |        | Reserved                      |
| 23:16  |   ro   |    x    | RXLVL  | Current fill level of RX fifo |
|  15:8  |        |         |        | Reserved                      |
|  7:0   |   ro   |    x    | TXLVL  | Current fill level of TX fifo |

## OVRD
TX pin override control. Gives direct SW control over TX pin state
- Offset: `0x28`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "TXEN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TXVAL", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                          |
|:------:|:------:|:-------:|:-------|:-------------------------------------|
|  31:2  |        |         |        | Reserved                             |
|   1    |   rw   |   0x0   | TXVAL  | Write to set the value of the TX pin |
|   0    |   rw   |   0x0   | TXEN   | Enable TX pin override control       |

## VAL
UART oversampled values
- Offset: `0x2c`
- Reset default: `0x0`
- Reset mask: `0xffff`

### Fields

```wavejson
{"reg": [{"name": "RX", "bits": 16, "attr": ["ro"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                            |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------|
| 31:16  |        |         |        | Reserved                                                               |
|  15:0  |   ro   |    x    | RX     | Last 16 oversampled values of RX. Most recent bit is bit 0, oldest 15. |

## TIMEOUT_CTRL
UART RX timeout control
- Offset: `0x30`
- Reset default: `0x0`
- Reset mask: `0x80ffffff`

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 24, "attr": ["rw"], "rotate": 0}, {"bits": 7}, {"name": "EN", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                        |
|:------:|:------:|:-------:|:-------|:-----------------------------------|
|   31   |   rw   |   0x0   | EN     | Enable RX timeout feature          |
| 30:24  |        |         |        | Reserved                           |
|  23:0  |   rw   |   0x0   | VAL    | RX timeout value in UART bit times |


<!-- END CMDGEN -->
