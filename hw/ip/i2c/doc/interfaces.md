# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/i2c/data/i2c.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`i2c`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*

## Peripheral Pins for Chip IO

| Pin name   | Direction   | Description            |
|:-----------|:------------|:-----------------------|
| sda        | inout       | Serial input data bit  |
| scl        | inout       | Serial input clock bit |

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name   | Package::Struct   | Type    | Act   |   Width | Description   |
|:------------|:------------------|:--------|:------|--------:|:--------------|
| tl          | tlul_pkg::tl      | req_rsp | rsp   |       1 |               |

## Interrupts

| Interrupt Name   | Type   | Description                                                                                                                                                                                                          |
|:-----------------|:-------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| fmt_threshold    | Event  | host mode interrupt: raised when the FMT FIFO depth is less than the low threshold.                                                                                                                                  |
| rx_threshold     | Event  | host mode interrupt: raised if the RX FIFO is greater than the high threshold.                                                                                                                                       |
| fmt_overflow     | Event  | host mode interrupt: raised if the FMT FIFO has overflowed.                                                                                                                                                          |
| rx_overflow      | Event  | host mode interrupt: raised if the RX FIFO has overflowed.                                                                                                                                                           |
| nak              | Event  | host mode interrupt: raised if there is no ACK in response to an address or data write                                                                                                                               |
| scl_interference | Event  | host mode interrupt: raised if the SCL line drops early (not supported without clock synchronization).                                                                                                               |
| sda_interference | Event  | host mode interrupt: raised if the SDA line goes low when host is trying to assert high                                                                                                                              |
| stretch_timeout  | Event  | host mode interrupt: raised if target stretches the clock beyond the allowed timeout period                                                                                                                          |
| sda_unstable     | Event  | host mode interrupt: raised if the target does not assert a constant value of SDA during transmission.                                                                                                               |
| cmd_complete     | Event  | host and target mode interrupt. In host mode, raised if the host issues a repeated START or terminates the transaction by issuing STOP. In target mode, raised if the external host issues a STOP or repeated START. |
| tx_stretch       | Status | target mode interrupt: raised if the target is stretching clocks for a read command.  This is a level status interrupt.                                                                                              |
| tx_overflow      | Event  | target mode interrupt: raised if TX FIFO has overflowed.                                                                                                                                                             |
| acq_full         | Status | target mode interrupt: raised if ACQ FIFO becomes full.  This is a level status interrupt.                                                                                                                           |
| unexp_stop       | Event  | target mode interrupt: raised if STOP is received without a preceding NACK during an external host read.                                                                                                             |
| host_timeout     | Event  | target mode interrupt: raised if the host stops sending the clock during an ongoing transaction.                                                                                                                     |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID   | Description                      |
|:--------------------|:---------------------------------|
| I2C.BUS.INTEGRITY   | End-to-end bus integrity scheme. |


<!-- END CMDGEN -->
