# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/uart/data/uart.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`uart`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*

## Peripheral Pins for Chip IO

| Pin name   | Direction   | Description         |
|:-----------|:------------|:--------------------|
| rx         | input       | Serial receive bit  |
| tx         | output      | Serial transmit bit |

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name   | Package::Struct   | Type    | Act   |   Width | Description   |
|:------------|:------------------|:--------|:------|--------:|:--------------|
| tl          | tlul_pkg::tl      | req_rsp | rsp   |       1 |               |

## Interrupts

| Interrupt Name   | Type   | Description                                                                                                    |
|:-----------------|:-------|:---------------------------------------------------------------------------------------------------------------|
| tx_watermark     | Event  | raised if the transmit FIFO is past the high-water mark.                                                       |
| rx_watermark     | Event  | raised if the receive FIFO is past the high-water mark.                                                        |
| tx_empty         | Event  | raised if the transmit FIFO has emptied and no transmit is ongoing.                                            |
| rx_overflow      | Event  | raised if the receive FIFO has overflowed.                                                                     |
| rx_frame_err     | Event  | raised if a framing error has been detected on receive.                                                        |
| rx_break_err     | Event  | raised if break condition has been detected on receive.                                                        |
| rx_timeout       | Event  | raised if RX FIFO has characters remaining in the FIFO without being retrieved for the programmed time period. |
| rx_parity_err    | Event  | raised if the receiver has detected a parity error.                                                            |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID   | Description                      |
|:--------------------|:---------------------------------|
| UART.BUS.INTEGRITY  | End-to-end bus integrity scheme. |


<!-- END CMDGEN -->
