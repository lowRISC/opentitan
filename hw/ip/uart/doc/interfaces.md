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

| Port Name      | Package::Struct               | Type    | Act   |   Width | Description                                                                                                                                    |
|:---------------|:------------------------------|:--------|:------|--------:|:-----------------------------------------------------------------------------------------------------------------------------------------------|
| lsio_trigger   | logic                         | uni     | req   |       1 | Self-clearing status trigger for the DMA. Set when RX or TX FIFOs are past their configured watermarks matching watermark interrupt behaviour. |
| racl_policies  | top_racl_pkg::racl_policy_vec | uni     | rcv   |       1 | Incoming RACL policy vector from a racl_ctrl instance. The policy selection vector (parameter) selects the policy for each register.           |
| racl_error     | logic                         | uni     | req   |       1 | RACL error indication signal. If 1, the error log contains valid information.                                                                  |
| racl_error_log | top_racl_pkg::racl_error_log  | uni     | req   |       1 | RACL error log information of this module.                                                                                                     |
| tl             | tlul_pkg::tl                  | req_rsp | rsp   |       1 |                                                                                                                                                |

## Interrupts

| Interrupt Name   | Type   | Description                                                                                                    |
|:-----------------|:-------|:---------------------------------------------------------------------------------------------------------------|
| tx_watermark     | Status | raised if the transmit FIFO is past the high-water mark.                                                       |
| rx_watermark     | Status | raised if the receive FIFO is past the high-water mark.                                                        |
| tx_done          | Event  | raised if the transmit FIFO has emptied and no transmit is ongoing.                                            |
| rx_overflow      | Event  | raised if the receive FIFO has overflowed.                                                                     |
| rx_frame_err     | Event  | raised if a framing error has been detected on receive.                                                        |
| rx_break_err     | Event  | raised if break condition has been detected on receive.                                                        |
| rx_timeout       | Event  | raised if RX FIFO has characters remaining in the FIFO without being retrieved for the programmed time period. |
| rx_parity_err    | Event  | raised if the receiver has detected a parity error.                                                            |
| tx_empty         | Status | raised if the transmit FIFO is empty.                                                                          |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID   | Description                      |
|:--------------------|:---------------------------------|
| UART.BUS.INTEGRITY  | End-to-end bus integrity scheme. |


<!-- END CMDGEN -->
