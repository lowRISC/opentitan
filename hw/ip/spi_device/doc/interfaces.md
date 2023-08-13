# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/spi_device/data/spi_device.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`spi_device`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`scan_clk_i`**
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*

## Peripheral Pins for Chip IO

| Pin name   | Direction   | Description                                    |
|:-----------|:------------|:-----------------------------------------------|
| sck        | input       | SPI Clock                                      |
| csb        | input       | Chip Select#                                   |
| tpm_csb    | input       | TPM Chip Select#                               |
| sd[3:0]    | inout       | SPI IO, IO2/IO3 has multi-purpose (/WP, /HOLD) |

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name   | Package::Struct             | Type    | Act   |   Width | Description   |
|:------------|:----------------------------|:--------|:------|--------:|:--------------|
| ram_cfg     | prim_ram_2p_pkg::ram_2p_cfg | uni     | rcv   |       1 |               |
| passthrough | spi_device_pkg::passthrough | req_rsp | req   |       1 |               |
| mbist_en    | logic                       | uni     | rcv   |       1 |               |
| sck_monitor | logic                       | uni     | req   |       1 |               |
| tl          | tlul_pkg::tl                | req_rsp | rsp   |       1 |               |

## Interrupts

| Interrupt Name           | Type   | Description                                                                                                                                                                                                                                          |
|:-------------------------|:-------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| generic_rx_full          | Event  | RX SRAM FIFO Full                                                                                                                                                                                                                                    |
| generic_rx_watermark     | Event  | RX SRAM FIFO is above the level                                                                                                                                                                                                                      |
| generic_tx_watermark     | Event  | TX SRAM FIFO is under the level                                                                                                                                                                                                                      |
| generic_rx_error         | Event  | SDI in FwMode has error                                                                                                                                                                                                                              |
| generic_rx_overflow      | Event  | RX Async FIFO overflow                                                                                                                                                                                                                               |
| generic_tx_underflow     | Event  | TX Async FIFO underflow                                                                                                                                                                                                                              |
| upload_cmdfifo_not_empty | Event  | Upload Command FIFO is not empty                                                                                                                                                                                                                     |
| upload_payload_not_empty | Event  | Upload payload is not empty.  The event occurs after SPI transaction completed                                                                                                                                                                       |
| upload_payload_overflow  | Event  | Upload payload overflow event.  When a SPI Host system issues a command with payload more than 256B, this event is reported. When it happens, SW should read the last written payload index CSR to figure out the starting address of the last 256B. |
| readbuf_watermark        | Event  | Read Buffer Threshold event.  The host system accesses greater than or equal to the threshold of a buffer.                                                                                                                                           |
| readbuf_flip             | Event  | Read buffer flipped event.  The host system accesses other side of buffer.                                                                                                                                                                           |
| tpm_header_not_empty     | Status | TPM Header(Command/Address) buffer available                                                                                                                                                                                                         |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID        | Description                      |
|:-------------------------|:---------------------------------|
| SPI_DEVICE.BUS.INTEGRITY | End-to-end bus integrity scheme. |


<!-- END CMDGEN -->

The TPM submodule requires a separate input port for CS#.
The TPM submodule and other SPI Device modes are able to be active together.
The host system distinguishes between the TPM transactions and the other SPI transactions using separate CS# ports.
Even though both submodules are able to be active, the host system cannot issue a TPM command and a SPI transaction at the same time due to the SPI IO lines being shared.

The TPM has no write FIFO interrupt.
As TPM transactions are not bigger than 4B in current usage case, the waiting time of the core is not a concern.
The core takes multiple cycles to pop a byte from the write FIFO due to the slower peripheral clock and multiple CDC paths.
The gain of having write FIFO interrupt is not great.
