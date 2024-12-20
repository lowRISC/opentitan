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

| Port Name           | Package::Struct             | Type    | Act   |   Width | Description   |
|:--------------------|:----------------------------|:--------|:------|--------:|:--------------|
| ram_cfg_sys2spi     | prim_ram_2p_pkg::ram_2p_cfg | uni     | rcv   |       1 |               |
| ram_cfg_rsp_sys2spi | prim_ram_2p_pkg::ram_2p_cfg | uni     | req   |       1 |               |
| ram_cfg_spi2sys     | prim_ram_2p_pkg::ram_2p_cfg | uni     | rcv   |       1 |               |
| ram_cfg_rsp_spi2sys | prim_ram_2p_pkg::ram_2p_cfg | uni     | req   |       1 |               |
| passthrough         | spi_device_pkg::passthrough | req_rsp | req   |       1 |               |
| mbist_en            | logic                       | uni     | rcv   |       1 |               |
| sck_monitor         | logic                       | uni     | req   |       1 |               |
| tl                  | tlul_pkg::tl                | req_rsp | rsp   |       1 |               |

## Interrupts

| Interrupt Name           | Type   | Description                                                                                                                                                                                                                                         |
|:-------------------------|:-------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| upload_cmdfifo_not_empty | Event  | Upload Command FIFO is not empty                                                                                                                                                                                                                    |
| upload_payload_not_empty | Event  | Upload payload is not empty. The event occurs after SPI transaction completed                                                                                                                                                                       |
| upload_payload_overflow  | Event  | Upload payload overflow event. When a SPI Host system issues a command with payload more than 256B, this event is reported. When it happens, SW should read the last written payload index CSR to figure out the starting address of the last 256B. |
| readbuf_watermark        | Event  | Read Buffer Threshold event. The host system accesses greater than or equal to the threshold of a buffer.                                                                                                                                           |
| readbuf_flip             | Event  | Read buffer flipped event. The host system accesses other side of buffer.                                                                                                                                                                           |
| tpm_header_not_empty     | Status | TPM Header(Command/Address) buffer available                                                                                                                                                                                                        |
| tpm_rdfifo_cmd_end       | Event  | TPM RdFIFO command ended. The TPM Read command targeting the RdFIFO ended. Check TPM_STATUS.rdfifo_aborted to see if the transaction completed.                                                                                                     |
| tpm_rdfifo_drop          | Event  | TPM RdFIFO data dropped. Data was dropped from the RdFIFO. Data was written while a read command was not active, and it was not accepted. This can occur when the host aborts a read command.                                                       |

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
