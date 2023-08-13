# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/spi_host/data/spi_host.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`spi_host`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*

## Peripheral Pins for Chip IO

| Pin name   | Direction   | Description                                                                    |
|:-----------|:------------|:-------------------------------------------------------------------------------|
| sck        | output      | SPI Clock                                                                      |
| csb        | output      | Chip Select# (One hot, active low).  The size of this port should match NumCS. |
| sd[3:0]    | inout       | SPI data bus                                                                   |

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name   | Package::Struct             | Type    | Act   |   Width | Description   |
|:------------|:----------------------------|:--------|:------|--------:|:--------------|
| passthrough | spi_device_pkg::passthrough | req_rsp | rsp   |       1 |               |
| tl          | tlul_pkg::tl                | req_rsp | rsp   |       1 |               |

## Interrupts

| Interrupt Name   | Type   | Description                                                                                                 |
|:-----------------|:-------|:------------------------------------------------------------------------------------------------------------|
| error            | Event  | Error-related interrupts, see [`ERROR_ENABLE`](registers.md#error_enable) register for more    information. |
| spi_event        | Event  | Event-related interrupts, see [`EVENT_ENABLE`](registers.md#event_enable) register for more    information. |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID      | Description                      |
|:-----------------------|:---------------------------------|
| SPI_HOST.BUS.INTEGRITY | End-to-end bus integrity scheme. |


<!-- END CMDGEN -->
