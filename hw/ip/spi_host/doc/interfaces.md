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

| Port Name     | Package::Struct               | Type    | Act   |   Width | Description                                                                                                                                    |
|:--------------|:------------------------------|:--------|:------|--------:|:-----------------------------------------------------------------------------------------------------------------------------------------------|
| passthrough   | spi_device_pkg::passthrough   | req_rsp | rsp   |       1 |                                                                                                                                                |
| lsio_trigger  | logic                         | uni     | req   |       1 | Self-clearing status trigger for the DMA. Set when RX or TX FIFOs are past their configured watermarks matching watermark interrupt behaviour. |
| racl_policies | top_racl_pkg::racl_policy_vec | uni     | rcv   |       1 | Incoming RACL policy vector from a racl_ctrl instance. The policy selection vector (parameter) selects the policy for each register.           |
| racl_error    | top_racl_pkg::racl_error_log  | uni     | req   |       1 | RACL error log information of this module.                                                                                                     |
| tl            | tlul_pkg::tl                  | req_rsp | rsp   |       1 |                                                                                                                                                |

## Interrupts

| Interrupt Name   | Type   | Description                                                                                              |
|:-----------------|:-------|:---------------------------------------------------------------------------------------------------------|
| error            | Event  | Error-related interrupts, see [`ERROR_ENABLE`](registers.md#error_enable) register for more information. |
| spi_event        | Status | Event-related interrupts, see [`EVENT_ENABLE`](registers.md#event_enable) register for more information. |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID      | Description                      |
|:-----------------------|:---------------------------------|
| SPI_HOST.BUS.INTEGRITY | End-to-end bus integrity scheme. |


<!-- END CMDGEN -->
