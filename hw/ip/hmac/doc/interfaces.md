# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/hmac/data/hmac.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`hmac`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name   | Package::Struct      | Type    | Act   |   Width | Description   |
|:------------|:---------------------|:--------|:------|--------:|:--------------|
| idle        | prim_mubi_pkg::mubi4 | uni     | req   |       1 |               |
| tl          | tlul_pkg::tl         | req_rsp | rsp   |       1 |               |

## Interrupts

| Interrupt Name   | Type   | Description                                                       |
|:-----------------|:-------|:------------------------------------------------------------------|
| hmac_done        | Event  | HMAC-256 completes a message with key                             |
| fifo_empty       | Event  | Message FIFO empty condition                                      |
| hmac_err         | Event  | HMAC error occurred. ERR_CODE register shows which error occurred |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID   | Description                      |
|:--------------------|:---------------------------------|
| HMAC.BUS.INTEGRITY  | End-to-end bus integrity scheme. |


<!-- END CMDGEN -->
