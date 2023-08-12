# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/pattgen/data/pattgen.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`pattgen`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*

## Peripheral Pins for Chip IO

| Pin name   | Direction   | Description                                                |
|:-----------|:------------|:-----------------------------------------------------------|
| pda0_tx    | output      | Serial output data bit for pattern generation on Channel 0 |
| pcl0_tx    | output      | Clock corresponding to pattern data on Channel 0           |
| pda1_tx    | output      | Serial output data bit for pattern generation on Channel 1 |
| pcl1_tx    | output      | Clock corresponding to pattern data on Channel 1           |

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name   | Package::Struct   | Type    | Act   |   Width | Description   |
|:------------|:------------------|:--------|:------|--------:|:--------------|
| tl          | tlul_pkg::tl      | req_rsp | rsp   |       1 |               |

## Interrupts

| Interrupt Name   | Type   | Description                                          |
|:-----------------|:-------|:-----------------------------------------------------|
| done_ch0         | Event  | raise if pattern generation on Channel 0 is complete |
| done_ch1         | Event  | raise if pattern generation on Channel 1 is complete |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID     | Description                      |
|:----------------------|:---------------------------------|
| PATTGEN.BUS.INTEGRITY | End-to-end bus integrity scheme. |


<!-- END CMDGEN -->
