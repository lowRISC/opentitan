# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/top_earlgrey/ip_autogen/rv_plic/data/rv_plic.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`rv_plic`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*
- Interrupts: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name   | Package::Struct   | Type    | Act   |   Width | Description   |
|:------------|:------------------|:--------|:------|--------:|:--------------|
| irq         | logic             | uni     | req   |       1 |               |
| irq_id      | logic             | uni     | req   |       1 |               |
| msip        | logic             | uni     | req   |       1 |               |
| tl          | tlul_pkg::tl      | req_rsp | rsp   |       1 |               |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID     | Description                      |
|:----------------------|:---------------------------------|
| RV_PLIC.BUS.INTEGRITY | End-to-end bus integrity scheme. |


<!-- END CMDGEN -->
