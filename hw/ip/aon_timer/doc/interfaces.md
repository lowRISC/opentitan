# Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/aon_timer/data/aon_timer.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`aon_timer`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`clk_aon_i`**
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name           | Package::Struct    | Type    | Act   |   Width | Description   |
|:--------------------|:-------------------|:--------|:------|--------:|:--------------|
| nmi_wdog_timer_bark | logic              | uni     | req   |       1 |               |
| wkup_req            | logic              | uni     | req   |       1 |               |
| aon_timer_rst_req   | logic              | uni     | req   |       1 |               |
| lc_escalate_en      | lc_ctrl_pkg::lc_tx | uni     | rcv   |       1 |               |
| sleep_mode          | logic              | uni     | rcv   |       1 |               |
| tl                  | tlul_pkg::tl       | req_rsp | rsp   |       1 |               |

## Interrupts

| Interrupt Name     | Type   | Description                                                |
|:-------------------|:-------|:-----------------------------------------------------------|
| wkup_timer_expired | Event  | Raised if the wakeup timer has hit the specified threshold |
| wdog_timer_bark    | Event  | Raised if the watchdog timer has hit the bark threshold    |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID       | Description                      |
|:------------------------|:---------------------------------|
| AON_TIMER.BUS.INTEGRITY | End-to-end bus integrity scheme. |


<!-- END CMDGEN -->
