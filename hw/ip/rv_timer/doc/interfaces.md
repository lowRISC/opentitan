# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/rv_timer/data/rv_timer.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`rv_timer`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name     | Package::Struct               | Type    | Act   |   Width | Description                                                                                                                          |
|:--------------|:------------------------------|:--------|:------|--------:|:-------------------------------------------------------------------------------------------------------------------------------------|
| racl_policies | top_racl_pkg::racl_policy_vec | uni     | rcv   |       1 | Incoming RACL policy vector from a racl_ctrl instance. The policy selection vector (parameter) selects the policy for each register. |
| racl_error    | top_racl_pkg::racl_error_log  | uni     | req   |       1 | RACL error log information of this module.                                                                                           |
| tl            | tlul_pkg::tl                  | req_rsp | rsp   |       1 |                                                                                                                                      |

## Interrupts

| Interrupt Name             | Type   | Description                                          |
|:---------------------------|:-------|:-----------------------------------------------------|
| timer_expired_hart0_timer0 | Event  | raised if hart0's timer0 expired (mtimecmp >= mtime) |

## Security Alerts

| Alert Name   | Description                                                                                                |
|:-------------|:-----------------------------------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected inside the RV_TIMER unit. |

## Security Countermeasures

| Countermeasure ID      | Description                      |
|:-----------------------|:---------------------------------|
| RV_TIMER.BUS.INTEGRITY | End-to-end bus integrity scheme. |


<!-- END CMDGEN -->
