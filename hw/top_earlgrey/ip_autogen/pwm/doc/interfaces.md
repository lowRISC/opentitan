# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/top_earlgrey/ip_autogen/pwm/data/pwm.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`pwm`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`clk_core_i`**
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Interrupts: *none*

## Peripheral Pins for Chip IO

| Pin name   | Direction   | Description                                                                                                                                                                     |
|:-----------|:------------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| pwm[5:0]   | output      | Pulse output.  Note that though this output is always enabled, there is a formal set of enable pins (pwm_en_o) which are required for top-level integration of comportable IPs. |

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name     | Package::Struct               | Type    | Act   |   Width | Description                                                                                                                          |
|:--------------|:------------------------------|:--------|:------|--------:|:-------------------------------------------------------------------------------------------------------------------------------------|
| racl_policies | top_racl_pkg::racl_policy_vec | uni     | rcv   |       1 | Incoming RACL policy vector from a racl_ctrl instance. The policy selection vector (parameter) selects the policy for each register. |
| racl_error    | top_racl_pkg::racl_error_log  | uni     | req   |       1 | RACL error log information of this module.                                                                                           |
| tl            | tlul_pkg::tl                  | req_rsp | rsp   |       1 |                                                                                                                                      |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID   | Description                      |
|:--------------------|:---------------------------------|
| PWM.BUS.INTEGRITY   | End-to-end bus integrity scheme. |


<!-- END CMDGEN -->
