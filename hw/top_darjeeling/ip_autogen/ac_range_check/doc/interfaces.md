# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/top_darjeeling/ip_autogen/ac_range_check/data/ac_range_check.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`ac_range_check`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name             | Package::Struct               | Type    | Act   |   Width | Description                                                                                                                          |
|:----------------------|:------------------------------|:--------|:------|--------:|:-------------------------------------------------------------------------------------------------------------------------------------|
| range_check_overwrite | prim_mubi_pkg::mubi8          | uni     | rcv   |       1 | Overwrites all ranges and let all requests pass through.                                                                             |
| ctn_tl_h2d            | tlul_pkg::tl_h2d              | uni     | rcv   |       1 | TL-UL input port (request part), synchronous                                                                                         |
| ctn_tl_d2h            | tlul_pkg::tl_d2h              | uni     | req   |       1 | TL-UL input port (response part), synchronous                                                                                        |
| ctn_filtered_tl_h2d   | tlul_pkg::tl_h2d              | uni     | req   |       1 | Filtered TL-UL output port (request part), synchronous                                                                               |
| ctn_filtered_tl_d2h   | tlul_pkg::tl_d2h              | uni     | rcv   |       1 | Filtered TL-UL output port (response part), synchronous                                                                              |
| racl_policies         | top_racl_pkg::racl_policy_vec | uni     | rcv   |       1 | Incoming RACL policy vector from a racl_ctrl instance. The policy selection vector (parameter) selects the policy for each register. |
| racl_error            | top_racl_pkg::racl_error_log  | uni     | req   |       1 | RACL error log information of this module.                                                                                           |
| tl                    | tlul_pkg::tl                  | req_rsp | rsp   |       1 |                                                                                                                                      |

## Interrupts

| Interrupt Name   | Type   | Description                         |
|:-----------------|:-------|:------------------------------------|
| deny_cnt_reached | Event  | Deny counter has reached threshold. |

## Security Alerts

| Alert Name            | Description                                                                                                            |
|:----------------------|:-----------------------------------------------------------------------------------------------------------------------|
| recov_ctrl_update_err | This recoverable alert is triggered upon detecting an update error in the shadowed Control Register.                   |
| fatal_fault           | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected or the internal counter has an error. |

## Security Countermeasures

| Countermeasure ID            | Description                      |
|:-----------------------------|:---------------------------------|
| AC_RANGE_CHECK.BUS.INTEGRITY | End-to-end bus integrity scheme. |


<!-- END CMDGEN -->
