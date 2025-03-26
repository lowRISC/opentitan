# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/top_darjeeling/ip_autogen/racl_ctrl/data/racl_ctrl.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`racl_ctrl`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name           | Package::Struct               | Type    | Act   | Width                     | Description                                                                            |
|:--------------------|:------------------------------|:--------|:------|:--------------------------|:---------------------------------------------------------------------------------------|
| racl_policies       | top_racl_pkg::racl_policy_vec | uni     | req   | 1                         | Policy vector distributed to the subscribing RACL IPs.                                 |
| racl_error          | top_racl_pkg::racl_error_log  | uni     | rcv   | NumSubscribingIps         | Error log information from all IPs. Only one IP can raise an error at a time.          |
| racl_error_external | top_racl_pkg::racl_error_log  | uni     | rcv   | NumExternalSubscribingIps | Error log information from all external IPs. Only one IP can raise an error at a time. |
| tl                  | tlul_pkg::tl                  | req_rsp | rsp   | 1                         |                                                                                        |

## Interrupts

| Interrupt Name   | Type   | Description              |
|:-----------------|:-------|:-------------------------|
| racl_error       | Status | RACL error has occurred. |

## Security Alerts

| Alert Name            | Description                                                                                          |
|:----------------------|:-----------------------------------------------------------------------------------------------------|
| fatal_fault           | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected.                    |
| recov_ctrl_update_err | This recoverable alert is triggered upon detecting an update error in the shadowed Control Register. |

## Security Countermeasures

| Countermeasure ID                   | Description                         |
|:------------------------------------|:------------------------------------|
| RACL_CTRL.BUS.INTEGRITY             | End-to-end bus integrity scheme.    |
| RACL_CTRL.RACL_POLICY.CONFIG.SHADOW | RACL policy registers are shadowed. |


<!-- END CMDGEN -->
