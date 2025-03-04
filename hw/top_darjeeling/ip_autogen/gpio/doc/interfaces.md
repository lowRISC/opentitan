# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/top_darjeeling/ip_autogen/gpio/data/gpio.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`gpio`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*

## Peripheral Pins for Chip IO

| Pin name   | Direction   | Description            |
|:-----------|:------------|:-----------------------|
| gpio[31:0] | inout       | GPIO inout to/from PAD |

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name      | Package::Struct               | Type    | Act   |   Width | Description                                                                                                                                 |
|:---------------|:------------------------------|:--------|:------|--------:|:--------------------------------------------------------------------------------------------------------------------------------------------|
| strap_en       | logic                         | uni     | rcv   |       1 | The strap enable signal tells gpio to take a snapshot of the input pins. The behaviour of this signal after that event will have no effect. |
| sampled_straps | gpio_pkg::gpio_straps         | uni     | req   |       1 | This vector contains the sampled strap values.                                                                                              |
| racl_policies  | top_racl_pkg::racl_policy_vec | uni     | rcv   |       1 | Incoming RACL policy vector from a racl_ctrl instance. The policy selection vector (parameter) selects the policy for each register.        |
| racl_error     | top_racl_pkg::racl_error_log  | uni     | req   |       1 | RACL error log information of this module.                                                                                                  |
| tl             | tlul_pkg::tl                  | req_rsp | rsp   |       1 |                                                                                                                                             |

## Interrupts

| Interrupt Name   | Type   | Description                                                 |
|:-----------------|:-------|:------------------------------------------------------------|
| gpio[31:0]       | Event  | raised if any of GPIO pin detects configured interrupt mode |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID   | Description                      |
|:--------------------|:---------------------------------|
| GPIO.BUS.INTEGRITY  | End-to-end bus integrity scheme. |


<!-- END CMDGEN -->
