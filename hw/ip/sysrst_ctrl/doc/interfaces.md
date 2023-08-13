# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/sysrst_ctrl/data/sysrst_ctrl.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`sysrst_ctrl`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`clk_aon_i`**
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*

## Peripheral Pins for Chip IO

| Pin name    | Direction   | Description                                                          |
|:------------|:------------|:---------------------------------------------------------------------|
| ac_present  | input       | A/C power is present                                                 |
| key0_in     | input       | VolUp button in tablet; column output from the EC in a laptop        |
| key1_in     | input       | VolDown button in tablet; row input from keyboard matrix in a laptop |
| key2_in     | input       | TBD button in tablet; row input from keyboard matrix in a laptop     |
| pwrb_in     | input       | Power button in both tablet and laptop                               |
| lid_open    | input       | Lid is open                                                          |
| bat_disable | output      | Battery is disconnected                                              |
| key0_out    | output      | Passthrough from key0_in, can be configured to invert                |
| key1_out    | output      | Passthrough from key1_in, can be configured to invert                |
| key2_out    | output      | Passthrough from key2_in, can be configured to invert                |
| pwrb_out    | output      | Passthrough from pwrb_in, can be configured to invert                |
| z3_wakeup   | output      | To enter Z3 mode and exit from Z4 sleep mode                         |
| ec_rst_l    | inout       | ec_rst_l as an inout to/from the open drain IO                       |
| flash_wp_l  | inout       | flash_wp_l as an inout to/from the open drain IO                     |

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name   | Package::Struct   | Type    | Act   |   Width | Description   |
|:------------|:------------------|:--------|:------|--------:|:--------------|
| wkup_req    | logic             | uni     | req   |       1 |               |
| rst_req     | logic             | uni     | req   |       1 |               |
| tl          | tlul_pkg::tl      | req_rsp | rsp   |       1 |               |

## Interrupts

| Interrupt Name   | Type   | Description                                             |
|:-----------------|:-------|:--------------------------------------------------------|
| event_detected   | Event  | Common interrupt triggered by combo or keyboard events. |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID         | Description                      |
|:--------------------------|:---------------------------------|
| SYSRST_CTRL.BUS.INTEGRITY | End-to-end bus integrity scheme. |


<!-- END CMDGEN -->
