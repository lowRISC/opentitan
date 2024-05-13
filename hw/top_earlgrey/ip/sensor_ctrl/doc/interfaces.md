# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/top_earlgrey/ip/sensor_ctrl/data/sensor_ctrl.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`sensor_ctrl`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`clk_aon_i`**
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Security Countermeasures: *none*

## Peripheral Pins for Chip IO

| Pin name           | Direction   | Description                 |
|:-------------------|:------------|:----------------------------|
| ast_debug_out[8:0] | output      | ast debug outputs to pinmux |

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name       | Package::Struct                | Type    | Act   |   Width | Description   |
|:----------------|:-------------------------------|:--------|:------|--------:|:--------------|
| ast_alert       | ast_pkg::ast_alert             | req_rsp | rsp   |       1 |               |
| ast_status      | ast_pkg::ast_status            | uni     | rcv   |       1 |               |
| ast_init_done   | prim_mubi_pkg::mubi4           | uni     | rcv   |       1 |               |
| ast2pinmux      | logic                          | uni     | rcv   |       9 |               |
| wkup_req        | logic                          | uni     | req   |       1 |               |
| manual_pad_attr | prim_pad_wrapper_pkg::pad_attr | uni     | req   |       4 |               |
| tl              | tlul_pkg::tl                   | req_rsp | rsp   |       1 |               |

## Interrupts

| Interrupt Name     | Type   | Description                 |
|:-------------------|:-------|:----------------------------|
| io_status_change   | Event  | io power status has changed |
| init_status_change | Event  | ast init status has changed |

## Security Alerts

| Alert Name   | Description                    |
|:-------------|:-------------------------------|
| recov_alert  | recoverable sensor_ctrl alerts |
| fatal_alert  | fatal sensor_ctrl alerts       |


<!-- END CMDGEN -->
