# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/i3c/data/i3c.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`i3c`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`clk_aon_i`**, **`scan_clk_i`**
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*

## Peripheral Pins for Chip IO

| Pin name    | Direction   | Description                              |
|:------------|:------------|:-----------------------------------------|
| ctrl_sda_pu | output      | I3C Controller data Pullup enable output |
| scl         | inout       | I3C SCL bus clock                        |
| sda         | inout       | I3C SDA data line                        |

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name      | Package::Struct               | Type    | Act   |   Width | Description                                                                                                                                        |
|:---------------|:------------------------------|:--------|:------|--------:|:---------------------------------------------------------------------------------------------------------------------------------------------------|
| rstdet_enable  | logic                         | uni     | req   |       1 | Enables the SCL/SDA inputs of the external Target Reset Detector (`i3c_reset_detector`); deasserted while the Target is disconnected from the bus. |
| rstdet         | i3c_pkg::i3c_rstdet           | req_rsp | req   |       1 | Control and status interface to the external Target Reset Detector (`i3c_reset_detector`).                                                         |
| mbist_en       | logic                         | uni     | rcv   |       1 | Memory built-in self-test enable (currently unused).                                                                                               |
| scl_hk_en      | logic                         | uni     | req   |       1 | I3C Controller clock High-keeper enable output                                                                                                     |
| sda_hk_en      | logic                         | uni     | req   |       1 | I3C Controller data High-keeper enable output                                                                                                      |
| ctrl_scl_pu_en | logic                         | uni     | req   |       1 | I3C Controller clock Pullup enable output                                                                                                          |
| ram_cfg        | prim_ram_1p_pkg::ram_1p_cfg   | req_rsp | rsp   |       1 | RAM configuration of the message buffer memory.                                                                                                    |
| dat_cfg        | prim_ram_1p_pkg::ram_1p_cfg   | req_rsp | rsp   |       1 | RAM configuration of the Device Address Table (DAT) memory.                                                                                        |
| dct_cfg        | prim_ram_1p_pkg::ram_1p_cfg   | req_rsp | rsp   |       1 | RAM configuration of the Device Characteristics Table (DCT) memory.                                                                                |
| racl_policies  | top_racl_pkg::racl_policy_vec | uni     | rcv   |       1 | Incoming RACL policy vector from a racl_ctrl instance. The policy selection vector (parameter) selects the policy for each register.               |
| racl_error     | top_racl_pkg::racl_error_log  | uni     | req   |       1 | RACL error log information of this module.                                                                                                         |
| tl             | tlul_pkg::tl                  | req_rsp | rsp   |       1 |                                                                                                                                                    |

## Interrupts

| Interrupt Name   | Type   | Description       |
|:-----------------|:-------|:------------------|
| hci              | Status | HCI interrupt.    |
| targ             | Status | Target interrupt. |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID   | Description                      |
|:--------------------|:---------------------------------|
| I3C.BUS.INTEGRITY   | End-to-end bus integrity scheme. |


<!-- END CMDGEN -->
