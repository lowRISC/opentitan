# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/top_earlgrey/ip/pwrmgr/data/autogen/pwrmgr.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`pwrmgr`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`clk_slow_i`**, **`clk_lc_i`**, **`clk_esc_i`**
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name      | Package::Struct           | Type    | Act   |   Width | Description   |
|:---------------|:--------------------------|:--------|:------|--------:|:--------------|
| pwr_ast        | pwrmgr_pkg::pwr_ast       | req_rsp | req   |       1 |               |
| pwr_rst        | pwrmgr_pkg::pwr_rst       | req_rsp | req   |       1 |               |
| pwr_clk        | pwrmgr_pkg::pwr_clk       | req_rsp | req   |       1 |               |
| pwr_otp        | pwrmgr_pkg::pwr_otp       | req_rsp | req   |       1 |               |
| pwr_lc         | pwrmgr_pkg::pwr_lc        | req_rsp | req   |       1 |               |
| pwr_flash      | pwrmgr_pkg::pwr_flash     | uni     | rcv   |       1 |               |
| esc_rst_tx     | prim_esc_pkg::esc_tx      | uni     | rcv   |       1 |               |
| esc_rst_rx     | prim_esc_pkg::esc_rx      | uni     | req   |       1 |               |
| pwr_cpu        | pwrmgr_pkg::pwr_cpu       | uni     | rcv   |       1 |               |
| wakeups        | logic                     | uni     | rcv   |       6 |               |
| rstreqs        | logic                     | uni     | rcv   |       2 |               |
| ndmreset_req   | logic                     | uni     | rcv   |       1 |               |
| strap          | logic                     | uni     | req   |       1 |               |
| low_power      | logic                     | uni     | req   |       1 |               |
| rom_ctrl       | rom_ctrl_pkg::pwrmgr_data | uni     | rcv   |       1 |               |
| fetch_en       | lc_ctrl_pkg::lc_tx        | uni     | req   |       1 |               |
| lc_dft_en      | lc_ctrl_pkg::lc_tx        | uni     | rcv   |       1 |               |
| lc_hw_debug_en | lc_ctrl_pkg::lc_tx        | uni     | rcv   |       1 |               |
| sw_rst_req     | prim_mubi_pkg::mubi4      | uni     | rcv   |       1 |               |
| tl             | tlul_pkg::tl              | req_rsp | rsp   |       1 |               |

## Interrupts

| Interrupt Name   | Type   | Description                                               |
|:-----------------|:-------|:----------------------------------------------------------|
| wakeup           | Event  | Wake from low power state. See wake info for more details |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID             | Description                                                                                                              |
|:------------------------------|:-------------------------------------------------------------------------------------------------------------------------|
| PWRMGR.BUS.INTEGRITY          | End-to-end bus integrity scheme.                                                                                         |
| PWRMGR.LC_CTRL.INTERSIG.MUBI  | life cycle control / debug signals are multibit.                                                                         |
| PWRMGR.ROM_CTRL.INTERSIG.MUBI | rom control done/good signals are multibit.                                                                              |
| PWRMGR.RSTMGR.INTERSIG.MUBI   | reset manager software request is multibit.                                                                              |
| PWRMGR.ESC_RX.CLK.BKGN_CHK    | Escalation receiver has a background timeout check                                                                       |
| PWRMGR.ESC_RX.CLK.LOCAL_ESC   | Escalation receiver clock timeout has a local reset escalation                                                           |
| PWRMGR.FSM.SPARSE             | Sparse encoding for slow and fast state machines.                                                                        |
| PWRMGR.FSM.TERMINAL           | When FSMs reach a bad state, go into a terminate state that does not recover without user or external host intervention. |
| PWRMGR.CTRL_FLOW.GLOBAL_ESC   | When global escalation is received, proceed directly to reset.                                                           |
| PWRMGR.MAIN_PD.RST.LOCAL_ESC  | When main power domain reset glitches, proceed directly to reset.                                                        |
| PWRMGR.CTRL.CONFIG.REGWEN     | Main control protected by regwen.                                                                                        |
| PWRMGR.WAKEUP.CONFIG.REGWEN   | Wakeup configuration protected by regwen.                                                                                |
| PWRMGR.RESET.CONFIG.REGWEN    | Reset configuration protected by regwen.                                                                                 |


<!-- END CMDGEN -->
