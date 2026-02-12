# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/top_darjeeling/ip_autogen/clkmgr/data/clkmgr.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`clkmgr`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`clk_main_i`**, **`clk_io_i`**, **`clk_aon_i`**
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*
- Interrupts: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name   | Package::Struct          | Type    | Act   |   Width | Description   |
|:------------|:-------------------------|:--------|:------|--------:|:--------------|
| clocks      | clkmgr_pkg::clkmgr_out   | uni     | req   |       1 |               |
| cg_en       | clkmgr_pkg::clkmgr_cg_en | uni     | req   |       1 |               |
| jitter_en   | prim_mubi_pkg::mubi4     | uni     | req   |       1 |               |
| pwr         | pwr_clk                  | req_rsp | rsp   |       1 |               |
| idle        | prim_mubi_pkg::mubi4     | uni     | rcv   |       4 |               |
| tl          | tlul_pkg::tl             | req_rsp | rsp   |       1 |               |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| recov_fault  | This recoverable alert is triggered when there are measurement errors.            |
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID             | Description                                                  |
|:------------------------------|:-------------------------------------------------------------|
| CLKMGR.BUS.INTEGRITY          | End-to-end bus integrity scheme.                             |
| CLKMGR.TIMEOUT.CLK.BKGN_CHK   | Background check for clock timeout.                          |
| CLKMGR.MEAS.CLK.BKGN_CHK      | Background check for clock frequency.                        |
| CLKMGR.MEAS.CONFIG.SHADOW     | Measurement configurations are shadowed.                     |
| CLKMGR.IDLE.INTERSIG.MUBI     | Idle inputs are multibit encoded.                            |
| CLKMGR.JITTER.CONFIG.MUBI     | The jitter enable configuration is multibit encoded.         |
| CLKMGR.IDLE.CTR.REDUN         | Idle counter is duplicated.                                  |
| CLKMGR.MEAS.CONFIG.REGWEN     | The measurement controls protected with regwen.              |
| CLKMGR.CLK_CTRL.CONFIG.REGWEN | Software controlled clock requests are proteced with regwen. |


<!-- END CMDGEN -->
