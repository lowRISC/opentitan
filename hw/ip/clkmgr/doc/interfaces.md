# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/top_earlgrey/ip/clkmgr/data/autogen/clkmgr.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`clkmgr`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`clk_main_i`**, **`clk_io_i`**, **`clk_usb_i`**, **`clk_aon_i`**, **`clk_io_div2_i`**, **`clk_io_div4_i`**
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*
- Interrupts: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name         | Package::Struct          | Type    | Act   |   Width | Description                                              |
|:------------------|:-------------------------|:--------|:------|--------:|:---------------------------------------------------------|
| clocks            | clkmgr_pkg::clkmgr_out   | uni     | req   |       1 |                                                          |
| cg_en             | clkmgr_pkg::clkmgr_cg_en | uni     | req   |       1 |                                                          |
| lc_hw_debug_en    | lc_ctrl_pkg::lc_tx       | uni     | rcv   |       1 |                                                          |
| io_clk_byp_req    | prim_mubi_pkg::mubi4     | uni     | req   |       1 |                                                          |
| io_clk_byp_ack    | prim_mubi_pkg::mubi4     | uni     | rcv   |       1 |                                                          |
| all_clk_byp_req   | prim_mubi_pkg::mubi4     | uni     | req   |       1 |                                                          |
| all_clk_byp_ack   | prim_mubi_pkg::mubi4     | uni     | rcv   |       1 |                                                          |
| hi_speed_sel      | prim_mubi_pkg::mubi4     | uni     | req   |       1 |                                                          |
| div_step_down_req | prim_mubi_pkg::mubi4     | uni     | rcv   |       1 |                                                          |
| lc_clk_byp_req    | lc_ctrl_pkg::lc_tx       | uni     | rcv   |       1 |                                                          |
| lc_clk_byp_ack    | lc_ctrl_pkg::lc_tx       | uni     | req   |       1 |                                                          |
| jitter_en         | prim_mubi_pkg::mubi4     | uni     | req   |       1 |                                                          |
| pwr               | pwr_clk                  | req_rsp | rsp   |       1 |                                                          |
| idle              | prim_mubi_pkg::mubi4     | uni     | rcv   |       4 |                                                          |
| calib_rdy         | prim_mubi_pkg::mubi4     | uni     | rcv   |       1 | Indicates clocks are calibrated and frequencies accurate |
| tl                | tlul_pkg::tl             | req_rsp | rsp   |       1 |                                                          |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| recov_fault  | This recoverable alert is triggered when there are measurement errors.            |
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID                          | Description                                                  |
|:-------------------------------------------|:-------------------------------------------------------------|
| CLKMGR.BUS.INTEGRITY                       | End-to-end bus integrity scheme.                             |
| CLKMGR.TIMEOUT.CLK.BKGN_CHK                | Background check for clock timeout.                          |
| CLKMGR.MEAS.CLK.BKGN_CHK                   | Background check for clock frequency.                        |
| CLKMGR.MEAS.CONFIG.SHADOW                  | Measurement configurations are shadowed.                     |
| CLKMGR.IDLE.INTERSIG.MUBI                  | Idle inputs are multibit encoded.                            |
| CLKMGR.LC_CTRL.INTERSIG.MUBI               | The life cycle control signals are multibit encoded.         |
| CLKMGR.LC_CTRL_CLK_HANDSHAKE.INTERSIG.MUBI | The life cycle clock req/ack signals are multibit encoded.   |
| CLKMGR.CLK_HANDSHAKE.INTERSIG.MUBI         | The external clock req/ack signals are multibit encoded.     |
| CLKMGR.DIV.INTERSIG.MUBI                   | Divider step down request is multibit encoded.               |
| CLKMGR.JITTER.CONFIG.MUBI                  | The jitter enable configuration is multibit encoded.         |
| CLKMGR.IDLE.CTR.REDUN                      | Idle counter is duplicated.                                  |
| CLKMGR.MEAS.CONFIG.REGWEN                  | The measurement controls protected with regwen.              |
| CLKMGR.CLK_CTRL.CONFIG.REGWEN              | Software controlled clock requests are proteced with regwen. |


<!-- END CMDGEN -->
