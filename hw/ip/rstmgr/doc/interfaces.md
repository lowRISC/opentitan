# Hardware Interfaces

## Parameters

The following table lists the instantiation parameters of `rstmgr`.

Parameter                   | Default       | Description
----------------------------|---------------|---------------
`SecCheck`                  | 1             | Enables reset consistency checks on the leaf reset.  Each check contains a small FSM.
`SecMaxSyncDelay`           | 2             | The default synchronization delay assumptions used in reset consistency checks.  If a design uses a sync cell with more stages of delay, that value should be supplied.


## Signals

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/top_earlgrey/ip/rstmgr/data/autogen/rstmgr.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`rstmgr`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`clk_aon_i`**, **`clk_io_div4_i`**, **`clk_main_i`**, **`clk_io_i`**, **`clk_io_div2_i`**, **`clk_usb_i`**, **`clk_por_i`**
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*
- Interrupts: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name   | Package::Struct                  | Type    | Act   |   Width | Description                                                                                                                  |
|:------------|:---------------------------------|:--------|:------|--------:|:-----------------------------------------------------------------------------------------------------------------------------|
| por_n       | logic                            | uni     | rcv   |       2 | Root power on reset signals from ast. There is one root reset signal for each core power domain.                             |
| pwr         | pwr_rst                          | req_rsp | rsp   |       1 | Reset request signals from power manager. Power manager can request for specific domains of the lc/sys reset tree to assert. |
| resets      | rstmgr_pkg::rstmgr_out           | uni     | req   |       1 | Leaf resets fed to the system.                                                                                               |
| rst_en      | rstmgr_pkg::rstmgr_rst_en        | uni     | req   |       1 | Low-power-group outputs used by alert handler.                                                                               |
| alert_dump  | alert_pkg::alert_crashdump       | uni     | rcv   |       1 | Alert handler crash dump information.                                                                                        |
| cpu_dump    | rv_core_ibex_pkg::cpu_crash_dump | uni     | rcv   |       1 | Main processing element crash dump information.                                                                              |
| sw_rst_req  | prim_mubi_pkg::mubi4             | uni     | req   |       1 | Software requested system reset to pwrmgr.                                                                                   |
| tl          | tlul_pkg::tl                     | req_rsp | rsp   |       1 |                                                                                                                              |

## Security Alerts

| Alert Name        | Description                                                                                                                                                    |
|:------------------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------|
| fatal_fault       | This fatal alert is triggered when a fatal structural fault is detected. Structural faults include errors such as sparse fsm errors and tlul integrity errors. |
| fatal_cnsty_fault | This fatal alert is triggered when a reset consistency fault is detected. It is separated from the category above for clearer error collection and debug.      |

## Security Countermeasures

| Countermeasure ID              | Description                                                                                                                |
|:-------------------------------|:---------------------------------------------------------------------------------------------------------------------------|
| RSTMGR.BUS.INTEGRITY           | End-to-end bus integrity scheme.                                                                                           |
| RSTMGR.SCAN.INTERSIG.MUBI      | scan control signals are multibit                                                                                          |
| RSTMGR.LEAF.RST.BKGN_CHK       | Background consistency checks for each leaf reset.                                                                         |
| RSTMGR.LEAF.RST.SHADOW         | Leaf resets to blocks containing shadow registers are shadowed                                                             |
| RSTMGR.LEAF.FSM.SPARSE         | Sparsely encoded fsm for each leaf rst check. The Hamming delta is only 3 as there are a significant number of leaf resets |
| RSTMGR.SW_RST.CONFIG.REGWEN    | Software reset controls are protected by regwen                                                                            |
| RSTMGR.DUMP_CTRL.CONFIG.REGWEN | Crash dump controls are protected by regwen                                                                                |


<!-- END CMDGEN -->
