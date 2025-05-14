# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/soc_dbg_ctrl/data/soc_dbg_ctrl.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`soc_dbg_ctrl`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`core_tl`**, **`jtag_tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*
- Interrupts: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name          | Package::Struct                  | Type    | Act   |   Width | Description                                                                                                                                                |
|:-------------------|:---------------------------------|:--------|:------|--------:|:-----------------------------------------------------------------------------------------------------------------------------------------------------------|
| boot_status        | pwrmgr_pkg::pwr_boot_status      | uni     | rcv   |       1 |                                                                                                                                                            |
| soc_dbg_state      | lc_ctrl_state_pkg::soc_dbg_state | uni     | rcv   |       1 |                                                                                                                                                            |
| soc_dbg_policy_bus | soc_dbg_ctrl_pkg::soc_dbg_policy | uni     | req   |       1 |                                                                                                                                                            |
| lc_hw_debug_en     | lc_ctrl_pkg::lc_tx               | uni     | rcv   |       1 | Multibit life cycle hardware debug enable signal coming from life cycle controller, asserted when the hardware debug mechanisms are enabled in the system. |
| lc_dft_en          | lc_ctrl_pkg::lc_tx               | uni     | rcv   |       1 | Test enable qualifier coming from life cycle controller. This signals enables TEST & RMA mode accesses.                                                    |
| lc_raw_test_rma    | lc_ctrl_pkg::lc_tx               | uni     | rcv   |       1 | Test enable qualifier coming from life cycle controller. This signals enables RAW, TEST and RMA mode accesses.                                             |
| halt_cpu_boot      | logic                            | uni     | rcv   |       1 | External request to halt the CPU until a JTAG command allows the boot process to continue.                                                                 |
| continue_cpu_boot  | rom_ctrl_pkg::pwrmgr_data        | uni     | req   |       1 | Artificial ROM control input to the pwrmgr to halt the boot process.                                                                                       |
| core_tl            | tlul_pkg::tl                     | req_rsp | rsp   |       1 |                                                                                                                                                            |
| jtag_tl            | tlul_pkg::tl                     | req_rsp | rsp   |       1 |                                                                                                                                                            |

## Security Alerts

| Alert Name            | Description                                                                                          |
|:----------------------|:-----------------------------------------------------------------------------------------------------|
| fatal_fault           | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected.                    |
| recov_ctrl_update_err | This recoverable alert is triggered upon detecting an update error in the shadowed Control Register. |

## Security Countermeasures

| Countermeasure ID                                | Description                                 |
|:-------------------------------------------------|:--------------------------------------------|
| SOC_DBG_CTRL.BUS.INTEGRITY                       | End-to-end bus integrity scheme.            |
| SOC_DBG_CTRL.DEBUG_POLICY_VALID.CONFIG.SHADOW    | Debug policy valid register is shadowed.    |
| SOC_DBG_CTRL.DEBUG_POLICY_CATEGORY.CONFIG.SHADOW | Debug policy category register is shadowed. |
| SOC_DBG_CTRL.HALT.FSM.SPARSE                     | The halt FSM uses a sparse state encoding.  |


<!-- END CMDGEN -->
