Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`ascon`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`clk_edn_i`**
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*
- Interrupts: *none*
- Security Countermeasures: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name      | Package::Struct        | Type    | Act   |   Width | Description   |
|:---------------|:-----------------------|:--------|:------|--------:|:--------------|
| idle           | prim_mubi_pkg::mubi4   | uni     | req   |       1 |               |
| lc_escalate_en | lc_ctrl_pkg::lc_tx     | uni     | rcv   |       1 |               |
| edn            | edn_pkg::edn           | req_rsp | req   |       1 |               |
| keymgr_key     | keymgr_pkg::hw_key_req | uni     | rcv   |       1 |               |
| tl             | tlul_pkg::tl           | req_rsp | rsp   |       1 |               |

## Security Alerts

| Alert Name            | Description                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
|:----------------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| recov_ctrl_update_err | This recoverable alert is triggered upon detecting an update error in the shadowed Control Register. The content of the Control Register is not modified (See Control Register). The Ascon unit can be recovered from such a condition by restarting the Ascon operation, i.e., by re-writing the Control Register. This should be monitored by the system.                                                                                                                                                     |
| fatal_fault           | This fatal alert is triggered upon detecting a fatal fault inside the Ascon unit. Examples for such faults include i) storage errors in the shadowed Control Register, ii) any internal FSM entering an invalid state, iii) any sparsely encoded signal taking on an invalid value, iv) errors in the internal round counter, v) escalations triggered by the life cycle controller, and vi) fatal integrity failures on the TL-UL bus. The Ascon unit cannot recover from such an error and needs to be reset. |
