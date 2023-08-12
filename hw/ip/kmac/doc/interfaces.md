# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/kmac/data/kmac.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`kmac`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`clk_edn_i`**
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name      | Package::Struct        | Type    | Act   |   Width | Description   |
|:---------------|:-----------------------|:--------|:------|--------:|:--------------|
| keymgr_key     | keymgr_pkg::hw_key_req | uni     | rcv   |       1 |               |
| app            | kmac_pkg::app          | req_rsp | rsp   |       3 |               |
| entropy        | edn_pkg::edn           | req_rsp | req   |       1 |               |
| idle           | prim_mubi_pkg::mubi4   | uni     | req   |       1 |               |
| en_masking     | logic                  | uni     | req   |       1 |               |
| lc_escalate_en | lc_ctrl_pkg::lc_tx     | uni     | rcv   |       1 |               |
| tl             | tlul_pkg::tl           | req_rsp | rsp   |       1 |               |

## Interrupts

| Interrupt Name   | Type   | Description                                                   |
|:-----------------|:-------|:--------------------------------------------------------------|
| kmac_done        | Event  | KMAC/SHA3 absorbing has been completed                        |
| fifo_empty       | Event  | Message FIFO empty condition                                  |
| kmac_err         | Event  | KMAC/SHA3 error occurred. ERR_CODE register shows the details |

## Security Alerts

| Alert Name          | Description                                                                                                                                                                                                                                                                                                                                                                                                 |
|:--------------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| recov_operation_err | Alert for KMAC operation error. It occurs when the shadow registers have update errors.                                                                                                                                                                                                                                                                                                                     |
| fatal_fault_err     | This fatal alert is triggered when a fatal error is detected inside the KMAC unit. Examples for such faults include: i) TL-UL bus integrity fault. ii) Storage errors in the shadow registers. iii) Errors in the message, round, or key counter. iv) Any internal FSM entering an invalid state. v) An error in the redundant lfsr. The KMAC unit cannot recover from such an error and needs to be reset. |

## Security Countermeasures

| Countermeasure ID                 | Description                                                                                            |
|:----------------------------------|:-------------------------------------------------------------------------------------------------------|
| KMAC.BUS.INTEGRITY                | End-to-end bus integrity scheme.                                                                       |
| KMAC.LC_ESCALATE_EN.INTERSIG.MUBI | The global escalation input signal from the life cycle is multibit encoded                             |
| KMAC.SW_KEY.KEY.MASKING           | Data storage and secret key are two share to guard against 1st order attack.                           |
| KMAC.KEY.SIDELOAD                 | Key from KeyMgr is sideloaded.                                                                         |
| KMAC.CFG_SHADOWED.CONFIG.SHADOW   | Shadowed CFG register.                                                                                 |
| KMAC.FSM.SPARSE                   | FSMs in KMAC are sparsely encoded.                                                                     |
| KMAC.CTR.REDUN                    | Round counter, key index counter, sentmsg counter and hash counter use prim_count for redundancy       |
| KMAC.PACKER.CTR.REDUN             | Packer Position counter uses prim_count for redundancy                                                 |
| KMAC.CFG_SHADOWED.CONFIG.REGWEN   | CFG_SHADOWED is protected by REGWEN                                                                    |
| KMAC.FSM.GLOBAL_ESC               | Escalation moves all sparse FSMs into an invalid state.                                                |
| KMAC.FSM.LOCAL_ESC                | Local fatal faults move all sparse FSMs into an invalid state.                                         |
| KMAC.LOGIC.INTEGRITY              | The reset net for the internal state register and critical nets around the output register are buried. |
| KMAC.ABSORBED.CTRL.MUBI           | `absorbed` signal is mubi4_t type to protect against FI attacks.                                       |
| KMAC.SW_CMD.CTRL.SPARSE           | `sw_cmd` and related signals are sparse encoded to protect against FI attacks.                         |


<!-- END CMDGEN -->
