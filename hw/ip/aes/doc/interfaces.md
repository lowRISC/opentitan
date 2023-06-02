# Hardware Interfaces
<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/aes/data/aes.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`aes`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`clk_edn_i`**
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*
- Interrupts: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name      | Package::Struct        | Type    | Act   |   Width | Description   |
|:---------------|:-----------------------|:--------|:------|--------:|:--------------|
| idle           | prim_mubi_pkg::mubi4   | uni     | req   |       1 |               |
| lc_escalate_en | lc_ctrl_pkg::lc_tx     | uni     | rcv   |       1 |               |
| edn            | edn_pkg::edn           | req_rsp | req   |       1 |               |
| keymgr_key     | keymgr_pkg::hw_key_req | uni     | rcv   |       1 |               |
| tl             | tlul_pkg::tl           | req_rsp | rsp   |       1 |               |

## Security Alerts

| Alert Name            | Description                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
|:----------------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| recov_ctrl_update_err | This recoverable alert is triggered upon detecting an update error in the shadowed Control Register. The content of the Control Register is not modified (See Control Register). The AES unit can be recovered from such a condition by restarting the AES operation, i.e., by re-writing the Control Register. This should be monitored by the system.                                                                                                                                                     |
| fatal_fault           | This fatal alert is triggered upon detecting a fatal fault inside the AES unit. Examples for such faults include i) storage errors in the shadowed Control Register, ii) any internal FSM entering an invalid state, iii) any sparsely encoded signal taking on an invalid value, iv) errors in the internal round counter, v) escalations triggered by the life cycle controller, and vi) fatal integrity failures on the TL-UL bus. The AES unit cannot recover from such an error and needs to be reset. |

## Security Countermeasures

| Countermeasure ID                | Description                                                                                                                                                                                              |
|:---------------------------------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| AES.BUS.INTEGRITY                | End-to-end bus integrity scheme.                                                                                                                                                                         |
| AES.LC_ESCALATE_EN.INTERSIG.MUBI | The global escalation input signal from life cycle is multibit encoded.                                                                                                                                  |
| AES.MAIN.CONFIG.SHADOW           | Main control register shadowed.                                                                                                                                                                          |
| AES.MAIN.CONFIG.SPARSE           | Critical fields in main control register one-hot encoded.                                                                                                                                                |
| AES.AUX.CONFIG.SHADOW            | Auxiliary control register shadowed.                                                                                                                                                                     |
| AES.AUX.CONFIG.REGWEN            | Auxiliary control register can be locked until reset.                                                                                                                                                    |
| AES.KEY.SIDELOAD                 | The key can be loaded from a key manager via sideload interface without exposing it to software.                                                                                                         |
| AES.KEY.SW_UNREADABLE            | Key registers are not readable by software.                                                                                                                                                              |
| AES.DATA_REG.SW_UNREADABLE       | Data input and internal state registers are not readable by software.                                                                                                                                    |
| AES.KEY.SEC_WIPE                 | Key registers are cleared with pseudo-random data.                                                                                                                                                       |
| AES.IV.CONFIG.SEC_WIPE           | IV registers are cleared with pseudo-random data.                                                                                                                                                        |
| AES.DATA_REG.SEC_WIPE            | Data input/output and internal state registers are cleared with pseudo-random data.                                                                                                                      |
| AES.DATA_REG.KEY.SCA             | Internal state register cleared with pseudo-random data at the end of the last round. This uses the same mechanism as KEY.SEC_WIPE and is active independent of KEY.MASKING.                             |
| AES.KEY.MASKING                  | 1st-order domain-oriented masking of the cipher core including data path and key expand. Can optionally be disabled via compile-time Verilog parameter for instantiations that don't need SCA hardening. |
| AES.MAIN.FSM.SPARSE              | The main control FSM uses a sparse state encoding.                                                                                                                                                       |
| AES.MAIN.FSM.REDUN               | The main control FSM uses multiple, independent logic rails.                                                                                                                                             |
| AES.CIPHER.FSM.SPARSE            | The cipher core FSM uses a sparse state encoding.                                                                                                                                                        |
| AES.CIPHER.FSM.REDUN             | The cipher core FSM uses multiple, independent logic rails.                                                                                                                                              |
| AES.CIPHER.CTR.REDUN             | The AES round counter inside the cipher core FSM is protected with multiple, independent logic rails.                                                                                                    |
| AES.CTR.FSM.SPARSE               | The CTR mode FSM uses a sparse state encoding.                                                                                                                                                           |
| AES.CTR.FSM.REDUN                | The CTR mode FSM uses multiple, independent logic rails.                                                                                                                                                 |
| AES.CTRL.SPARSE                  | Critical control signals such as handshake and MUX control signals use sparse encodings.                                                                                                                 |
| AES.MAIN.FSM.GLOBAL_ESC          | The main control FSM moves to a terminal error state upon global escalation.                                                                                                                             |
| AES.MAIN.FSM.LOCAL_ESC           | The main control FSM moves to a terminal error state upon local escalation. Can be triggered by MAIN.FSM.SPARSE, MAIN.FSM.REDUN, CTRL.SPARSE, as well as CIPHER.FSM.LOCAL_ESC, CTR.FSM.LOCAL_ESC.        |
| AES.CIPHER.FSM.LOCAL_ESC         | The cipher core FSM moves to a terminal error state upon local escalation. Can be triggered by CIPHER.FSM.SPARSE, CIPHER.FSM.REDUN, CIPHER.CTR.REDUN, CTRL.SPARSE as well as MAIN.FSM.LOCAL_ESC.         |
| AES.CTR.FSM.LOCAL_ESC            | The CTR mode FSM moves to a terminal error state upon local escalation. Can be triggered by CTR.FSM.SPARSE, CTR.FSM.REDUN, and CTRL.SPARSE.                                                              |
| AES.DATA_REG.LOCAL_ESC           | Upon local escalation, the module doesn't output intermediate state.                                                                                                                                     |


<!-- END CMDGEN -->

### Other Signals

The table below lists other signals of the AES unit.

Signal             | Direction        | Type                   | Description
-------------------|------------------|------------------------|---------------
`idle_o`           | `output`         | `logic`                | Idle indication signal for clock manager.
`lc_escalate_en_i` | `input`          | `lc_ctrl_pkg::lc_tx_t` | Life cycle escalation enable coming from [life cycle controller](../../lc_ctrl/README.md). This signal moves the main controller FSM within the AES unit into the terminal error state. The AES unit needs to be reset.
`edn_o`            | `output`         | `edn_pkg::edn_req_t`   | Entropy request to [entropy distribution network (EDN)](../../edn/README.md) for reseeding internal pseudo-random number generators (PRNGs) used for register clearing and masking.
`edn_i`            | `input`          | `edn_pkg::edn_rsp_t`   | [EDN](../../edn/README.md) acknowledgment and entropy input for reseeding internal PRNGs.
`keymgr_key_i`     | `input`          | `keymgr_pgk::hw_key_req_t` | Key sideload request coming from [key manager](../../keymgr/README.md).

Note that the `edn_o` and `edn_i` signals used to interface [EDN](../../edn/README.md) follow a REQ/ACK protocol.
The entropy distributed by EDN is obtained from the [cryptographically secure random number generator (CSRNG)](../../csrng/README.md).
