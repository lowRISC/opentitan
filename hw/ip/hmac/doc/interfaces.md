# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/hmac/data/hmac.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`hmac`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name   | Package::Struct                 | Type    | Act   |   Width | Description   |
|:------------|:--------------------------------|:--------|:------|--------:|:--------------|
| idle        | prim_mubi_pkg::mubi4            | uni     | req   |       1 |               |
| keymgr_key  | keymgr_dpe_pkg::wide_hw_key_req | uni     | rcv   |       1 |               |
| tl          | tlul_pkg::tl                    | req_rsp | rsp   |       1 |               |

## Interrupts

| Interrupt Name   | Type   | Description                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
|:-----------------|:-------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| hmac_done        | Event  | HMAC/SHA-2 has completed.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| fifo_empty       | Status | The message FIFO is empty. This interrupt is raised only if the message FIFO is actually writable by software, i.e., if all of the following conditions are met: i) The HMAC block is not running in HMAC mode and performing the second round of computing the final hash of the outer key as well as the result of the first round using the inner key. ii) Software has not yet written the Process or Stop command to finish the hashing operation. For the interrupt to be raised, the message FIFO must also have been full previously. Otherwise, the hardware empties the FIFO faster than software can fill it and there is no point in interrupting the software to inform it about the message FIFO being empty. |
| hmac_err         | Event  | HMAC error has occurred. ERR_CODE register shows which error occurred.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |

## Security Alerts

| Alert Name   | Description                                                                                                                                                                                                                                                                                                                                                                                    |
|:-------------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected, when an FSM is glitched into an invalid state, when the redundant check of the inner and outer hash rounds fails, or when the multi-bit encoded `hmac_en` or `sha_en` configuration carries an invalid encoding. Except for TL-UL bus integrity faults, these faults also lock up HMAC until the next reset. |

## Security Countermeasures

| Countermeasure ID   | Description                                                                                                                                                                                                                                             |
|:--------------------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| HMAC.BUS.INTEGRITY  | End-to-end bus integrity scheme.                                                                                                                                                                                                                        |
| HMAC.KEY.SIDELOAD   | Key from KeyMgr is sideloaded.                                                                                                                                                                                                                          |
| HMAC.FSM.SPARSE     | The HMAC core and done-tracking FSMs are sparsely encoded.                                                                                                                                                                                              |
| HMAC.FSM.LOCAL_ESC  | Upon detecting a fatal fault, the HMAC core FSM moves into a terminal error state and a fatal error is latched in a multi-bit encoded register. While latched, the SHA-2 engine is disabled and the digest registers read as zero until the next reset. |
| HMAC.CONFIG.MUBI    | The hmac_en and sha_en configuration signals are multi-bit encoded.                                                                                                                                                                                     |
| HMAC.CTR.REDUN      | A redundant round counter tracks the completion of the inner and outer hash and is checked against the primary round tracking before signaling completion.                                                                                              |


<!-- END CMDGEN -->
