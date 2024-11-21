# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/hmac/data/hmac.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`hmac`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name   | Package::Struct      | Type    | Act   |   Width | Description                                                                                               |
|:------------|:---------------------|:--------|:------|--------:|:----------------------------------------------------------------------------------------------------------|
| idle        | prim_mubi_pkg::mubi4 | uni     | req   |       1 | <!-- req_hmac_0023 begin --> TODO add description: Idle should be high when... <!-- req_hmac_0023 end --> |
| tl          | tlul_pkg::tl         | req_rsp | rsp   |       1 |                                                                                                           |

## Interrupts

| Interrupt Name   | Type   | Description                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
|:-----------------|:-------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| hmac_done        | Event  | <!-- req_hmac_0008 begin --> HMAC/SHA-2 has completed. <!-- req_hmac_0008 end -->                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| fifo_empty       | Status | The message FIFO is empty. <!-- req_hmac_001A begin --> This interrupt is raised only if the message FIFO is actually writable by software, i.e., if all of the following conditions are met: i) The HMAC block is not running in HMAC mode and performing the second round of computing the final hash of the outer key as well as the result of the first round using the inner key. ii) Software has not yet written the Process or Stop command to finish the hashing operation. For the interrupt to be raised, the message FIFO must also have been full previously. <!-- req_hmac_001A end --> Otherwise, the hardware empties the FIFO faster than software can fill it and there is no point in interrupting the software to inform it about the message FIFO being empty. |
| hmac_err         | Event  | <!-- req_hmac_0019 begin --> HMAC error has occurred. ERR_CODE register shows which error occurred. <!-- req_hmac_0019 end -->                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |

## Security Alerts

| Alert Name   | Description                                                                                                                               |
|:-------------|:------------------------------------------------------------------------------------------------------------------------------------------|
| fatal_fault  | <!-- req_hmac_0022 begin --> This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. <!-- req_hmac_0022 end --> |

## Security Countermeasures

| Countermeasure ID   | Description                                                                              |
|:--------------------|:-----------------------------------------------------------------------------------------|
| HMAC.BUS.INTEGRITY  | <!-- req_hmac_0023 begin --> End-to-end bus integrity scheme. <!-- req_hmac_0023 end --> |


<!-- END CMDGEN -->
