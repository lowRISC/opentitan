# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/mbx/data/mbx.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`mbx`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`core_tl_d`**, **`soc_tl_d`**
- Bus Host Interfaces (TL-UL): **`sram_tl_h`**
- Peripheral Pins for Chip IO: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name             | Package::Struct               | Type    | Act   |   Width | Description                                                                                                                          |
|:----------------------|:------------------------------|:--------|:------|--------:|:-------------------------------------------------------------------------------------------------------------------------------------|
| doe_intr_support      | logic                         | uni     | req   |       1 |                                                                                                                                      |
| doe_intr_en           | logic                         | uni     | req   |       1 |                                                                                                                                      |
| doe_intr              | logic                         | uni     | req   |       1 |                                                                                                                                      |
| doe_async_msg_support | logic                         | uni     | req   |       1 |                                                                                                                                      |
| racl_policies         | top_racl_pkg::racl_policy_vec | uni     | rcv   |       1 | Incoming RACL policy vector from a racl_ctrl instance. The policy selection vector (parameter) selects the policy for each register. |
| racl_error            | top_racl_pkg::racl_error_log  | uni     | req   |       1 | RACL error log information of this module.                                                                                           |
| sram_tl_h             | tlul_pkg::tl                  | req_rsp | req   |       1 |                                                                                                                                      |
| core_tl_d             | tlul_pkg::tl                  | req_rsp | rsp   |       1 |                                                                                                                                      |
| soc_tl_d              | tlul_pkg::tl                  | req_rsp | rsp   |       1 |                                                                                                                                      |

## Interrupts

| Interrupt Name   | Type   | Description                                       |
|:-----------------|:-------|:--------------------------------------------------|
| mbx_ready        | Event  | A new object was received in the inbound mailbox. |
| mbx_abort        | Event  | An abort request was received from the requester. |
| mbx_error        | Event  | The mailbox instance generated an error.          |

## Security Alerts

| Alert Name   | Description                                                                                                                         |
|:-------------|:------------------------------------------------------------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected.                                                   |
| recov_fault  | This recoverable alert is triggered when memory with invalid ECC (e.g., uninitialized memory) or at an invalid address is accessed. |

## Security Countermeasures

| Countermeasure ID                    | Description                                              |
|:-------------------------------------|:---------------------------------------------------------|
| MBX.BUS.INTEGRITY                    | End-to-end bus integrity scheme.                         |
| MBX.ADDRESS_RANGE.CONFIG.REGWEN_MUBI | Private SRAM memory range is software multibit lockable. |


<!-- END CMDGEN -->
