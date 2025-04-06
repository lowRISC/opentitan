# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/dma/data/dma.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`dma`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`tl_d`**
- Bus Host Interfaces (TL-UL): **`host_tl_h`**
- Peripheral Pins for Chip IO: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name     | Package::Struct               | Type    | Act   |   Width | Description                                                                                                                          |
|:--------------|:------------------------------|:--------|:------|--------:|:-------------------------------------------------------------------------------------------------------------------------------------|
| lsio_trigger  | dma_pkg::lsio_trigger         | uni     | rcv   |       1 |                                                                                                                                      |
| sys           | dma_pkg::sys                  | req_rsp | req   |       1 |                                                                                                                                      |
| ctn_tl_h2d    | tlul_pkg::tl_h2d              | uni     | req   |       1 | TL-UL host port for egress into CTN (request part), synchronous                                                                      |
| ctn_tl_d2h    | tlul_pkg::tl_d2h              | uni     | rcv   |       1 | TL-UL host port for egress into CTN (response part), synchronous                                                                     |
| racl_policies | top_racl_pkg::racl_policy_vec | uni     | rcv   |       1 | Incoming RACL policy vector from a racl_ctrl instance. The policy selection vector (parameter) selects the policy for each register. |
| racl_error    | top_racl_pkg::racl_error_log  | uni     | req   |       1 | RACL error log information of this module.                                                                                           |
| host_tl_h     | tlul_pkg::tl                  | req_rsp | req   |       1 |                                                                                                                                      |
| tl_d          | tlul_pkg::tl                  | req_rsp | rsp   |       1 |                                                                                                                                      |

## Interrupts

| Interrupt Name   | Type   | Description                                                               |
|:-----------------|:-------|:--------------------------------------------------------------------------|
| dma_done         | Status | DMA operation has been completed.                                         |
| dma_chunk_done   | Status | Indicates the transfer of a single chunk has been completed.              |
| dma_error        | Status | DMA error has occurred. DMA_STATUS.error_code register shows the details. |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID            | Description                                               |
|:-----------------------------|:----------------------------------------------------------|
| DMA.BUS.INTEGRITY            | End-to-end bus integrity scheme.                          |
| DMA.ASID.INTERSIG.MUBI       | Destination and source ASID signals are multibit encoded. |
| DMA.RANGE.CONFIG.REGWEN_MUBI | DMA enabled memory range is software multibit lockable.   |


<!-- END CMDGEN -->
