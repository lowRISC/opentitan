# Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/edn/data/edn.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`edn`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name   | Package::Struct   | Type    | Act   |   Width | Description                                                                                                                                                                                                                                                                                                                   |
|:------------|:------------------|:--------|:------|--------:|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| csrng_cmd   | csrng_pkg::csrng  | req_rsp | req   |       1 | EDN supports a signal CSRNG application interface.                                                                                                                                                                                                                                                                            |
| edn         | edn_pkg::edn      | req_rsp | rsp   |       8 | The collection of peripheral ports supported by edn. The width (4) indicates the number of peripheral ports on a single instance. Due to limitations in the parametrization of top-level interconnects this value is not currently parameterizable.  However, the number of peripheral ports may change in a future revision. |
| tl          | tlul_pkg::tl      | req_rsp | rsp   |       1 |                                                                                                                                                                                                                                                                                                                               |

## Interrupts

| Interrupt Name   | Type   | Description                                           |
|:-----------------|:-------|:------------------------------------------------------|
| edn_cmd_req_done | Event  | Asserted when a software CSRNG request has completed. |
| edn_fatal_err    | Event  | Asserted when a FIFO error occurs.                    |

## Security Alerts

| Alert Name   | Description                                                                                                                              |
|:-------------|:-----------------------------------------------------------------------------------------------------------------------------------------|
| recov_alert  | This alert is triggered when entropy bus data matches on consecutive clock cycles.                                                       |
| fatal_alert  | This alert triggers (i) if an illegal state machine state is reached, or (ii) if a fatal integrity failure is detected on the TL-UL bus. |

## Security Countermeasures

| Countermeasure ID            | Description                                                                                                       |
|:-----------------------------|:------------------------------------------------------------------------------------------------------------------|
| EDN.CONFIG.REGWEN            | Registers are protected from writes.                                                                              |
| EDN.CONFIG.MUBI              | Registers have multi-bit encoded fields.                                                                          |
| EDN.MAIN_SM.FSM.SPARSE       | The EDN main state machine uses a sparse state encoding.                                                          |
| EDN.ACK_SM.FSM.SPARSE        | The EDN ACK state machine uses a sparse state encoding.                                                           |
| EDN.CTR.REDUN                | Counter hardening on the generate command maximum requests counter.                                               |
| EDN.MAIN_SM.CTR.LOCAL_ESC    | A mismatch detected inside any EDN counter moves the main state machine into a terminal error state.              |
| EDN.CS_RDATA.BUS.CONSISTENCY | Comparison on successive bus values for genbits returned from csrng that will distribute over the endpoint buses. |
| EDN.TILE_LINK.BUS.INTEGRITY  | Tilelink end-to-end bus integrity scheme.                                                                         |


<!-- END CMDGEN -->
