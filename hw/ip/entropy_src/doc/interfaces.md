# Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/entropy_src/data/entropy_src.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`entropy_src`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name                  | Package::Struct                    | Type    | Act   |   Width | Description                                                                                                                                                                                                                                                                                                                       |
|:---------------------------|:-----------------------------------|:--------|:------|--------:|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| entropy_src_hw_if          | entropy_src_pkg::entropy_src_hw_if | req_rsp | rsp   |       1 |                                                                                                                                                                                                                                                                                                                                   |
| cs_aes_halt                | entropy_src_pkg::cs_aes_halt       | req_rsp | req   |       1 | Coordinate activity between CSRNG's AES and Entropy Source's SHA3. The idea is that Entropy Source requests CSRNG's AES to halt and waits for CSRNG to acknowledge before it starts its SHA3. While SHA3 runs, Entropy Source keeps the request high. CSRNG may not drop the acknowledge before Entropy Source drops the request. |
| entropy_src_rng            | entropy_src_pkg::entropy_src_rng   | req_rsp | req   |       1 |                                                                                                                                                                                                                                                                                                                                   |
| entropy_src_xht            | entropy_src_pkg::entropy_src_xht   | req_rsp | req   |       1 |                                                                                                                                                                                                                                                                                                                                   |
| otp_en_entropy_src_fw_read | prim_mubi_pkg::mubi8               | uni     | rcv   |       1 |                                                                                                                                                                                                                                                                                                                                   |
| otp_en_entropy_src_fw_over | prim_mubi_pkg::mubi8               | uni     | rcv   |       1 |                                                                                                                                                                                                                                                                                                                                   |
| rng_fips                   | logic                              | uni     | req   |       1 |                                                                                                                                                                                                                                                                                                                                   |
| tl                         | tlul_pkg::tl                       | req_rsp | rsp   |       1 |                                                                                                                                                                                                                                                                                                                                   |

## Interrupts

| Interrupt Name        | Type   | Description                                                                         |
|:----------------------|:-------|:------------------------------------------------------------------------------------|
| es_entropy_valid      | Event  | Asserted when entropy source bits are available.                                    |
| es_health_test_failed | Event  | Asserted when the alert count has been met.                                         |
| es_observe_fifo_ready | Event  | Asserted when the observe FIFO has filled to the threshold level.                   |
| es_fatal_err          | Event  | Asserted when a FIFO error occurs, or if an illegal state machine state is reached. |

## Security Alerts

| Alert Name   | Description                                                                                                                                                                                                                       |
|:-------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| recov_alert  | This alert is triggered upon the alert health test threshold criteria not met.                                                                                                                                                    |
| fatal_alert  | This alert triggers for any condition detected in the [`ERR_CODE`](registers.md#err_code) register, which includes FIFO errors, COUNTER errors, FSM state errors, and also when integrity failures are detected on the TL-UL bus. |

## Security Countermeasures

| Countermeasure ID                         | Description                                                                         |
|:------------------------------------------|:------------------------------------------------------------------------------------|
| ENTROPY_SRC.CONFIG.REGWEN                 | Registers are protected from writes.                                                |
| ENTROPY_SRC.CONFIG.MUBI                   | Registers have multi-bit encoded fields.                                            |
| ENTROPY_SRC.CONFIG.REDUN                  | Threshold register has an inverted copy to compare against.                         |
| ENTROPY_SRC.INTERSIG.MUBI                 | OTP signal used to enable software access to registers.                             |
| ENTROPY_SRC.MAIN_SM.FSM.SPARSE            | The ENTROPY_SRC main state machine uses a sparse state encoding.                    |
| ENTROPY_SRC.ACK_SM.FSM.SPARSE             | The ENTROPY_SRC ack state machine uses a sparse state encoding.                     |
| ENTROPY_SRC.RNG.BKGN_CHK                  | Random number generator is protected with continuous background health checks.      |
| ENTROPY_SRC.CTR.REDUN                     | Counter hardening for all health test counters.                                     |
| ENTROPY_SRC.CTR.LOCAL_ESC                 | Redundant counter failures will cause a local escalation to the main state machine. |
| ENTROPY_SRC.ESFINAL_RDATA.BUS.CONSISTENCY | Comparison on successive bus values for the post-conditioned entropy seed bus.      |
| ENTROPY_SRC.TILE_LINK.BUS.INTEGRITY       | Tilelink end-to-end bus integrity scheme.                                           |


<!-- END CMDGEN -->
