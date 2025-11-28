# Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/entropy_src/data/entropy_src.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`entropy_src`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name                          | Package::Struct                       | Type    | Act   | Width                 | Description                                                                                                                                                                                                                                                                                                                  |
|:-----------------------------------|:--------------------------------------|:--------|:------|:----------------------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| entropy_src_hw_if                  | entropy_src_pkg::entropy_src_hw_if    | req_rsp | rsp   | 1                     |                                                                                                                                                                                                                                                                                                                              |
| entropy_src_rng_enable             | logic                                 | uni     | req   | 1                     | Signal through which entropy_src enables the noise source. entropy_src will keep this signal high as long as it expects the noise source to operate. This is *not* a flow control signal through which entropy_src would exert backpressure on the noise source; rather this signal stays high while entropy_src is enabled. |
| entropy_src_rng_valid              | logic                                 | uni     | rcv   | 1                     | Acknowledgement signal from the noise source. When '1', it indicates that the `entropy_src_rng_bit` data is valid and ready to be consumed.                                                                                                                                                                                  |
| entropy_src_rng_bits               | logic                                 | uni     | rcv   | RngBusWidth           | Output data bus carrying the raw entropy bits from the noise source. These bits are valid when `entropy_src_rng_valid` is asserted. The width is determined by `RngBusWidth` parametrization.                                                                                                                                |
| entropy_src_xht_valid              | logic                                 | uni     | req   | 1                     | Valid signal for the external health test interface. When asserted, it indicates that `entropy_src_xht_bits`, `entropy_src_xht_bit_sel`, and `entropy_src_xht_meta` are valid for consumption by the external health test.                                                                                                   |
| entropy_src_xht_bits               | logic                                 | uni     | req   | RngBusWidth           | Carries the raw entropy data from the entropy source to be consumed by the external health test module. The data on this bus is valid when `entropy_src_xht_valid` is asserted. The width is determined by `RngBusWidth` parametrization.                                                                                    |
| entropy_src_xht_bit_sel            | logic                                 | uni     | req   | RngBusBitSelWidth     | Provides bit selection information for the raw entropy data. It specifies which specific bit or subset of bits from `entropy_src_xht_bit` should be used. The width is determined by `RngBusBitSelWidth` parametrization.                                                                                                    |
| entropy_src_xht_health_test_window | logic                                 | uni     | req   | HealthTestWindowWidth | Provides the window size of the health in bits.                                                                                                                                                                                                                                                                              |
| entropy_src_xht_meta               | entropy_src_pkg::entropy_src_xht_meta | req_rsp | req   | 1                     |                                                                                                                                                                                                                                                                                                                              |
| otp_en_entropy_src_fw_read         | prim_mubi_pkg::mubi8                  | uni     | rcv   | 1                     |                                                                                                                                                                                                                                                                                                                              |
| otp_en_entropy_src_fw_over         | prim_mubi_pkg::mubi8                  | uni     | rcv   | 1                     |                                                                                                                                                                                                                                                                                                                              |
| rng_fips                           | logic                                 | uni     | req   | 1                     |                                                                                                                                                                                                                                                                                                                              |
| tl                                 | tlul_pkg::tl                          | req_rsp | rsp   | 1                     |                                                                                                                                                                                                                                                                                                                              |

## Interrupts

| Interrupt Name        | Type   | Description                                                                                                                                                                                         |
|:----------------------|:-------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| es_entropy_valid      | Event  | Asserted when entropy source bits are available for firmware for consumption via [`ENTROPY_DATA`](registers.md#entropy_data) register.                                                              |
| es_health_test_failed | Event  | Asserted whenever the main state machine is in the alert state, e.g., due to health tests failing and reaching the threshold value configured in [`ALERT_THRESHOLD.`](registers.md#alert_threshold) |
| es_observe_fifo_ready | Event  | Asserted when the observe FIFO has filled to the configured threshold level (see [`OBSERVE_FIFO_THRESH`](registers.md#observe_fifo_thresh)).                                                        |
| es_fatal_err          | Event  | Asserted when an fatal error condition is met, e.g., upon FIFO errors, or if an illegal state machine state is reached.                                                                             |

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
| ENTROPY_SRC.FIFO.CTR.REDUN                | The FIFO pointers of several FIFOs are implemented with duplicate counters.         |
| ENTROPY_SRC.CTR.REDUN                     | Counter hardening for all health test counters.                                     |
| ENTROPY_SRC.CTR.LOCAL_ESC                 | Redundant counter failures will cause a local escalation to the main state machine. |
| ENTROPY_SRC.ESFINAL_RDATA.BUS.CONSISTENCY | Comparison on successive bus values for the post-conditioned entropy seed bus.      |
| ENTROPY_SRC.TILE_LINK.BUS.INTEGRITY       | Tilelink end-to-end bus integrity scheme.                                           |


<!-- END CMDGEN -->
