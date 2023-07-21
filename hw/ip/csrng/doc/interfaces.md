# Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/csrng/data/csrng.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`csrng`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name                | Package::Struct                    | Type    | Act   |   Width | Description                                                                                                                                                                                                               |
|:-------------------------|:-----------------------------------|:--------|:------|--------:|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| csrng_cmd                | csrng_pkg::csrng                   | req_rsp | rsp   |       2 |                                                                                                                                                                                                                           |
| entropy_src_hw_if        | entropy_src_pkg::entropy_src_hw_if | req_rsp | req   |       1 |                                                                                                                                                                                                                           |
| cs_aes_halt              | entropy_src_pkg::cs_aes_halt       | req_rsp | rsp   |       1 | Coordinate activity between CSRNG's AES and Entropy Source's SHA3. When CSRNG gets a request and its AES is not active, it acknowledges and until the request has dropped neither runs its AES nor drops the acknowledge. |
| otp_en_csrng_sw_app_read | prim_mubi_pkg::mubi8               | uni     | rcv   |       1 |                                                                                                                                                                                                                           |
| lc_hw_debug_en           | lc_ctrl_pkg::lc_tx                 | uni     | rcv   |       1 |                                                                                                                                                                                                                           |
| tl                       | tlul_pkg::tl                       | req_rsp | rsp   |       1 |                                                                                                                                                                                                                           |

## Interrupts

| Interrupt Name   | Type   | Description                                                                                                                         |
|:-----------------|:-------|:------------------------------------------------------------------------------------------------------------------------------------|
| cs_cmd_req_done  | Event  | Asserted when a command request is completed.                                                                                       |
| cs_entropy_req   | Event  | Asserted when a request for entropy has been made.                                                                                  |
| cs_hw_inst_exc   | Event  | Asserted when a hardware-attached CSRNG instance encounters a command exception                                                     |
| cs_fatal_err     | Event  | Asserted when a FIFO error or a fatal alert occurs. Check the [`ERR_CODE`](registers.md#err_code) register to get more information. |

## Security Alerts

| Alert Name   | Description                                                                                                                                                                               |
|:-------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| recov_alert  | This alert is triggered when a recoverable alert occurs.  Check the [`RECOV_ALERT_STS`](registers.md#recov_alert_sts) register to get more information.                                   |
| fatal_alert  | This alert triggers (i) if an illegal state machine state is reached, or (ii) if an AES fatal alert condition occurs, or (iii) if a fatal integrity failure is detected on the TL-UL bus. |

## Security Countermeasures

| Countermeasure ID                   | Description                                                                                                                                                                                                                                                         |
|:------------------------------------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| CSRNG.CONFIG.REGWEN                 | Registers are protected from writes.                                                                                                                                                                                                                                |
| CSRNG.CONFIG.MUBI                   | Registers have multi-bit encoded fields.                                                                                                                                                                                                                            |
| CSRNG.INTERSIG.MUBI                 | OTP signal used to enable software access to registers.                                                                                                                                                                                                             |
| CSRNG.MAIN_SM.FSM.SPARSE            | The CSRNG main state machine uses a sparse state encoding.                                                                                                                                                                                                          |
| CSRNG.UPDATE.FSM.SPARSE             | The CSRNG update state machine uses a sparse state encoding.                                                                                                                                                                                                        |
| CSRNG.BLK_ENC.FSM.SPARSE            | The CSRNG block encrypt state machine uses a sparse state encoding.                                                                                                                                                                                                 |
| CSRNG.OUTBLK.FSM.SPARSE             | The CSRNG block output state machine uses a sparse state encoding.                                                                                                                                                                                                  |
| CSRNG.GEN_CMD.CTR.REDUN             | The generate command uses a counter that is protected by a second counter that counts in the opposite direction.                                                                                                                                                    |
| CSRNG.DRBG_UPD.CTR.REDUN            | The ctr_drbg update algorthm uses a counter that is protected by a second counter that counts in the opposite direction.                                                                                                                                            |
| CSRNG.DRBG_GEN.CTR.REDUN            | The ctr_drbg generate algorthm uses a counter that is protected by a second counter that counts in the opposite direction.                                                                                                                                          |
| CSRNG.CTRL.MUBI                     | Multi-bit field used for selection control.                                                                                                                                                                                                                         |
| CSRNG.MAIN_SM.CTR.LOCAL_ESC         | A mismatch detected inside any CSRNG counter moves the  main state machine into a terminal error state.                                                                                                                                                             |
| CSRNG.CONSTANTS.LC_GATED            | Seed diversification based on the lifecycle state.                                                                                                                                                                                                                  |
| CSRNG.SW_GENBITS.BUS.CONSISTENCY    | Comparison on successive bus values for genbits returned on the software channel.                                                                                                                                                                                   |
| CSRNG.TILE_LINK.BUS.INTEGRITY       | Tilelink end-to-end bus integrity scheme.                                                                                                                                                                                                                           |
| CSRNG.AES_CIPHER.FSM.SPARSE         | The AES cipher core FSM uses a sparse state encoding. See the AES module documentation for AES-specific countermeasures.                                                                                                                                            |
| CSRNG.AES_CIPHER.FSM.REDUN          | The AES cipher core FSM uses multiple, independent logic rails. See the AES module documentation for AES-specific countermeasures.                                                                                                                                  |
| CSRNG.AES_CIPHER.CTRL.SPARSE        | Critical control signals for the AES cipher core such as handshake and MUX control signals use sparse encodings. See the AES module documentation for AES-specific countermeasures.                                                                                 |
| CSRNG.AES_CIPHER.FSM.LOCAL_ESC      | The AES cipher core FSM moves to a terminal error state upon local escalation. Can be triggered by AES_CIPHER.FSM.SPARSE, AES_CIPHER.FSM.REDUN, AES_CIPHER.CTR.REDUN and AES_CIPHER.CTRL.SPARSE. See the AES module documentation for AES-specific countermeasures. |
| CSRNG.AES_CIPHER.CTR.REDUN          | The AES round counter inside the AES cipher core FSM is protected with multiple, independent logic rails. See the AES module documentation for AES-specific countermeasures.                                                                                        |
| CSRNG.AES_CIPHER.DATA_REG.LOCAL_ESC | Upon local escalation, the AES cipher core doesn't output intermediate state. See the AES module documentation for AES-specific countermeasures.                                                                                                                    |


<!-- END CMDGEN -->

## Other CSRNG signals.

Signal                       | Direction        | Type                        | Description
-----------------------------|------------------|-----------------------------|---------------
`otp_en_csrng_sw_app_read_i` | `input `         | `otp_en_t `                 | An efuse that will enable firmware to access the NIST CTR_DRBG internal state and genbits through registers.
`lc_hw_debug_en_i`           | `input`          | `lc_tx_t `                  | A life-cycle that will select which diversification value is used for xoring with the seed from ENTROPY_SRC.
`entropy_src_hw_if_o`        | `output`         | `entropy_src_hw_if_req_t`   | Seed request made to the ENTROPY_SRC module.
`entropy_src_hw_if_i`        | `input`          | `entropy_src_hw_if_rsp_t`   | Seed response from the ENTROPY_SRC module.
`cs_aes_halt_i`              | `input`          | `cs_aes_halt_req_t`         | Request to CSRNG from ENTROPY_SRC to halt requests to the AES block for power leveling purposes.
`cs_aes_halt_o`              | `output`         | `cs_aes_halt_rsp_t`         | Response from CSRNG to ENTROPY_SRC that all requests to AES block are halted.
`csrng_cmd_i`                | `input`          | `csrng_req_t`               | Application interface request to CSRNG from an EDN block.
`csrng_cmd_o`                | `output`         | `csrng_rsp_t`               | Application interface response from CSRNG to an EDN block.
