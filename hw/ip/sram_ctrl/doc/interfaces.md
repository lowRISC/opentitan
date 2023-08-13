# Hardware Interfaces

## Parameters

The following table lists the instantiation parameters of the SRAM controller.

Parameter                   | Default               | Top Earlgrey      | Description
----------------------------|-----------------------|-------------------|---------------
`AlertAsyncOn`              | 1'b1                  | 1'b1              |
`InstrExec`                 | 1                     | 1                 | Enables the execute from SRAM feature.
`MemSizeRam`                | 4096                  | (multiple values) | Number of 32bit words in the SRAM (can be overridden by `topgen`).
`RndCnstSramKey`            | (see RTL)             | (see RTL)         | Compile-time random default constant for scrambling key.
`RndCnstSramNonce`          | (see RTL)             | (see RTL)         | Compile-time random default constant for scrambling nonce.
`RndCnstLfsrSeed`           | (see RTL)             | (see RTL)         | Compile-time random default constant for LFSR seed.
`RndCnstLfsrPerm`           | (see RTL)             | (see RTL)         | Compile-time random default constant for LFSR permutation.

## Signals

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/sram_ctrl/data/sram_ctrl.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`sram_ctrl`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`clk_otp_i`**
- Bus Device Interfaces (TL-UL): **`regs_tl`**, **`ram_tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*
- Interrupts: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name          | Package::Struct             | Type    | Act   |   Width | Description   |
|:-------------------|:----------------------------|:--------|:------|--------:|:--------------|
| sram_otp_key       | otp_ctrl_pkg::sram_otp_key  | req_rsp | req   |       1 |               |
| cfg                | prim_ram_1p_pkg::ram_1p_cfg | uni     | rcv   |       1 |               |
| lc_escalate_en     | lc_ctrl_pkg::lc_tx          | uni     | rcv   |       1 |               |
| lc_hw_debug_en     | lc_ctrl_pkg::lc_tx          | uni     | rcv   |       1 |               |
| otp_en_sram_ifetch | prim_mubi_pkg::mubi8        | uni     | rcv   |       1 |               |
| regs_tl            | tlul_pkg::tl                | req_rsp | rsp   |       1 |               |
| ram_tl             | tlul_pkg::tl                | req_rsp | rsp   |       1 |               |

## Security Alerts

| Alert Name   | Description                                                                                                                                        |
|:-------------|:---------------------------------------------------------------------------------------------------------------------------------------------------|
| fatal_error  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected, or if the initialization mechanism has reached an invalid state. |

## Security Countermeasures

| Countermeasure ID                      | Description                                                                                                                                                                 |
|:---------------------------------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| SRAM_CTRL.BUS.INTEGRITY                | End-to-end bus integrity scheme.                                                                                                                                            |
| SRAM_CTRL.CTRL.CONFIG.REGWEN           | The SRAM control register is protected by a REGWEN.                                                                                                                         |
| SRAM_CTRL.EXEC.CONFIG.REGWEN           | The SRAM execution enable register is protected by a REGWEN.                                                                                                                |
| SRAM_CTRL.EXEC.CONFIG.MUBI             | The SRAM execution enable register is multibit encoded.                                                                                                                     |
| SRAM_CTRL.EXEC.INTERSIG.MUBI           | The SRAM execution enable signal coming from OTP is multibit encoded.                                                                                                       |
| SRAM_CTRL.LC_ESCALATE_EN.INTERSIG.MUBI | The life cycle escalation enable signal is multibit encoded.                                                                                                                |
| SRAM_CTRL.LC_HW_DEBUG_EN.INTERSIG.MUBI | The life cycle hardware debug enable signal is multibit encoded.                                                                                                            |
| SRAM_CTRL.MEM.INTEGRITY                | End-to-end data/memory integrity scheme.                                                                                                                                    |
| SRAM_CTRL.MEM.SCRAMBLE                 | Data is scrambled with a keyed reduced-round PRINCE cipher in CTR mode.                                                                                                     |
| SRAM_CTRL.ADDR.SCRAMBLE                | Address is scrambled with a keyed lightweight permutation/diffusion function.                                                                                               |
| SRAM_CTRL.INSTR.BUS.LC_GATED           | Prevent code execution from SRAM in non-test lifecycle states.                                                                                                              |
| SRAM_CTRL.RAM_TL_LC_GATE.FSM.SPARSE    | The control FSM inside the TL-UL gating primitive is sparsely encoded.                                                                                                      |
| SRAM_CTRL.KEY.GLOBAL_ESC               | Scrambling key and nonce are reset to a fixed value upon escalation, and bus transactions going to the memory will be blocked.                                              |
| SRAM_CTRL.KEY.LOCAL_ESC                | Scrambling key and nonce are reset to a fixed value upon local escalation due to bus integrity or counter errors, and bus transactions going to the memory will be blocked. |
| SRAM_CTRL.INIT.CTR.REDUN               | The initialization counter is duplicated.                                                                                                                                   |
| SRAM_CTRL.SCRAMBLE.KEY.SIDELOAD        | The scrambling key is sideloaded from OTP and thus unreadable by SW.                                                                                                        |
| SRAM_CTRL.TLUL_FIFO.CTR.REDUN          | The TL-UL response FIFO pointers are implemented with duplicate counters.                                                                                                   |


<!-- END CMDGEN -->

The table below lists other SRAM controller signals.

Signal                     | Direction        | Type                               | Description
---------------------------|------------------|------------------------------------|---------------
`lc_hw_debug_en_i`         | `input`          | `lc_ctrl_pkg::lc_tx_t`             | Multibit life cycle hardware debug enable signal coming from life cycle controller, asserted when the hardware debug mechanisms are enabled in the system.
`lc_escalate_en_i`         | `input`          | `lc_ctrl_pkg::lc_tx_t`             | Multibit life cycle escalation enable signal coming from life cycle controller, asserted if an escalation has occurred.
`sram_otp_key_o`           | `output`         | `otp_ctrl_pkg::sram_otp_key_req_t` | Key derivation request going to the key derivation interface of the OTP controller.
`sram_otp_key_i`           | `input`          | `otp_ctrl_pkg::sram_otp_key_rsp_t` | Ephemeral scrambling key coming back from the key derivation interface of the OTP controller.
`otp_en_sram_ifetch_i`     | `input`          | `otp_ctrl_pkg::mubi8_t`            | Multibit value coming from the OTP HW_CFG partition ([EN_SRAM_IFETCH](../../otp_ctrl/README.md#direct-access-memory-map)), set to kMuBi8True in order to enable the [`EXEC`](../data/sram_ctrl.hjson#exec) CSR.
`cfg_i`                    | `input`          | `logic [CfgWidth-1:0]`             | Attributes for physical memory macro.

### Interfaces to OTP and the SRAM Scrambling Primitive

The interface to the key derivation interface inside the OTP controller follows a simple req / ack protocol, where the SRAM controller first requests an updated ephemeral key by asserting the `sram_otp_key_i.req`.
The OTP controller then fetches entropy from CSRNG and derives an ephemeral key using the SRAM_DATA_KEY_SEED and the PRESENT scrambling data path as described in the [OTP controller spec](../../otp_ctrl/README.md#scrambling-datapath).
Finally, the OTP controller returns a fresh ephemeral key via the response channels (`sram_otp_key_o[*]`, `otbn_otp_key_o`), which complete the req / ack handshake.
The key and nonce are made available to the scrambling primitive in the subsequent cycle.
The wave diagram below illustrates this process.

```wavejson
{signal: [
  {name: 'clk_otp_i',                 wave: 'p...........'},
  {name: 'sram_otp_key_o.req',        wave: '0.|1.|..0|..'},
  {name: 'sram_otp_key_i.ack',        wave: '0.|..|.10|..'},
  {name: 'sram_otp_key_i.nonce',      wave: '0.|..|.30|..'},
  {name: 'sram_otp_key_i.key',        wave: '0.|..|.30|..'},
  {name: 'sram_otp_key_i.seed_valid', wave: '0.|..|.10|..'},
  {},
  {name: 'clk_i',                     wave: 'p...........'},
  {name: 'key_valid_q',               wave: '10|..|...|1.'},
  {name: 'key_q',                     wave: '4.|..|...|3.'},
  {name: 'nonce_q',                   wave: '4.|..|...|3.'},
  {name: 'key_seed_valid_q',          wave: '4.|..|...|3.'},
]}
```

If the key seeds have not yet been provisioned in OTP, the keys are derived from all-zero constants, and the `*.seed_valid` signal will be set to 0 in the response.
It should be noted that this mechanism requires the CSRNG and entropy distribution network to be operational, and a key derivation request will block if they are not.

Note that the req/ack protocol runs on `clk_otp_i`.
The SRAM controller synchronizes the data over via a req/ack handshake primitive `prim_sync_reqack.sv` primitive as shown below.

![OTP Key Req Ack](../../otp_ctrl/doc/otp_ctrl_key_req_ack.svg)

Note that the key and nonce output signals on the OTP controller side are guaranteed to remain stable for at least 62 OTP clock cycles after the `ack` signal is pulsed high, because the derivation of a 64bit half-key takes at least two passes through the 31-cycle PRESENT primitive.
Hence, if the SRAM controller clock `clk_i` is faster or in the same order of magnitude as `clk_otp_i`, the data can be directly sampled upon assertion of `src_ack_o`.
If the SRAM controller runs on a significantly slower clock than OTP, an additional register (as indicated with dashed grey lines in the figure) has to be added.

### Global and Local Escalation

If `lc_escalate_en_i` is set to any different value than `lc_ctrl_pkg::Off`, the current scrambling keys are discarded and reset to `RndCnstSramKey` and `RndCnstSramNonce` in the subsequent cycle.
Any subsequent memory request to `prim_ram_1p_scr` will then be blocked as well.
This mechanism is part of the [life cycle](../../lc_ctrl/README.md) state scrapping and secret wiping countermeasure triggered by the alert handler (global escalation).

Note that if any local bus integrity or counter errors are detected, the SRAM controller will locally escalate without assertion of `lc_escalate_en_i`.
The behavior of local escalation is identical to global escalation via `lc_escalate_en_i`.
