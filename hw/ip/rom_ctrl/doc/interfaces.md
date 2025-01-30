# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/rom_ctrl/data/rom_ctrl.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`rom_ctrl`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`regs_tl`**, **`rom_tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*
- Interrupts: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name   | Package::Struct           | Type    | Act   |   Width | Description   |
|:------------|:--------------------------|:--------|:------|--------:|:--------------|
| rom_cfg     | prim_rom_pkg::rom_cfg     | uni     | rcv   |       1 |               |
| pwrmgr_data | rom_ctrl_pkg::pwrmgr_data | uni     | req   |       1 |               |
| keymgr_data | rom_ctrl_pkg::keymgr_data | uni     | req   |       1 |               |
| kmac_data   | kmac_pkg::app             | req_rsp | req   |       1 |               |
| regs_tl     | tlul_pkg::tl              | req_rsp | rsp   |       1 |               |
| rom_tl      | tlul_pkg::tl              | req_rsp | rsp   |       1 |               |

## Security Alerts

| Alert Name   | Description                                                                              |
|:-------------|:-----------------------------------------------------------------------------------------|
| fatal        | A fatal error. Fatal alerts are non-recoverable and will be asserted until a hard reset. |

## Security Countermeasures

| Countermeasure ID                      | Description                                                                                                                                                                                                                                                                                                                                                   |
|:---------------------------------------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| ROM_CTRL.CHECKER.CTR.CONSISTENCY       | Once rom_ctrl has handed control of the mux to the bus, the internal FSM counter should point at the top of ROM (where we ensure the word has invalid ECC bits). The unexpected_counter_change signal in rom_ctrl_fsm goes high and generates a fatal alert if that counter is perturbed in any way.                                                          |
| ROM_CTRL.CHECKER.CTRL_FLOW.CONSISTENCY | The main checker FSM steps on internal 'done' signals, coming from its address counter, the KMAC response and its comparison counter. If any of these are asserted at times we don't expect, the FSM jumps to an invalid state. This triggers an alert and will not set the external 'done' signal for pwrmgr to continue boot.                               |
| ROM_CTRL.CHECKER.FSM.LOCAL_ESC         | The main checker FSM moves to an invalid state on local escalation.                                                                                                                                                                                                                                                                                           |
| ROM_CTRL.COMPARE.CTRL_FLOW.CONSISTENCY | The hash comparison module triggers a fatal error if the checker FSM triggers a second comparison after a reset. This is handled by the start_alert signal in the rom_ctrl_compare module and could be triggered if the checker FSM was somehow glitched to jump backwards.                                                                                   |
| ROM_CTRL.COMPARE.CTR.CONSISTENCY       | The hash comparison module has an internal count (indexing 32-bit words in the 256-bit digests). If this glitches to a nonzero value before the comparison starts or to a value other than the last index after the comparison ends then an fatal alert is generated. This is handled by the wait_addr_alert and done_addr_alert signals in rom_ctrl_compare. |
| ROM_CTRL.COMPARE.CTR.REDUN             | The hash comparison module has an internal count (indexing 32-bit words in the 256-bit digests) implemented using a redundant counter module. In case a mismatch is detected between the redundant counters a fatal alert is generated.                                                                                                                       |
| ROM_CTRL.FSM.SPARSE                    | FSMs are sparsely encoded. There are two FSMs. The first is in rom_ctrl_fsm. The second, simpler FSM is in rom_ctrl_compare.                                                                                                                                                                                                                                  |
| ROM_CTRL.MEM.SCRAMBLE                  | The ROM is scrambled.                                                                                                                                                                                                                                                                                                                                         |
| ROM_CTRL.MEM.DIGEST                    | A cSHAKE digest is computed of the ROM contents.                                                                                                                                                                                                                                                                                                              |
| ROM_CTRL.INTERSIG.MUBI                 | Checker FSM 'done' signal is multi-bit encoded when passed to pwrmgr. This signal is derived from the (multi-bit) sparse FSM state in the rom_ctrl_fsm module.                                                                                                                                                                                                |
| ROM_CTRL.BUS.INTEGRITY                 | TL bus control and data signals are integrity protected (using the system-wide end-to-end integrity scheme).                                                                                                                                                                                                                                                  |
| ROM_CTRL.BUS.LOCAL_ESC                 | To avoid responding to a request with erroneous data, even though an alert went out, the bus_rom_rvalid signal used to signal a response to the ROM-side TL bus can only be high if no internal consistency error has been spotted.                                                                                                                           |
| ROM_CTRL.MUX.MUBI                      | The mux that arbitrates between the checker and the bus is multi-bit encoded. An invalid value generates a fatal alert with the sel_invalid signal in the rom_ctrl_mux module.                                                                                                                                                                                |
| ROM_CTRL.MUX.CONSISTENCY               | The mux that arbitrates between the checker and the bus gives access to the checker at the start of time and then switches to the bus, never going back. If a glitch does cause it to switch back, a fatal alert is generated with the sel_reverted or sel_q_reverted signals in the rom_ctrl_mux module.                                                     |
| ROM_CTRL.CTRL.REDUN                    | Addresses from TL accesses are passed redundantly to the scrambled ROM module, to ensure the address lines are not independently faultable downstream of the bus integrity ECC check. See the bus_rom_prince_index and bus_rom_rom_index signals in the rom_ctrl module.                                                                                      |
| ROM_CTRL.CTRL.MEM.INTEGRITY            | End-to-end data/memory integrity scheme.                                                                                                                                                                                                                                                                                                                      |
| ROM_CTRL.TLUL_FIFO.CTR.REDUN           | The TL-UL response FIFO pointers are implemented with duplicate counters.                                                                                                                                                                                                                                                                                     |


<!-- END CMDGEN -->

## Parameters

The top-level `rom_ctrl` module has several parameters, although some of them are only relevant for verification.
Those parameters are described separately below.
The parameters that have an effect on the generated block are:

Parameter         | Default (Max)                 | Top Earlgrey                                       | Description
------------------|-------------------------------|----------------------------------------------------|---------------
`AlertAsyncOn`    | True                          | True                                               | This is passed to the single `prim_alert_sender` instance and causes it to generate synchronization logic to support alert rx and tx being on different clocks.
`RndCnstRomNonce` | `RND_CNST_SCR_NONCE` (define) | `top_earlgrey_rnd_cnst_pkg::RndCnstRomCtrlScrNonce`| Compile-time random default constant for scrambling nonce (used in `prim_prince` block and the S&P block).
`RndCnstRomKey`   | `RND_CNST_SCR_KEY` (define)   | `top_earlgrey_rnd_cnst_pkg::RndCnstRomCtrlScrKey`  | 128-bit compile-time random default constant for scrambling key (used in `prim_prince` block).
`MemSizeRom`      | 64kB                          | 32kB                                               | The size of the ROM itself

The parameters that are only used at verification time are:

Parameter                   | Description
----------------------------|---------------
`BootRomInitFile`           | This is the path of a vmem file that can be loaded to populate the ROM in a test. Used for FPGA testing.
`SecDisableScrambling`      | A flag that tells `rom_ctrl` not to scramble its backing memory. The result is less secure, but much smaller (used for `top_englishbreakfast`)

## Signals

The table below lists other ROM controller inter-module signals.

<table>
  <tr>
    <th>Signal</th>
    <th>Type</th>
    <th>Destination</th>
    <th>Description</th>
  </tr>
  <tr>
    <td><code>pwrmgr_data_o</code></td>
    <td><code>rom_ctrl_pkg::pwrmgr_data_t</code></td>
    <td>pwrmgr</td>
    <td>
      <p>
        A structure with two fields: <code>done</code> and <code>good</code>.
        Both of these fields are encoded as <code>mubi4_t</code>.
        Barring fault injection, in the <code>rom_ctrl</code> block, both fields will always be valid.
      </p><p>
        The <code>done</code> field is initially <code>MuBi4False</code>.
        It only becomes <code>MuBi4True</code> after the contents of the ROM have been read.
        This switch happens immediately after <code>rom_ctrl</code> has received the digest from kmac and compared it with the expected digest at the top of the ROM.
      </p><p>
        The <code>good</code> field is only valid if <code>done</code> is <code>MuBi4True</code>.
        The field is <code>MuBi4True</code> if the digest computation matched the expected value stored in the top words of ROM and <code>MuBi4False</code> otherwise.
        This field does not change after <code>done</code> becomes true.
      </p>
    </td>
  </tr>

  <tr>
    <td><code>keymgr_data_o</code></td>
    <td><code>rom_ctrl_pkg::keymgr_data_t</code></td>
    <td>keymgr</td>
    <td>
      <p>
        A 256-bit digest in the <code>data</code>, together with a <code>valid</code> signal.
        Once the ROM check is complete, <code>valid</code> will become high and will then remain high until reset.
        This change happens at the same time as <code>pwrmgr_data_o.done</code> becomes <code>MuBi4True</code>.
      </p><p>
        The digest in <code>data</code> is the digest that was computed by kmac.
        The contents of the field are supplied from copy of this digest, stored in the <code>DIGEST_*</code> CSRs.
      </p>
    </td>
  </tr>

  <tr>
    <td><code>kmac_data_o</code></td>
    <td><code>kmac_pkg::app_req_t</code></td>
    <td>kmac</td>
    <td>
      <p>
        The request side of a request/response interface with kmac.
        The ROM controller only sends KMAC requests when it is doing its initial read of the ROM.
        It will request exactly one KMAC checksum calculation after each reset.
        As such, there will be no more requests after the one containing the top word of the ROM image.
      </p><p>
        The <code>valid</code> field is true if there is a request on this cycle.
        This forms a rdy/vld interface with the <code>ready</code> field of <code>kmac_data_i</code>.
        The <code>data</code> field is the word that has been read from the ROM.
      </p><p>
        The <code>app_req_t</code> format supports up to 64 bits in a cycle but the ROM will only send one word.
        This word gets sent as the low bytes of <code>data</code> and the <code>strb</code> field is set to a constant value showing them.
        That strobe value will enable just the bytes used: 5 bytes per word if scrambling is enabled; 4 bytes per word if not.
        When sending the top word of the ROM image, the ROM controller will set the <code>last</code> field to true.
      </p>
    </td>
  </tr>
  <tr>
    <td><code>kmac_data_i</code></td>
    <td><code>kmac_pkg::app_rsp_t</code></td>
    <td>kmac</td>
    <td>
      <p>
        The response side of a request/response interface with kmac.
        The <code>ready</code> field is part of a rdy/vld handshake for the request using the <code>valid</code> field of <code>kmac_data_o</code>.
        The <code>done</code> field is true when there is a digest available on this cycle.
        The following fields only have a defined meaning when <code>done</code> is true.
        For the interface with ROM controller, we expect this to happen exactly once after a reset.
      </p><p>
        The <code>digest_share0</code> and <code>digest_share1</code> fields contain the computed digest in two shares.
        The <code>error</code> field is true if there was some error in the KMAC checksum calculation.
        If this happens, the ROM controller will move to an invalid state and generate an alert.
      </p>
    </td>
  </tr>
</table>
