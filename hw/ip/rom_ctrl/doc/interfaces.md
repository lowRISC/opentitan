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

Parameter                   | Default (Max)         | Top Earlgrey | Description
----------------------------|-----------------------|--------------|---------------
`RndCnstRomKey`             | (see RTL)             | (see RTL)    | Compile-time random default constant for scrambling key (used in `prim_prince` block).
`RndCnstRomNonce`           | (see RTL)             | (see RTL)    | Compile-time random default constant for scrambling nonce (used in `prim_prince` block and the two S&P blocks).

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
        A structure with two fields.
        The first, <code>done</code>, becomes true when the ROM check is complete and remains true until reset.
      </p><p>
        The second, <code>good</code>, is only valid if <code>done</code> is true.
        This is true if the digest computation matched the expected value stored in the top words of ROM and false otherwise.
        This field stays constant when <code>done</code> is true.
      </p>
    </td>
  </tr>

  <tr>
    <td><code>keymgr_data_o</code></td>
    <td><code>rom_ctrl_pkg::keymgr_data_t</code></td>
    <td>keymgr</td>
    <td>
      A 256-bit digest, together with a <code>valid</code> signal.
      Once the ROM check is complete, <code>valid</code> will become true and will then remain true until reset.
      The digest in <code>data</code> is only valid when <code>valid</code> is true and is be constant until reset.
    </td>
  </tr>

  <tr>
    <td><code>kmac_data_o</code></td>
    <td>kmac_pkg::app_req_t</td>
    <td>kmac</td>
    <td>
      Outgoing data to KMAC.
      Data is sent in 64-bit words in the <code>data</code> field.
      When a word of data is available, the <code>valid</code> field is true.
      When this is the last word of data, the <code>last</code> field is also true.
      Since we never send partial words, the <code>strb</code> field is always zero.
    </td>
  </tr>
  <tr>
    <td><code>kmac_data_i</code></td>
    <td>kmac_pkg::app_rsp_t</td>
    <td>kmac</td>
    <td>
      Incoming data from KMAC interface.
      This contains a <code>ready</code> signal for passing ROM data and a <code>done</code> signal that shows a digest has been computed.
      When <code>done</code> is true, the digest is exposed in two shares (<code>digest_share0</code> and <code>digest_share1</code>).
      The <code>error</code> field is ignored.
    </td>
  </tr>
</table>
