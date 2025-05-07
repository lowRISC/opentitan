# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/top_earlgrey/ip_autogen/alert_handler/data/alert_handler.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`alert_handler`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`clk_edn_i`**
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*
- Security Alerts: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name   | Package::Struct                    | Type    | Act   |   Width | Description   |
|:------------|:-----------------------------------|:--------|:------|--------:|:--------------|
| crashdump   | alert_handler_pkg::alert_crashdump | uni     | req   |       1 |               |
| edn         | edn_pkg::edn                       | req_rsp | req   |       1 |               |
| esc_rx      | prim_esc_pkg::esc_rx               | uni     | rcv   |       4 |               |
| esc_tx      | prim_esc_pkg::esc_tx               | uni     | req   |       4 |               |
| tl          | tlul_pkg::tl                       | req_rsp | rsp   |       1 |               |

## Interrupts

| Interrupt Name   | Type   | Description                                                                                                                |
|:-----------------|:-------|:---------------------------------------------------------------------------------------------------------------------------|
| classa           | Event  | Interrupt state bit of Class A. Set by HW in case an alert within this class triggered. Defaults true, write one to clear. |
| classb           | Event  | Interrupt state bit of Class B. Set by HW in case an alert within this class triggered. Defaults true, write one to clear. |
| classc           | Event  | Interrupt state bit of Class C. Set by HW in case an alert within this class triggered. Defaults true, write one to clear. |
| classd           | Event  | Interrupt state bit of Class D. Set by HW in case an alert within this class triggered. Defaults true, write one to clear. |

## Security Countermeasures

| Countermeasure ID                        | Description                                                                                                                                                                                                                         |
|:-----------------------------------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| ALERT_HANDLER.BUS.INTEGRITY              | End-to-end bus integrity scheme.                                                                                                                                                                                                    |
| ALERT_HANDLER.CONFIG.SHADOW              | Important CSRs are shadowed.                                                                                                                                                                                                        |
| ALERT_HANDLER.PING_TIMER.CONFIG.REGWEN   | The ping timer configuration registers are REGWEN protected.                                                                                                                                                                        |
| ALERT_HANDLER.ALERT.CONFIG.REGWEN        | The individual alert enables are REGWEN protected.                                                                                                                                                                                  |
| ALERT_HANDLER.ALERT_LOC.CONFIG.REGWEN    | The individual local alert enables are REGWEN protected.                                                                                                                                                                            |
| ALERT_HANDLER.CLASS.CONFIG.REGWEN        | The class configuration registers are REGWEN protected.                                                                                                                                                                             |
| ALERT_HANDLER.ALERT.INTERSIG.DIFF        | Differentially encoded alert channels.                                                                                                                                                                                              |
| ALERT_HANDLER.LPG.INTERSIG.MUBI          | LPG signals are encoded with MUBI types.                                                                                                                                                                                            |
| ALERT_HANDLER.ESC.INTERSIG.DIFF          | Differentially encoded escalation channels.                                                                                                                                                                                         |
| ALERT_HANDLER.ALERT_RX.INTERSIG.BKGN_CHK | Periodic background checks on alert channels (ping mechanism).                                                                                                                                                                      |
| ALERT_HANDLER.ESC_TX.INTERSIG.BKGN_CHK   | Periodic background checks on escalation channels (ping mechanism).                                                                                                                                                                 |
| ALERT_HANDLER.ESC_RX.INTERSIG.BKGN_CHK   | Escalation receivers can detect absence of periodic ping requests.                                                                                                                                                                  |
| ALERT_HANDLER.ESC_TIMER.FSM.SPARSE       | Escalation timer FSMs are sparsely encoded.                                                                                                                                                                                         |
| ALERT_HANDLER.PING_TIMER.FSM.SPARSE      | Ping timer FSM is sparsely encoded.                                                                                                                                                                                                 |
| ALERT_HANDLER.ESC_TIMER.FSM.LOCAL_ESC    | Escalation timer FSMs move into an invalid state upon local escalation.                                                                                                                                                             |
| ALERT_HANDLER.PING_TIMER.FSM.LOCAL_ESC   | Ping timer FSM moves into an invalid state upon local escalation.                                                                                                                                                                   |
| ALERT_HANDLER.ESC_TIMER.FSM.GLOBAL_ESC   | The escalation timer FSMs are the root of global escalation, hence if any of them moves into an invalid state by virtue of ESC_TIMER.FSM.LOCAL_ESC, this will trigger all escalation actions and thereby global escalation as well. |
| ALERT_HANDLER.ACCU.CTR.REDUN             | Accumulator counters employ a cross-counter implementation.                                                                                                                                                                         |
| ALERT_HANDLER.ESC_TIMER.CTR.REDUN        | Escalation timer counters employ a duplicated counter implementation.                                                                                                                                                               |
| ALERT_HANDLER.PING_TIMER.CTR.REDUN       | Ping timer counters employ a duplicated counter implementation.                                                                                                                                                                     |
| ALERT_HANDLER.PING_TIMER.LFSR.REDUN      | Ping timer LFSR is redundant.                                                                                                                                                                                                       |


<!-- END CMDGEN -->
