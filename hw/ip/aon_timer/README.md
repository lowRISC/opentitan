# AON Timer Technical Specification
<!-- BEGIN AUTOGEN from util/mdbook_regression_links.py -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`aon_timer`](https://nightly.reports.lowrisc.org/opentitan_weekly_earlgrey/2026_03_08/index.html) | 2.0.0 | D3, V3 | <img src="https://img.shields.io/badge/Tests_Running-315-blue"> <img src="https://img.shields.io/badge/Tests_Passing-100.00%25-brightgreen"> <img src="https://img.shields.io/badge/Functional_Coverage-100.00%25-brightgreen"> <img src="https://img.shields.io/badge/Code_Coverage-98.81%25-brightgreen"> |

This IP has been taped out in Earl Grey 1.0.0. The corresponding documentation and regression results can be found [here](https://opentitan.org/earlgrey_1.0.0/book/hw/ip/aon_timer/index.html).
<!-- END AUTOGEN -->

## Overview

The Always-On ("AON") Timer contains two upcounting timers, designed to run in the always-on domain.
These timers are:
- WKUP: A 64-bit timer that functions as a wakeup timer.
- WDOG: A 32-bit timer that functions as a watchdog timer.

The module conforms to the [Comportable guideline for peripheral functionality](../../../doc/contributing/hw/comportability/README.md).
The AON timer can be programmed and interrogated over a TileLink register interface, which is controlled by RACL.
As well as register values visible over that interface, the module has the following features:
- When a timer expires, the module asserts an associated output in the AON domain.
- Each timer has a threshold, above which it will assert an output in the SYS domain to signal a level interrupt.
- If configured to do so, the watchdog timer pauses on assertion of the (asynchronous) the `sleep_mode_i` port.
- Both timers pause if the `lc_escalate_en_i` port (an `lc_tx_t`) is `On`.
  This ensures that neither timer interferes with system escalation behavior.

## Wakeup timer

The wakeup timer (WKUP) is a 64-bit timer.
Its current value is visible through [`WKUP_COUNT_HI`](doc/registers.md#wkup_count_hi) and [`WKUP_COUNT_LO`](doc/registers.md#wkup_count_lo).
Once the timer is enabled, it increments on every tick of the AON clock, divided by a pre-scaler.
The number of cycles per tick is one more than the 12-bit [`WKUP_CTRL.prescaler`](doc/registers.md#wkup_ctrl) field.

The threshold for this timer is split across [`WKUP_THOLD_HI`](doc/registers.md#wkup_thold_hi) and [`WKUP_THOLD_LO`](doc/registers.md#wkup_thold_lo).
Each time the pre-scaler completes when the count is at or above the threshold, two outputs become high:
- `wkup_req_o` (in the AON domain).
  This should be connected to the power manager.
- `intr_wkup_timer_expired_o` (in the SYS domain).
  This should be connected to the PLIC to pass an interrupt to the processor.

The wakeup signal (`wkup_req_o`) stays high until software explicitly acknowledges it by software writing 0 to [`WKUP_CAUSE`](doc/registers.md#wkup_cause).
Note that this signal is also asserted by a watchdog bark event.
To clear the level interrupt (`intr_wkup_timer_expired_o`), write 1 to the field [`INTR_STATE.wkup_timer_expired`](doc/registers.md#intr_state).
Note that the counter needs clearing or each of these signals will be re-asserted at the next completion of the pre-scaler.

The wakeup timer can be used like a real-time clock for long periods in a low-power mode (though it does not give any guarantees of time accuracy).

## Watchdog timer

The watchdog timer (WDOG) is a 32-bit timer.
Its current value is visible through [`WDOG_COUNT`](doc/registers.md#wdog_count).
Once the timer is enabled, it increments on every tick of the AON clock.

The timer has two separate thresholds ("bark" and "bite").
If the timer is enabled, there is a "bark" on every AON clock tick when the count is at least [`WDOG_BARK_THOLD`](doc/registers.md#wdog_bark_thold).
If the timer is enabled, there is also a "bite" on every AON clock tick when the count is at least [`WDOG_BITE_THOLD`](doc/registers.md#wdog_bite_thold).
To prevent the count reaching the bark or bite thresholds, software is expected to periodically reset the count when operating normally.
This is referred to as "petting the watchdog", and is achieved by resetting the count to zero.

If [`WDOG_CTRL.pause_in_sleep`](doc/registers.md#wdog_ctrl) has been set, the timer pauses when `sleep_mode_i` is asserted.
This allows configurations where the watchdog timer can remain programmed and locked while the device is put to sleep for relatively long periods, controlled by the wakeup timer.
Without this feature, the watchdog timer might wake up the core prematurely by triggering a watchdog bark.

Writes to watchdog configuration can be disabled by [`WDOG_REGWEN`](doc/registers.md#wdog_regwen).
This allows the option of preventing firmware from accidentally or maliciously disabling the watchdog.

### Watchdog bark

When there is a "bark" event, two outputs become high:
- `wkup_req_o` (in the AON domain)
  This should be connected to the power manager.
- `intr_wdog_timer_bark_o` (in the SYS domain)
  This should be connected to the PLIC to pass an interrupt to the processor.

The level wakeup signal (`wkup_req_o`) stays high until software explicitly acknowledges it by software writing 0 to [`WKUP_CAUSE`](doc/registers.md#wkup_cause).
Note that this signal is also asserted by the wakeup timer.
To clear the level interrupt (`intr_wdog_timer_bark_o`) write 1 to the field [`INTR_STATE.wdog_timer_bark`](doc/registers.md#intr_state).

For tooling convenience, the `intr_wdog_timer_bark_o` port is duplicated in `nmi_wdog_timer_bark_o`.
If desired, this can be connected to an NMI on the processor.

### Watchdog bite

When there is a "bite" event, one output becomes high:
- `aon_timer_rst_req_o` (in the AON domain)

This signal is expected to be connected to the power manager, which will trigger a system reset.
