# AON Timer Technical Specification

[`aon_timer`](https://reports.opentitan.org/hw/ip/aon_timer/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/aon_timer/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/aon_timer/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/aon_timer/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/aon_timer/code.svg)

[`Opentitan Glossary`](../../../doc/glossary.md).


# Overview

This document specifies the Always-On ("AON") Timer IP functionality.
This module conforms to the [Comportable guideline for peripheral functionality.](../../../doc/contributing/hw/comportability/README.md)
See that document for an overview of how it is integrated into the top level system.

## Features

- Two upcounting timers: one 64-bit timer that functions as a wakeup timer, and a 32-bit one that functions as a watchdog timer
- The watchdog timer has two thresholds: bark (generates an interrupt) and bite (resets core)
- There is 12 bit pre-scaler for the wakeup timer to enable very long timeouts
- The pause in sleep port for WDOG timer permits pausing the count when the system is in sleep mode when configured accordingly
- Count is halted for both timers if `lc_escalate_en_i` is set

Note: the pause during escalation feature ensures either timer do not interfere with system escalation behavior.


## Description

This IP provides two timers: a WKUP and WDOG counter which generate interrupts if their respective count register is greater than or equals to the threshold once enabled.

### AON Wakeup timer

The always-on wakeup timer operation is straightforward.
When the counter is enabled and its value is as large as the wakeup threshold, `aon_timer` reports a wakeup event.
This is reported through a level wakeup signal (`wkup_req_o`, in the AON domain) that gets sent to the power manager.
It is also exposed to the processor through a level IRQ (`intr_wkup_timer_expired_o`, in the SYS domain).
In addition, the Wkup timer has a prescaler which is configured via writing to register `wkup_ctrl.prescaler`.
If the prescaler is set to a non-zero value, the count register will increase every `N + 1` clock cycles, where `N` is the pre-scaler value).
The level wakeup signal (`wkup_req_o`) stays high until there's a system reset or it's explicitly acknowledged by software by writing a 0 to the [`WKUP_CAUSE`](doc/registers.md#wkup_cause) register.
To clear the level interrupt (`intr_wkup_timer_expired_o`) write 1 to the field [`INTR_STATE.wkup_timer_expired`](doc/registers.md#intr_state).
Note that if [`WKUP_COUNT`](doc/registers.md#wkup_count) is not zeroed and remains at or above the wake threshold and the wakeup timer isn't disabled, the wakeup and interrupt will trigger again at the next clock tick.
The wakeup timer can be used like a real-time clock for long periods in a low-power mode (though it does not give any guarantees of time-accuracy). **TODO: specify accuracy**

### AON Watchdog timer

The always-on watchdog timer behaves similarly to the wakeup timer.
It has an independent count starting at `wdog_count` and increasing on each tick of AON clock.
The counter can generate interrupts based on the bark and bite thresholds (`wdog_bark_thold` and `wdog_bite_thold`).

To prevent the count reaching the bark or bite thresholds, software is expected to periodically reset the count when operating normally.
This is referred to as petting the watchdog, and is achieved by resetting the count to zero.

Since this timer functions as a watchdog, it has two additional features not present in the always-on wakeup timer: Watchdog configuration lock and pause in sleep.

Once the watchdog timer configuration is locked, firmware cannot modify the timer configuration registers  until the next system reset.
This allows the option of preventing firmware from accidentally or maliciously disabling the watchdog.
The Watchdog timer configuration is locked by writting 0 to register [`WDOG_REGWEN`](doc/registers.md#wdog_regwen).

The "pause in sleep" option controls whether the count increases in low-power modes if enabled.
This allows configurations where the watchdog timer can remain programmed and locked while the device is put to sleep for relatively long periods, controlled by the wakeup timer.
Without this feature, the watchdog timer might wake up the core prematurely by triggering a watchdog bark.
In order to enable this functionality, the field [`WDOG_CTRL.pause_in_sleep`](doc/registers.md#wdog_ctrl) must be set to 1.
That way, the timer will halt the count whenever `sleep_mode_i` is set after it's been synchronised.

#### AON Watchdog bark

If the count is greater than or equals to the threshold and it's enabled then a level wakeup signal (`wkup_req_o` in AON domain) is sent to the power manager.
Note `wkup_req_o` can get set by either timer once the threshold is surpassed.
In addition, a level IRQ (`intr_wdog_timer_bark_o` in SYS domain) is also generated for the processor.
If the system is in a low power state, `wkup_req_o` signal asks the power manager to wake the system so that the IRQ (`intr_wdog_timer_bark_o`) can be serviced.
If the system is not in a low power mode, the IRQ is immediately serviced.
The level wakup signal (`wkup_req_o`) stays high until there's a system reset or it's explicitly acknowledged by software by writing a 0 to the [`WKUP_CAUSE`](doc/registers.md#wkup_cause) register.
To clear the level interrupt (`intr_wdog_timer_bark_o`) write 1 to the field [`INTR_STATE.wdog_timer_bark`](doc/registers.md#intr_state).
The condition of the count reaching the bark threshold is known as the watchdog bark.

An extra interrupt output is available to connect the watchdog bark output to an NMI pin (`nmi_wdog_timer_bark_o`) if required.

#### AON Watchdog bite

The condition of the count reaching the bite threshold is known as the watchdog bite.
In the same manner as the watchdog bark, if the count is greater than or equals to the [`WDOG_BARK_THOLD.threshold`](doc/registers.md#wdog_bark_thold) and the timer it's enabled, then a reset request (`aon_timer_rst_req_o` in AON domain) is sent to the power manager which will trigger a system reset.
This reset request is independent of the IRQ sent as part of the watchdog bark.
The system reset from the power manager also resets the always-on timer, so software is not required to directly acknowledge anything after a watchdog reset.
