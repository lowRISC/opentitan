# AON Timer Technical Specification

[`aon_timer`](https://reports.opentitan.org/hw/ip/aon_timer/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/aon_timer/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/aon_timer/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/aon_timer/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/aon_timer/code.svg)

# Overview

This document specifies the Always-On ("AON") Timer IP functionality.
This module conforms to the [Comportable guideline for peripheral functionality.](../../../doc/contributing/hw/comportability/README.md)
See that document for an overview of how it is integrated into the top level system.

## Features

- Two 32-bit upcounting timers: one timer functions as a wakeup timer, one as a watchdog timer
- The watchdog timer has two thresholds: bark (generates an interrupt) and bite (resets core)
- There is 12 bit pre-scaler for the wakeup timer to enable very long timeouts

## Description

### AON Wakeup timer

The always-on wakeup timer operation is straightforward.
A count starts at 0 and slowly ticks upwards (one tick every `N + 1` clock cycles, where `N` is the pre-scaler value).
When it reaches / exceeds the wake threshold, a level wakeup signal is sent to the power manager and a level IRQ is sent to the processor.
This wakeup signal stays high until it is explicitly acknowledged by software.
To clear the wakeup write 0 to the [`WKUP_CAUSE`](data/aon_timer.hjson#wkup_cause) register.
To clear the interrupt write 1 to [`INTR_STATE.wkup_timer_expired`](data/aon_timer.hjson#intr_state).
Note that if [`WKUP_COUNT`](data/aon_timer.hjson#wkup_count) is not zeroed and remains at or above the wake threshold and the wakeup timer isn't disabled, the wakeup and interrupt will trigger again at the next clock tick.
The wakeup timer can be used like a real-time clock for long periods in a low-power mode (though it does not give any guarantees of time-accuracy). **TODO: specify accuracy**

### AON Watchdog timer

The always-on watchdog timer behaves similarly to the wakeup timer.
It has an independent count starting at 0 which slowly ticks upwards.
When the first threshold is met or exceeded, a level wakeup signal (if enabled) is sent to the power manager.
Simultaneously, a level IRQ signal is also generated to the processor.

If the system is in a low power state, the wakeup signal asks the power manager to wake the system so that the IRQ can be serviced.
If the system is not in a low power mode, the IRQ is immediately serviced.
Both the wakeup and the IRQ signals remain asserted until system reset or explicit acknowledgement by software.
This first threshold is known as the watchdog bark.

An extra interrupt output is available to connect the watchdog bark output to a non-maskable interrupt pin if required.

When the second threshold is met (this is known as the watchdog bite), a reset request is sent to the power manager which will trigger a system reset.
This is independent of the IRQ sent as part of the watchdog bark.
The system reset also resets the always-on timer, so software is not required to directly acknowledge anything after a watchdog reset.

To prevent the watchdog bark or bite, software is expected to periodically reset the count when operating normally.
This is referred to as petting the watchdog, and is achieved by resetting the count to zero.

Since this timer functions as a watchdog, it has three additional functions not present in the always-on wakeup timer:
* Watchdog configuration lock
* Watchdog pause in sleep
* Watchdog pause during system escalation

Unlike the wakeup timer, the watchdog timer configuration can be locked by firmware until the next system reset.
This allows the option of preventing firmware from accidentally or maliciously disabling the watchdog.

The "pause in sleep" option controls whether the watchdog timer continues to count in low-power modes.
This allows configurations where the watchdog timer can remain programmed and locked while the device is put to sleep for relatively long periods, controlled by the wakeup timer.
Without this feature, the watchdog timer might wake up the core prematurely by triggering a watchdog bark.

The "pause during escalation" feature ensures that watchdog bites and barks do not interfere with system escalation behavior.
If during escalation software configures the system to hang instead of reset, the watchdog bite cannot supersede that decision.
