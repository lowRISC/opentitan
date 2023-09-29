# Power Manager HWIP Technical Specification
[`pwrmgr`](https://reports.opentitan.org/hw/top_${top_name}/ip_autogen/pwrmgr/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/pwrmgr/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/pwrmgr/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/pwrmgr/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/pwrmgr/code.svg)

# Overview

This document specifies the functionality of the OpenTitan power manager.

${"##"} Features

- Cold boot, low power entry / exit and reset support.
- 2 different low power modes.
- Software initiated low power entry and hardware requested low power exit.
- Peripheral reset requests
- Low power abort and low power fall-through support.
- ROM integrity check at power-up.
- Local checks for escalator and power stability.

${"##"} Description

The power manager sequences power, clocks, and reset resources of the design through cold boot, low power entry/exit and reset scenarios.

Cold boot, also known as POR (power on reset) is the first reset state of the design.
The power manager sequences the design from a freshly reset state to an active state where software can be initialized.

- Low power entry is the process in which the device enters one of two low power modes (sleep or deep sleep).
- Low power exit is the process in which the device exits low power mode and returns to active state.
- Low power entry is always initiated by software, while low power exit is always initiated by a previously setup hardware event such as pins or internal timers.
- The power manager processes the software and hardware requests to perform the appropriate actions.

Reset scenarios refer to non-POR events that cause the device to reboot.
There are various stimuli that can cause such a reset, ranging from external user input to watchdog timeout.
The power manager processes the reset request and brings the device to an appropriate state.
