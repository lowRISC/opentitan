# Timer HWIP Technical Specification

[`rv_timer`](https://reports.opentitan.org/hw/ip/rv_timer/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/rv_timer/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/rv_timer/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/rv_timer/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/rv_timer/code.svg)

# Overview

This document specifies RISC-V Timer hardware IP functionality. This module
conforms to the
[Comportable guideline for peripheral functionality.](../../../doc/contributing/hw/comportability/README.md)
See that document for integration overview within the broader top level
system.


## Features

- 64-bit timer with 12-bit prescaler and 8-bit step register
- Compliant with RISC-V privileged specification v1.11
- Configurable number of timers per hart and number of harts

## Description

The timer module provides a configurable number of 64-bit counters where each
counter increments by a step value whenever the prescaler times out. Each timer
generates an interrupt if the counter reaches (or is above) a programmed
value. The timer is intended to be used by the processors to check the current
time relative to the reset or the system power-on.

In this version, the timer doesn't consider low-power modes and
assumes the clock is neither turned off nor changed during runtime.

## Compatibility

The timer IP provides memory-mapped registers `mtime` and `mtimecmp` which can
be used as the machine-mode timer registers defined in the RISC-V privileged
spec. Additional features such as prescaler, step, and a configurable number of
timers and harts have been added.
