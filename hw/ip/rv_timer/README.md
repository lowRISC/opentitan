# Timer HWIP Technical Specification
<!-- BEGIN CMDGEN util/mdbook_regression_links.py --hjson hw/ip/rv_timer/data/rv_timer.hjson --top earlgrey -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`rv_timer`](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/dashboard.html) | 1.0.0 | D3, V3 | ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/rv_timer/test.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/rv_timer/passing.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/rv_timer/functional.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/rv_timer/code.svg) |

This IP has been taped out in Earl Grey 1.0.0. The corresponding documentation and regression results can be found [here](https://opentitan.org/earlgrey_1.0.0/book/hw/ip/rv_timer/index.html).

<!-- END CMDGEN -->

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

Note: Although the number of timers is indeed configurable, the implementation currently only connects up one timer for one hart.
## Description

The timer module provides a configurable number of 64-bit counters where each
counter increments by a step value whenever the prescaler times out. Each timer
generates an interrupt if the counter reaches (or is above) a programmed
value. The timer is intended to be used by the processors to check the current
time relative to the reset or the system power-on.

In this version, the timer doesn't consider low-power modes and
assumes the clock is neither turned off nor changed during runtime.

## Compatibility

The timer IP provides memory-mapped registers equivalent to `mtime` and `mtimecmp` which can
be used as the machine-mode timer registers defined in the RISC-V privileged
spec. Additional features such as prescaler, step, and a configurable number of
timers and harts have been added.
