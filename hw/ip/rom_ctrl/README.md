# ROM Controller Technical Specification

[`rom_ctrl`](https://reports.opentitan.org/hw/ip/rom_ctrl/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/rom_ctrl/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/rom_ctrl/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/rom_ctrl/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/rom_ctrl/code.svg)

# Overview

This document describes the ROM controller (`rom_ctrl`).
This module attaches as a peripheral to the system bus, and thus follows the [Comportability Specification](../../../doc/contributing/hw/comportability/README.md).

The ROM controller interfaces between the system bus and the ROM.
This ROM has scrambled contents (scrambled with a fixed key, derived from a global constant).
The controller is responsible for descrambling these contents on memory fetches.

Unlike the [SRAM controller](../sram_ctrl/README.md), which performs the equivalent task for SRAM, the ROM controller also contains a *ROM checker* block.
This ROM checker is used to compute a cryptographic hash of the ROM contents just after boot, detecting any malicious changes that have been made to the ROM when the system was at rest.

## Features

- Logic for memory and address descrambling
- Post-boot ROM integrity check
- Alert trigger and status CSRs for ROM integrity errors or FSM glitches.
