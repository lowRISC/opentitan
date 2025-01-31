# ROM Controller Technical Specification

[`rom_ctrl`](https://reports.opentitan.org/hw/ip/rom_ctrl/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/rom_ctrl/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/rom_ctrl/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/rom_ctrl/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/rom_ctrl/code.svg)

# Overview

The ROM controller (`rom_ctrl`) is the connection between the chip and its ROM.
It has three main tasks:
- Pass read requests to the ROM and respond with the memory contents.
- Generate a checksum of the ROM contents and feed its value to keymgr to be included in the device identity.
- Inform pwrmgr once the checksum has been computed and looks reasonable, to allow the rest of the chip startup.

In order to fulfil the first task, the ROM controller attaches as a peripheral to the system bus.
Because it does so, it follows the [Comportability Specification](../../../doc/contributing/hw/comportability/README.md).
The contents of the ROM are also scrambled (with a fixed key, derived from a global constant).
The ROM controller is responsible for descrambling these contents as it replies to memory reads.

The contents of the ROM are read immediately after coming out of reset.
The words read are passed to KMAC (which computes a SHA3 checksum from them).
Once that is done, the resulting checksum is passed to keymgr over a dedicated connection.
The checksum can also be read by software, using the `DIGEST_*` registers.

There is also a dedicated connection to the power manager (to allow the third item).
A basic check that the contents look reasonable is performed by storing the expected value of the hash in the top 8 words of the ROM.
The ROM controller checks that this matches the hash that was computed, and passes this information to the power manager (which can stop the startup if the SHA doesn't match).

## Features

- Logic for memory and address descrambling
- Post-boot ROM integrity check
- Alert trigger and status CSRs for ROM integrity errors or FSM glitches.
