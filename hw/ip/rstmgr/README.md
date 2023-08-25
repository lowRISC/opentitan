# Reset Manager HWIP Technical Specification

[`rstmgr`](https://reports.opentitan.org/hw/ip/rstmgr/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/rstmgr/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/rstmgr/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/rstmgr/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/rstmgr/code.svg)

[`rstmgr_cnsty_chk`](https://reports.opentitan.org/hw/ip/rstmgr/dv/rstmgr_cnsty_chk/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/rstmgr_cnsty_chk/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/rstmgr_cnsty_chk/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/rstmgr_cnsty_chk/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/rstmgr_cnsty_chk/code.svg)

# Overview

This document describes the functionality of the reset controller and its interaction with the rest of the OpenTitan system.

## Features

*   Stretch incoming POR.
*   Cascaded system resets.
*   Peripheral system reset requests.
*   RISC-V non-debug-module reset support.
*   Limited and selective software controlled module reset.
*   Always-on reset information register.
*   Always-on alert crash dump register.
*   Always-on CPU crash dump register.
*   Reset consistency checks.
