# Reset Manager HWIP Technical Specification
<!-- BEGIN CMDGEN util/mdbook_regression_links.py --hjson hw/top_earlgrey/ip_autogen/rstmgr/data/rstmgr.hjson --top earlgrey -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`rstmgr`](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/dashboard.html) | 1.0.0 | D3, V2S | ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/rstmgr/test.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/rstmgr/passing.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/rstmgr/functional.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/rstmgr/code.svg) |

<!-- END CMDGEN -->

**NOTE**: This document describes the planned split of the reset manager into an always-on (AON) part and a power-gated (Main) part, including the software re-initialisation requirement.
The split is not implemented in the RTL yet; until it is, the reset manager resides entirely in the AON power domain and its state is retained during deep sleep.

# Overview

This document describes the functionality of the reset controller and its interaction with the rest of the OpenTitan system.

## Features

*   Stretch incoming POR.
*   Cascaded system resets.
*   Peripheral system reset requests.
*   RISC-V non-debug-module reset support.
*   Limited and selective software controlled module reset.
*   Reset information register.
*   Alert crash dump register.
*   CPU crash dump register.
*   Reset consistency checks.
*   Split into an always-on (AON) part and a power-gated (Main) part, to reduce power consumption during deep sleep:
    *   The AON part contains power-on reset generation, the life cycle and system reset request logic, and the retention of reset consistency errors.
    *   The Main part contains all leaf reset generation, the software-controlled peripheral resets, the crash dump logic and the CSRs.
    *   The CSRs lose their values during deep sleep. Software must re-initialise the configuration CSRs after returning from deep sleep.
    *   Crash dump information does not survive deep sleep. Software must read and act on the content before entering deep sleep.
