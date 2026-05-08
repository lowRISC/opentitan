# Reset Manager HWIP Technical Specification
<!-- BEGIN CMDGEN util/mdbook_regression_links.py --hjson hw/top_darjeeling/ip_autogen/rstmgr/data/rstmgr.hjson --top darjeeling -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`rstmgr`](https://dashboard.reports.lowrisc.org/opentitan/darjeeling/dashboard.html) | 1.0.0 | D3, V2S | ![](https://dashboard.reports.lowrisc.org/opentitan/darjeeling/badge/rstmgr/test.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/darjeeling/badge/rstmgr/passing.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/darjeeling/badge/rstmgr/functional.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/darjeeling/badge/rstmgr/code.svg) |

<!-- END CMDGEN -->

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
