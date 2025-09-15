# BKDR_LOADER Technical Specification
<!-- BEGIN CMDGEN util/mdbook_regression_links.py --hjson hw/ip/bkdr_loader/data/bkdr_loader.hjson --top earlgrey -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`bkdr_loader`](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/dashboard.html) | 0.1.0 | D1, V0 | ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/bkdr_loader/test.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/bkdr_loader/passing.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/bkdr_loader/functional.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/bkdr_loader/code.svg) |

<!-- END CMDGEN -->

# Overview

This document specifies the FPGA-only memory Backdoor Loader which is used to preload non-volatile
and volatile memories on FPGA targets.


## Features

- No impact on ASIC implementation: loader RTL only in FPGA-specific files
- Exposes FPGA-only registers such as the `USR_TIMESTAMP`
- Up to 64 memory r/w targets supported
- Automatic discovery of available targets by presenting a 32-bit target ID as well as width and depth
- Access to raw BRAM data allowing to set both data and ECC arbitrarily for each target

## Description

The BKDR_LOADER intercepts the reset and JTAG signals between the FPGA pad array and the top-level
OpenTitan instance. On reset, the IP samples the tap strap pins and becomes active if both strap
signals are high (DFT mode on the ASIC).

When active, the module keeps the reset to both the AST and OpenTitan asserted to prevent any access
to non-initialized memory regions. It presents an internal RISC-V DTM over which the loader's internal
[registers](doc/registers.md) can be accessed. The BKDR_LOADER presents both the number of targets and key target
information through its register space.

After completing preloading and data validation, the loader is deactivated until the next
button reset via the control register. In this case, the JTAG signals are forwarded to OpenTitan
and the reset to the AST and OpenTitan is de-asserted.
