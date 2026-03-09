# RISC-V Debug System Wrapper Technical Specification
<!-- BEGIN AUTOGEN from util/mdbook_regression_links.py -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`rv_dm_use_jtag_interface`](https://nightly.reports.lowrisc.org/opentitan_weekly_earlgrey/2026_03_08/index.html) | 1.2.1 | D2S, V1 | <img src="https://img.shields.io/badge/Tests_Running-483-blue"> <img src="https://img.shields.io/badge/Tests_Passing-83.44%25-green"> <img src="https://img.shields.io/badge/Functional_Coverage-51.71%25-orange"> <img src="https://img.shields.io/badge/Code_Coverage-88.48%25-green"> |

This IP has been taped out in Earl Grey 1.0.0. The corresponding documentation and regression results can be found [here](https://opentitan.org/earlgrey_1.0.0/book/hw/ip/rv_dm/index.html).
<!-- END AUTOGEN -->

# Overview

This document specifies the RISC-V Debug System wrapper functionality.

## Features

The debug system follows the execution-based debug approach described in the [RISC-V Debug Specification 0.13.2](https://github.com/riscv/riscv-debug-spec/raw/4e0bb0fc2d843473db2356623792c6b7603b94d4/riscv-debug-release.pdf) and provides the following features.

- JTAG Test Access Port (TAP)
- Run-control debug features (in cooperation with the CPU core), including breakpoints, single-stepping through code, and reading core registers
- System Bus Access (SBA): Access to arbitrary bus-attached peripherals through JTAG
- Compatible with RISC-V Debug Specification 0.13-compliant debug software, including OpenOCD and GDB
- TileLink Uncached Light (TL-UL) bus interfaces
- Late debug enable mechanism in DEV life cycle state

## Description

This module provides a RISC-V Debug Specification-compliant debug system with TileLink Uncached Light bus interfaces.
The main functionality is provided by the [PULP RISC-V Debug System](https://github.com/pulp-platform/riscv-dbg), which is instantiated by this module.
All bus interfaces are converted into TL-UL.

See the [PULP RISC-V Debug System Documentation](https://github.com/lowRISC/opentitan/blob/master/hw/vendor/pulp_riscv_dbg/doc/debug-system.md) for a full list of features and further design documentation.
This document only describes the additional logic provided on top of the PULP RISC-V Debug System.

## Compatibility

The debug system is compliant with the [RISC-V Debug Specification 0.13.2](https://github.com/riscv/riscv-debug-spec/raw/4e0bb0fc2d843473db2356623792c6b7603b94d4/riscv-debug-release.pdf).
