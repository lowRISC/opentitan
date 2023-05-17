# RISC-V Debug System Wrapper Technical Specification

# Overview

{{#block-dashboard rv_dm}}

This document specifies the RISC-V Debug System wrapper functionality.

## Features

The debug system follows the execution-based debug approach described in the [RISC-V Debug Specification 0.13.2](https://github.com/riscv/riscv-debug-spec/raw/4e0bb0fc2d843473db2356623792c6b7603b94d4/riscv-debug-release.pdf) and provides the following features.

- JTAG Test Access Port (TAP)
- Run-control debug features (in cooperation with the CPU core), including breakpoints, single-stepping through code, and reading core registers
- System Bus Access (SBA): Access to arbitrary bus-attached peripherals through JTAG
- Compatible with RISC-V Debug Specification 0.13-compliant debug software, including OpenOCD and GDB
- TileLink Uncached Light (TL-UL) bus interfaces

## Description

This module provides a RISC-V Debug Specification-compliant debug system with TileLink Uncached Light bus interfaces.
The main functionality is provided by the [PULP RISC-V Debug System](https://github.com/pulp-platform/riscv-dbg), which is instantiated by this module.
All bus interfaces are converted into TL-UL.

See the [PULP RISC-V Debug System Documentation](https://github.com/lowRISC/opentitan/blob/master/hw/vendor/pulp_riscv_dbg/doc/debug-system.md) for a full list of features and further design documentation.
This document only describes the additional logic provided on top of the PULP RISC-V Debug System.

## Compatibility

The debug system is compliant with the [RISC-V Debug Specification 0.13.2](https://github.com/riscv/riscv-debug-spec/raw/4e0bb0fc2d843473db2356623792c6b7603b94d4/riscv-debug-release.pdf).
