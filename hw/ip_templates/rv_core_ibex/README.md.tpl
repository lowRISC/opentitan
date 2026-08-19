# Ibex RISC-V Core Wrapper Technical Specification

[`rv_core_ibex`](https://ibex.reports.lowrisc.org/opentitan/latest/report.html):
![](https://dashboard.reports.lowrisc.org/badges/dv/ibex/opentitan/test.svg)
![](https://dashboard.reports.lowrisc.org/badges/dv/ibex/opentitan/passing.svg)
![](https://dashboard.reports.lowrisc.org/badges/dv/ibex/opentitan/functional.svg)
![](https://dashboard.reports.lowrisc.org/badges/dv/ibex/opentitan/code.svg)

# Overview

This document specifies Ibex CPU core wrapper functionality.

<%text>## Features</%text>

* Instantiation of a [Ibex RV32 CPU Core](https://github.com/lowRISC/ibex).
* TileLink Uncached Light (TL-UL) host interfaces for the instruction and data ports.
* Simple address translation.
* NMI support for security alert events for watchdog bark.
* General error status collection and alert generation.
* Crash dump collection for software debug.
% if cheriot_available:
* Write-once switch between the ePMP and CHERIoT execution modes.
% endif

<%text>## Description</%text>

The Ibex RISC-V Core Wrapper instantiates an [Ibex RV32 CPU Core](https://github.com/lowRISC/ibex), and wraps its data and instruction memory interfaces to TileLink Uncached Light (TL-UL).
% if cheriot_available:
All configuration parameters of Ibex are passed through, except for the TRVK ports (signals starting with `trvk_`), which are not yet exposed.
`BaseIsa` is exposed, but has to stay CHERIoT-capable: the wrapper holds the [execution mode switch](doc/theory_of_operation.md#execution-mode-switch) that selects between ePMP and CHERIoT mode at runtime.
% else:
All configuration parameters of Ibex are passed through, except for the CHERIoT ports and parameters (signals and parameters starting with `trvk_`, plus `BaseIsa`), which are not yet exposed.
% endif
The pipelining of the bus adapters is configurable.

<%text>## Compatibility</%text>

Ibex is a compliant RV32 RISC-V CPU core, as [documented in the Ibex documentation](https://ibex-core.readthedocs.io/en/latest/01_overview/compliance.html).

The TL-UL bus interfaces exposed by this wrapper block are compliant to the [TileLink Uncached Lite Specification version 1.7.1](https://sifive.cdn.prismic.io/sifive%2F57f93ecf-2c42-46f7-9818-bcdd7d39400a_tilelink-spec-1.7.1.pdf).
