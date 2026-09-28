# Ibex RISC-V Core Wrapper Technical Specification

<!-- BEGIN CMDGEN util/mdbook_regression_links.py --hjson hw/top_earlgrey/ip_autogen/rv_core_ibex/data/rv_core_ibex.hjson --top earlgrey -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`rv_core_ibex`](https://ibex.reports.lowrisc.org/opentitan/latest/report.html) | 3.0.0 | D1, V0 | ![](https://dashboard.reports.lowrisc.org/badges/dv/ibex/opentitan/test.svg) ![](https://dashboard.reports.lowrisc.org/badges/dv/ibex/opentitan/passing.svg) ![](https://dashboard.reports.lowrisc.org/badges/dv/ibex/opentitan/functional.svg) ![](https://dashboard.reports.lowrisc.org/badges/dv/ibex/opentitan/code.svg) |

This IP has been taped out in Earl Grey 1.0.0. The corresponding documentation and regression results can be found [here](https://opentitan.org/earlgrey_1.0.0/book/hw/ip/rv_core_ibex/index.html).

<!-- END CMDGEN -->

> rv_core_ibex is currently under active development as CHERIoT support is added, the bitmanip extension is upgraded to the ratified version, and the Zc* compressed ISA extensions are included.
> This is indicated by the development stages (see [`rv_core_ibex.hjson`](https://github.com/lowRISC/opentitan/blob/master/hw/top_earlgrey/ip_autogen/rv_core_ibex/data/rv_core_ibex.hjson) and [here](https://opentitan.org/book/doc/project_governance/development_stages.html)).
> As of this the documentation can slightly differ from the current RTL implementation.
> The documentation for the rv_core_ibex version with design stage D2S and verification stage V2S (v2.1.0) can be found under the Earl Grey v1.0.0 documentation [here](https://opentitan.org/earlgrey_1.0.0/book/hw/ip/rv_core_ibex/index.html).

# Overview

This document specifies Ibex CPU core wrapper functionality.

## Features

* Instantiation of a [Ibex RV32 CPU Core](https://github.com/lowRISC/ibex).
* TileLink Uncached Light (TL-UL) host interfaces for the instruction and data ports.
* Simple address translation.
* NMI support for security alert events for watchdog bark.
* General error status collection and alert generation.
* Crash dump collection for software debug.
* Write-once switch between the ePMP and CHERIoT execution modes.

## Description

The Ibex RISC-V Core Wrapper instantiates an [Ibex RV32 CPU Core](https://github.com/lowRISC/ibex), and wraps its data and instruction memory interfaces to TileLink Uncached Light (TL-UL).
All configuration parameters of Ibex are passed through, except for the TRVK ports (signals starting with `trvk_`), which are not yet exposed.
`BaseIsa` is not exposed: it is fixed to the CHERIoT-capable base ISA, and the wrapper holds the [execution mode switch](doc/theory_of_operation.md#execution-mode-switch) that selects between ePMP and CHERIoT mode at runtime.
The pipelining of the bus adapters is configurable.

## Compatibility

Ibex is a compliant RV32 RISC-V CPU core, as [documented in the Ibex documentation](https://ibex-core.readthedocs.io/en/latest/01_overview/compliance.html).

The TL-UL bus interfaces exposed by this wrapper block are compliant to the [TileLink Uncached Lite Specification version 1.7.1](https://sifive.cdn.prismic.io/sifive%2F57f93ecf-2c42-46f7-9818-bcdd7d39400a_tilelink-spec-1.7.1.pdf).
