# Ibex RISC-V Core Wrapper Technical Specification

<!-- BEGIN CMDGEN util/mdbook_regression_links.py --hjson hw/top_darjeeling/ip_autogen/rv_core_ibex/data/rv_core_ibex.hjson --top darjeeling -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`rv_core_ibex`](https://ibex.reports.lowrisc.org/opentitan/latest/report.html) | 3.0.0 | D1, V0 | ![](https://dashboard.reports.lowrisc.org/badges/dv/ibex/opentitan/test.svg) ![](https://dashboard.reports.lowrisc.org/badges/dv/ibex/opentitan/passing.svg) ![](https://dashboard.reports.lowrisc.org/badges/dv/ibex/opentitan/functional.svg) ![](https://dashboard.reports.lowrisc.org/badges/dv/ibex/opentitan/code.svg) |

<!-- END CMDGEN -->

> rv_core_ibex is currently under active development as CHERIoT support is added, the bitmanip extension is upgraded to the ratified version, and the Zc* compressed ISA extensions are included.
> This is indicated by the development stages (see [`rv_core_ibex.hjson`](https://github.com/lowRISC/opentitan/blob/master/hw/top_darjeeling/ip_autogen/rv_core_ibex/data/rv_core_ibex.hjson) and [here](https://opentitan.org/book/doc/project_governance/development_stages.html)).
> As of this the documentation can slightly differ from the current RTL implementation.

# Overview

This document specifies Ibex CPU core wrapper functionality.

## Features

* Instantiation of a [Ibex RV32 CPU Core](https://github.com/lowRISC/ibex).
* TileLink Uncached Light (TL-UL) host interfaces for the instruction and data ports.
* Simple address translation.
* NMI support for security alert events for watchdog bark.
* General error status collection and alert generation.
* Crash dump collection for software debug.

## Description

The Ibex RISC-V Core Wrapper instantiates an [Ibex RV32 CPU Core](https://github.com/lowRISC/ibex), and wraps its data and instruction memory interfaces to TileLink Uncached Light (TL-UL).
All configuration parameters of Ibex are passed through, except for the CHERIoT ports and parameters (signals and parameters starting with `trvk_`, plus `BaseIsa`), which are not yet exposed.
The pipelining of the bus adapters is configurable.

## Compatibility

Ibex is a compliant RV32 RISC-V CPU core, as [documented in the Ibex documentation](https://ibex-core.readthedocs.io/en/latest/01_overview/compliance.html).

The TL-UL bus interfaces exposed by this wrapper block are compliant to the [TileLink Uncached Lite Specification version 1.7.1](https://sifive.cdn.prismic.io/sifive%2F57f93ecf-2c42-46f7-9818-bcdd7d39400a_tilelink-spec-1.7.1.pdf).
