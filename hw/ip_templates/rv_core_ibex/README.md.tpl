# Ibex RISC-V Core Wrapper Technical Specification

<!-- BEGIN CMDGEN util/mdbook_regression_links.py --hjson hw/top_${topname}/ip_autogen/rv_core_ibex/data/rv_core_ibex.hjson --top ${topname} -->
<!-- END CMDGEN -->

> rv_core_ibex is currently under active development as CHERIoT support is added, the bitmanip extension is upgraded to the ratified version, and the Zc* compressed ISA extensions are included.
> This is indicated by the development stages (see [`rv_core_ibex.hjson`](https://github.com/lowRISC/opentitan/blob/master/hw/top_${topname}/ip_autogen/rv_core_ibex/data/rv_core_ibex.hjson) and [here](https://opentitan.org/book/doc/project_governance/development_stages.html)).
> As of this the documentation can slightly differ from the current RTL implementation.
% if topname == 'earlgrey':
> The documentation for the rv_core_ibex version with design stage D2S and verification stage V2S (v2.1.0) can be found under the Earl Grey v1.0.0 documentation [here](https://opentitan.org/earlgrey_1.0.0/book/hw/ip/rv_core_ibex/index.html).
% endif

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
`BaseIsa` is not exposed: it is fixed to the CHERIoT-capable base ISA, and the wrapper holds the [execution mode switch](doc/theory_of_operation.md#execution-mode-switch) that selects between ePMP and CHERIoT mode at runtime.
% else:
All configuration parameters of Ibex are passed through, except for the CHERIoT ports and parameters (signals and parameters starting with `trvk_`, plus `BaseIsa`), which are not yet exposed.
% endif
The pipelining of the bus adapters is configurable.

<%text>## Compatibility</%text>

Ibex is a compliant RV32 RISC-V CPU core, as [documented in the Ibex documentation](https://ibex-core.readthedocs.io/en/latest/01_overview/compliance.html).

The TL-UL bus interfaces exposed by this wrapper block are compliant to the [TileLink Uncached Lite Specification version 1.7.1](https://sifive.cdn.prismic.io/sifive%2F57f93ecf-2c42-46f7-9818-bcdd7d39400a_tilelink-spec-1.7.1.pdf).
