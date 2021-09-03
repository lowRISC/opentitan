---
title: "Ibex RISC-V Core Wrapper Technical Specification"
---

# Overview

This document specifies Ibex CPU core wrapper functionality.


## Features

* Instantiation of a [Ibex RV32 CPU Core](https://github.com/lowRISC/ibex).
* TileLink Uncached Light (TL-UL) host interfaces for the instruction and data ports.
* Simple address translation.
* NMI support for security alert events for watchdog bark.
* General error status collection and alert generation.

## Description

The Ibex RISC-V Core Wrapper instantiates an [Ibex RV32 CPU Core](https://github.com/lowRISC/ibex), and wraps its data and instruction memory interfaces to TileLink Uncached Light (TL-UL).
All configuration parameters of Ibex are passed through.
The pipelining of the bus adapters is configurable.

## Compatibility

Ibex is a compliant RV32 RISC-V CPU core, as [documented in the Ibex documentation](https://ibex-core.readthedocs.io/en/latest/01_overview/compliance.html).

The TL-UL bus interfaces exposed by this wrapper block are compliant to the [TileLink Uncached Lite Specification version 1.7.1](https://sifive.cdn.prismic.io/sifive%2F57f93ecf-2c42-46f7-9818-bcdd7d39400a_tilelink-spec-1.7.1.pdf).

# Theory of Operations

## Simple Address Translation

The wrapper supports a simple address translation scheme.
The goal of the scheme is to provide hardware support for A/B software copies.

Each copy of the software is stored at a different location.
Depending upon which execution slot is active, a different copy is used.
This creates an issue because each copy of software has different addresses and thus must be linked differently.
Ideally, software should be able to assume one address all the time, and the hardware should remap to the appropriate physical location.

The translation scheme is based on NAPOT (natural alignment to power of two).
Software picks a matching region and also a remap address.
When an incoming transaction matches the selected power-of-2 region, it is redirected to the new address.
If a transaction does not match, then it is directly passed through.

This allows software to place the executable code at a virtual address in the system and re-map that to the appropriate physical block.

There are separate translations controls for instruction and data.
Each control contains two programmable regions (2 for instruction and 2 for data).
If a transaction matches multiple regions, the lowest indexed region has priority.

For details on how to program the related registers, please see {{< regref "IBUS_ADDR_MATCHING_0" >}} and {{< regref "IBUS_REMAP_ADDR_0" >}}.

## Register Table

A number of memory-mapped registers are available to control Ibex-related functionality that's specific to OpenTitan.

{{< incGenFromIpDesc "../data/rv_core_ibex.hjson" "registers" >}}

## Hardware Interfaces

### Signals

{{< incGenFromIpDesc "../data/rv_core_ibex.hjson" "hwcfg" >}}

All ports and parameters of Ibex are exposed through this wrapper module, except for the instruction and data memory interfaces (signals starting with `instr_` and `data_`).
Refer to the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/02_user/integration.html) for a detailed description of these signals and parameters.

The instruction and data memory ports are exposed as TL-UL ports.
The table below lists other signals and the TL-UL ports.

Signal               | Direction        | Type                                   | Description
---------------------|------------------|----------------------------------------|---------------
`rst_cpu_n_o`        | `output`         | `logic`                                | Outgoing indication to reset manager that the process has reset.
`ram_cfg_i`          | `input`          | `prim_ram_1p_pkg::ram_1p_cfg_t`        | Incoming memory configuration that is technology dependent.
`corei_tl_h_o`       | `output`         | `tlul_pkg::tl_h2d_t`                   | Outgoing instruction tlul request
`corei_tl_h_i`       | `input`          | `tlul_pkg::tl_d2h_t`                   | Incoming instruction tlul response.
`cored_tl_h_o`       | `output`         | `tlul_pkg::tl_h2d_t`                   | Outgoing data tlul request
`cored_tl_h_i`       | `input`          | `tlul_pkg::tl_d2h_t`                   | Incoming data tlul response.
`esc_tx_i`           | `input`          | `prim_esc_pkg::esc_tx_t`               | Incoming escalation request / ping.
`esc_rx_o`           | `output`         | `prim_esc_pkg::esc_rx_t`               | Outgoing escalation response.
`nmi_wdog_i`         | `input`          | `logic`                                | Incoming watchdog NMI bark.
`crash_dump_o`       | `output`         | `ibex_pkg::crash_dump_t`               | Outgoing crash dump information to rstmgr.
`cfg_tl_d_i`         | `input`          | `tlul_pkg::tl_h2d_t`                   | Incoming configuration bus request.
`cfg_tl_d_o `        | `output`         | `tlul_pkg::tl_d2h_t`                   | Outgoing configuration bus response.


The `PipeLine` parameter can be used to configure the bus adapter pipelining.

* Setting `PipeLine` to `0` disables pipelining, which gives minimal latency between the bus and the core, at the cost of a combinatorial path into the core.
* Setting `PipeLine` to `1` introduces a pipelining FIFO between the core instruction/data interfaces and the bus.
  This setting increases the memory access latency, but improves timing.
