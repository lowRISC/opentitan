---
title: "Ibex RISC-V Core Wrapper Technical Specification"
---

# Overview

This document specifies Ibex CPU core wrapper functionality.


## Features

* Instantiation of a [Ibex RV32 CPU Core](https://github.com/lowRISC/ibex).
* TileLink Uncached Light (TL-UL) host interfaces for the instruction and data ports.

## Description

The Ibex RISC-V Core Wrapper instantiates an [Ibex RV32 CPU Core](https://github.com/lowRISC/ibex), and wraps its data and instruction memory interfaces to TileLink Uncached Light (TL-UL).
All configuration parameters of Ibex are passed through.
The pipelining of the bus adapters is configurable.

## Compatibility

Ibex is a compliant RV32 RISC-V CPU core, as [documented in the Ibex documentation](https://ibex-core.readthedocs.io/en/latest/01_overview/compliance.html).

The TL-UL bus interfaces exposed by this wrapper block are compliant to the [TileLink Uncached Lite Specification version 1.7.1](https://sifive.cdn.prismic.io/sifive%2F57f93ecf-2c42-46f7-9818-bcdd7d39400a_tilelink-spec-1.7.1.pdf).

# Theory of Operations

## Hardware Interfaces

All ports and parameters of Ibex are exposed through this wrapper module, except for the instruction and data memory interfaces (signals starting with `instr_` and `data_`).
Refer to the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/02_user/integration.html) for a detailed description of these signals and parameters.

The instruction and data memory ports are exposed as TL-UL ports.

```verilog
// Instruction memory interface
output tlul_pkg::tl_h2d_t     tl_i_o,
input  tlul_pkg::tl_d2h_t     tl_i_i,

// Data memory interface
output tlul_pkg::tl_h2d_t     tl_d_o,
input  tlul_pkg::tl_d2h_t     tl_d_i,
```

The `PipeLine` parameter can be used to configure the bus adapter pipelining.

* Setting `PipeLine` to `0` disables pipelining, which gives minimal latency between the bus and the core, at the cost of a combinatorial path into the core.
* Setting `PipeLine` to `1` introduces a pipelining FIFO between the core instruction/data interfaces and the bus.
  This setting increases the memory access latency, but improves timing.
