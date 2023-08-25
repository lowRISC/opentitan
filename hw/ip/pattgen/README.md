# Pattern Generator HWIP Technical Specification

[`pattgen`](https://reports.opentitan.org/hw/ip/pattgen/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/pattgen/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/pattgen/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/pattgen/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/pattgen/code.svg)

# Overview

This document specifies the functionality of the pattern generator hardware IP (HWIP).
This module conforms to the [Comportable guideline for peripheral functionality.](../../../doc/contributing/hw/comportability/README.md)
See that document for integration overview within the broader top-level system.

## Features

- Generates time-dependent patterns on two (2) channels, each with its own clock.
   - In each channel, data is transmitted serially on a one-bit data (`pda`) output, which is synchronous to a corresponding parallel clock signal (`pcl`).
   - The channels can operate independently or synchronously with each other.
- Each output channel supports the following configuration settings:
    - Pattern data per output (up to 64 bits of data).
    - 32-bit pre-divider to derive pattern clock from I/O clock (minimum ratio: 2).
    - Each pattern can be repeated up to 1024 times.
    - The polarity of the clock signal is programmable.
- The block sends an interrupt on pattern completion.

## Description

The pattern generator HWIP transmits short (maximum 64 bits) time-dependent data patterns on two clock-parallel channels.
Each channel consists of one clock (`pcl`) and one data (`pda`) line.
The output channels may be activated and operated independently, or they can be started at the same time to effectively create a 4-output pattern.

## Compatibility

This IP block does not have any direct hardware compatibility requirements.
