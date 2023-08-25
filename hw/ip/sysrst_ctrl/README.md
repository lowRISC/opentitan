# System Reset Control Technical Specification

[`sysrst_ctrl`](https://reports.opentitan.org/hw/ip/sysrst_ctrl/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/sysrst_ctrl/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/sysrst_ctrl/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/sysrst_ctrl/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/sysrst_ctrl/code.svg)

# Overview

This document specifies the functionality of the System Reset Controller (`sysrst_ctrl`) that provides programmable hardware-level responses to trusted IOs and basic board-level reset sequencing capabilities.
These capabilities include keyboard and button combination-triggered actions, reset stretching for system-level reset signals, and internal reset / wakeup requests that go to the OpenTitan reset and power manager blocks.
This module conforms to the [Comportable guideline for peripheral functionality](../../../doc/contributing/hw/comportability/README.md).
See that document for integration overview within the broader top level system.

## Features

The IP block implements the following features:

- Always-on: uses the always-on power and clock domain
- EC reset pulse duration control and stretching
- Keyboard and button combination (combo) triggered action
- AC_present can trigger interrupt
- Configuration registers can be set and locked until the next chip reset
- Pin output override

## Description

The `sysrst_ctrl` logic is very simple.
It looks up the configuration registers to decide how long the EC reset pulse duration and how long the key presses should be.
Also what actions to take (e.g. Interrupt, EC reset, OpenTitan reset request, disconnect the battery from the power tree).

## Compatibility

The configuration programming interface is not based on any existing interface.
