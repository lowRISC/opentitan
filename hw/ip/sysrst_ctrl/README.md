# System Reset Control Technical Specification
<!-- BEGIN AUTOGEN from util/mdbook_regression_links.py -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`sysrst_ctrl`](https://nightly.reports.lowrisc.org/opentitan_weekly_earlgrey/2026_03_08/index.html) | 2.0.0 | D3, V2S | <img src="https://img.shields.io/badge/Tests_Running-932-blue"> <img src="https://img.shields.io/badge/Tests_Passing-96.89%25-brightgreen"> <img src="https://img.shields.io/badge/Functional_Coverage-87.11%25-green"> <img src="https://img.shields.io/badge/Code_Coverage-98.20%25-brightgreen"> |

This IP has been taped out in Earl Grey 1.0.0. The corresponding documentation and regression results can be found [here](https://opentitan.org/earlgrey_1.0.0/book/hw/ip/sysrst_ctrl/index.html).
<!-- END AUTOGEN -->

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
