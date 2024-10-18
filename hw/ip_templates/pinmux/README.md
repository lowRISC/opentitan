# Pinmux Technical Specification


# Overview

This document specifies the functionality of the pin multiplexer (`pinmux`) peripheral.
This module conforms to the [OpenTitan guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability).
See that document for integration overview within the broader OpenTitan top level system.
The module provides a mechanism to reconfigure the peripheral-to-pin mapping at runtime, which greatly enhances the system flexibility.
In addition to that, the `pinmux` also allows the user to control pad attributes (such as pull-up, pull-down, open-drain, drive-strength, keeper and inversion), and it contains features that facilitate low-power modes of the system.
For example, the sleep behavior of each pad can be programmed individually, and the module contains additional pattern detectors that can listen on any IO and wake up the system if a specific pattern has been detected.

## Features

- Configurable number of chip bidirectional IOs

- Configurable number of peripheral inputs and outputs

- Programmable mapping from peripheral outputs (and output enables) to top-level outputs (and output enables)

- Programmable mapping from top-level inputs to peripheral inputs

- Programmable control of chip pad attributes like output drive-strength, pull-up, pull-down and virtual open-drain

- Programmable pattern detectors to detect wakeup conditions during sleep mode

- Programmable sleep mode behavior

- Support for life-cycle-based JTAG (TAP) isolation and muxing
