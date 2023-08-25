# GPIO HWIP Technical Specification

[`gpio`](https://reports.opentitan.org/hw/ip/gpio/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/gpio/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/gpio/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/gpio/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/gpio/code.svg)

# Overview

This document specifies GPIO hardware IP functionality. This
module conforms to the [Comportable guideline for peripheral device
functionality](../../../doc/contributing/hw/comportability/README.md)
See that document for integration overview within the broader top
level system.

## Features

- 32 GPIO ports
- Configurable interrupt per GPIO for detecting rising edge, falling edge,
  or active low/high input
- Two ways to update GPIO output: direct-write and masked (thread-safe) update

## Description

The GPIO block allows software to communicate through general purpose I/O
pins in a flexible manner. Each of 32 independent bits can be written
as peripheral outputs in two modes. Each of the 32 bits can be read
by software as peripheral inputs.  How these peripheral inputs and
outputs are connected to the chip IO is not within the scope of this
document. See the Comportability Specification for peripheral IO options
at the top chip level.

In the output direction, this module provides direct 32b access to each
GPIO value using direct write. This mode allows software to control all
GPIO bits simultaneously. Alternately, this module provides masked writes
to half of the bits at a time, allowing software to affect the output
value of a subset of the bits without requiring a read-modify-write.
In this mode the user provides a mask of which of the 16 bits are to be
modified, along with their new value. The details of this mode are given
in the [Programmers Guide](#programmers-guide) below.

In the input direction, software can read the contents of any of the GPIO
peripheral inputs.  In addition, software can request the detection of an
interrupt event for any of the 32 bits in a configurable manner.  The choices
are positive edge, negative edge or level detection events. A noise
filter is available through configuration for any of the 32 GPIO inputs.
This requires the input to be stable for 16 cycles of the
module clock before the input register reflects the change and interrupt
generation is evaluated. Note that if the filter is enabled and the pin
is set to output then there will be a corresponding delay in a change
in output value being reflected in the input register.

See the Design Details section for more details on output, input, and
interrupt control.
