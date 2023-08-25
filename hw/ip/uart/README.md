# UART HWIP Technical Specification

[`uart`](https://reports.opentitan.org/hw/ip/uart/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/uart/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/uart/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/uart/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/uart/code.svg)

# Overview

This document specifies UART hardware IP functionality. This module
conforms to the
[Comportable guideline for peripheral functionality.](../../../doc/contributing/hw/comportability/README.md)
See that document for integration overview within the broader
top level system.


## Features

- 2-pin full duplex external interface
- 8-bit data word, optional even or odd parity bit per byte
- 1 stop bit
- 32 x 8b RX buffer
- 32 x 8b TX buffer
- Programmable baud rate
- Interrupt for transmit empty, receive overflow, frame error, parity error, break error, receive
  timeout

## Description

The UART module is a serial-to-parallel receive (RX) and parallel-to-serial
(TX) full duplex design intended to communicate to an outside device, typically
for basic terminal-style communication. It is programmed to run at a particular
baud rate and contains only a transmit and receive signal to the outside world,
i.e. no synchronizing clock. The programmable baud rate guarantees to be met up
to 1Mbps.

## Compatibility

The OpenTitan UART is feature compatible to a specific implementation in [Chromium EC](https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/master/chip/g/uart.c).
Additional features such as parity have been added.
