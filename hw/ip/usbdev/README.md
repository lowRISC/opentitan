# USB 2.0 Full-Speed Device HWIP Technical Specification

[`usbdev`](https://reports.opentitan.org/hw/ip/usbdev/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/usbdev/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/usbdev/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/usbdev/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/usbdev/code.svg)

# Overview

This document specifies the USB device hardware IP functionality.
This IP block implements a Full-Speed device according to the [USB 2.0 specification.](https://www.usb.org/document-library/usb-20-specification)
It is attached to the chip interconnect bus as a peripheral module and conforms to the [Comportable guideline for peripheral functionality.](../../../doc/contributing/hw/comportability/README.md)


## Features

The IP block implements the following features:

- USB 2.0 Full-Speed (12 Mbps) Device interface
- 2 kB interface buffer
- Up to 12 endpoints (including required Endpoint 0), configurable using a compile-time Verilog parameter
- Support for USB packet sizes up to 64 bytes
- Support SETUP, IN and OUT transactions
- Support for Bulk, Control, Interrupt and Isochronous endpoints and transactions
- Streaming possible through software
- Interrupts for packet reception and transmission
- Flippable D+/D- pins, configurable via software, useful if it helps routing the PCB or if D+/D- are mapped to SBU1/SBU2 pins of USB-C

Isochronous transfers larger than 64 bytes are currently not supported.
This feature might be added in a later version of this IP.


## Description

The USB device module is a simple software-driven generic USB device interface for Full-Speed USB 2.0 operation.
The IP includes the physical layer interface, the low level USB protocol and a packet buffer interface to the software.
The physical layer interface features multiple transmit and receive paths to allow interfacing with a variety of USB PHYs or regular 3.3V IO pads for FPGA prototyping.


## Compatibility

The USB device programming interface is not based on any existing interface.
