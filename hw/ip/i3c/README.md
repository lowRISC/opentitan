# I3C Controller/Target

# Overview

This document specifies the I3C Controller/Target IP functionality.

## Features

In summary, the IP block implements the following features:

- I3C Primary Controller.
- I3C Target.
- Host Controller Interface (HCI) in PIO mode.
- Target Transaction Interface.
- 2-4KiB message buffer.
  - Apportioned in software amongst Controller- and Target-side logical queues.
  - Queues may be sized appropriately for the use case.
  - The design uses a single-ported SRAM, which offers a considerable area saving.
- Entire message buffer may optionally be accessed directly by software when the IP block is not using it, or for diagnostic purposes.
  - Provides extra general-purpose memory on the system bus when I3C not in use.

### Controller-side features

- Designed for a 50MHz clock, supporting 4 phases for 12.5MHz signaling.
- Design parameter supports other clock frequencies.
- HCI implementation.
- PIO mode only; no support for DMA.
- Configurable Device Address Table (DAT) and Device Characteristics Table (DCT) dimensions.
  - DAT defaults to 32 entries, the maximum size supported by the HCI.
  - DCT defaults to 32 entries
    - Dynamic Address Assignment (DAA) may be decomposed into multiple operations by firmware to support more targets.
- Signaling modes:
  - Single Data Rate (SDR)
    - 12.5Mbps theoretical peak.
  - Double Data Rate (HDR-DDR)
    - 25Mbps theoretical peak; minus overheads this is 20Mbps throughput for long transfers.
  - No support for HDR-BT mode or Multi-Lane transfers.
  - I2C Fast Mode and Fast Mode Plus support for backwards compatibility with some I2C devices.
- Primary Controller.
  - This version of the IP block does not support the Secondary Controller role, Controller Role Handoff or operation as a Standby Controller.

### Target-side features

- Designed for 50MHz IP clock (shared with the Controller-side logic).
- I3C transceiver logic is driven by the I3C SCL signal directly.
- Support for 'Deepest Sleep' state, with wake-up detection being performed by the Target Reset detector.
  - Almost all logic powered-down, and no free-running clock required; clocked by I3C signaling.
- Signaling modes:
  - Single Data Rate (SDR), 12.5Mbps.
  - Double Data Rate (HDR-DDR), 25Mbps signaling/20Mbps throughput.
- Target Transaction Interface (TTI).
  - Modeled on the HCI, supporting:
    - Tx/Rx transfers, longer than the associated data buffers.
    - IBI data payloads, longer than buffer.
    - Asynchronous event queue, reporting bus activity and errors.
- Supports a parameterized number of Virtual Targets.
  - Defaults to 2 Virtual Targets.
  - Maximum of 4 without incurring changes to the IP address map and software compatibility.
- Group addressing.
  - Defaults to 8 group addresses across all Virtual Targets.
  - An arbitrary subset of all Virtual Targets may be subscribed to each group.

## Description

The I3C IP block provides both Controller and Target functionality on a single I3C bus.
The Controller and the Target share the SCL and SDA signals of the IP block, and software enables one of them at a time.
The IP block may thus operate as follows:

- As the Active Controller of the bus.
- As a Target on a bus that another Controller controls.

Software must not enable both Controller and Target functionality at the same time, as the I3C Basic Specification (Section 3.2) does not permit a device to function as Controller and Target at the same time.
The hardware does not prevent this.

On a bus with several Controller-capable devices, the IP block operates either as the Primary Controller, which keeps the Controller role, or as a Target; it does not support the Secondary Controller role (see [Buses with several Controller-capable Devices](doc/theory_of_operation.md#buses-with-several-controller-capable-devices)).

## Compatibility

The IP block implements the following specifications:

- MIPI Alliance Specification for I3C Host Controller Interface (I3C HCI) Version 1.2.
- MIPI Alliance Specification for I3C Transfer Command Response (I3C TCRI) Version 1.0.
- MIPI Alliance Specification for I3C Basic (I3C Basic) Version 1.2.
