# I2C HWIP Technical Specification

[`i2c`](https://reports.opentitan.org/hw/ip/i2c/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/i2c/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/i2c/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/i2c/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/i2c/code.svg)

# Overview

This document specifies I2C hardware IP functionality.
This module conforms to the [Comportable guideline for peripheral functionality.](../../../doc/contributing/hw/comportability/README.md)
See that document for integration overview within the broader top level system.

## Features

- Two-pin clock-data parallel bidirectional external interface: SCL (serial clock line) and SDA (serial data line)
- Support for I2C Host ("I2C Master"<sup>1</sup>) and I2C Target ("I2C Slave"<sup>1</sup>) device modes
- Support for Standard-mode (100 kbaud), Fast-mode (400 kbaud) and Fast-mode Plus (1 Mbaud)
- Bandwidth up to 1 Mbaud
- Support for all "Mandatory" features as specified for I2C Hosts (as listed in Table 2 of the [I2C specification (revision 6)](https://web.archive.org/web/20210813122132/https://www.nxp.com/docs/en/user-guide/UM10204.pdf)):
    - Start condition
    - Stop condition
    - Acknowledge (ACK)
    - 7-bit target address
- Support for the following optional capabilities:
    - Clock stretching in the host mode
    - Automatic clock stretching in the target mode<sup>2</sup>
- *No support at this time* for any of the features related to multi-host control:
    - No support for host-host clock synchronization
    - No support for host bus arbitration.
- Byte-formatted register interface with four separate queues: two queues in the host mode, one for holding read data (RX), the other for holding bytes to be transmitted (TX: addresses or write data) and two queues in the target mode, for holding read (RX) and write (TX) data
- Direct SCL and SDA control in "Override mode" (for debugging)
- SCL and SDA ports mapped to I/O via the pinmux
- Interrupts in the host mode for FMT and RX FIFO overflow, target NACK, SCL/SDA signal interference, timeout, unstable SDA signal levels, and transaction complete
- Interrupts in the target mode for TX FIFO empty during a read, TX FIFO nonempty at the end of a read, TX overflow and ACQ FIFO full, host sending STOP after ACK, and host ceasing to send SCL pulses during an ongoing transaction
- Loopback support with external host when in target operation
- SW may reset I2C block using the Reset Manager

<sup>1</sup> lowRISC is avoiding the fraught terms master/slave and defaulting to host/target where applicable.

<sup>2</sup> The target is only compatible with hosts that support clock stretching.
For hosts that do not support clock stretching, it is expected that there must be an additional protocol to guarantee there is always sufficient space and data.
These protocols are not in scope of this document.

## Description

This IP block implements the [I2C specification (rev. 6)](https://web.archive.org/web/20210813122132/https://www.nxp.com/docs/en/user-guide/UM10204.pdf), though with some variation in nomenclature.
For the purposes of this document, an "I2C Host" meets the specifications put forth for a "Master" device.
Furthermore, a device which meets the specifications put forward for an "I2C Slave" device is here referred to as an "I2C Target" or "I2C Target Device".

At a high-level, the I2C protocol is a clock-parallel serial protocol, with at least one host issuing transactions to a number of targets on the same bus.
Though I2C optionally allows for multiple hosts on the same bus, we do not support this feature at this time.

Every transaction consists of a number of bytes transmitted, either from host-to-target or target-to-host.
Each byte is typically followed by a single bit acknowledgement (ACK) from the receiving side.
Typically each transaction consists of:
1. A START signal, issued by the host.
1. An address, issued by the host, encoded using 7 bits.
1. An R/W bit indicating if the transaction is a read-from or a write-to the target device.
The R/W bit is encoded along with the address.
1. An acknowledge signal (ACK) sent by the target device.
1. Data bytes, where the number of bytes required is indicated by the host,
in a manner which differs between reads and writes.
    - For write transactions, the target device sends an ACK signal after every byte received.
    The host indicates the end of a transaction by sending a STOP or repeating the START signal.
    - For read transactions, the target device continues to send data as long as the host acknowledges the target-issued data by sending an ACK signal.
    Once the host has received all the required data it indicates that no more data is needed by explicitly de-asserting the ACK signal (this is called a NACK signal) just before sending a STOP or a repeated START signal.
1. A STOP signal or a repeated START signal.

This protocol is generally quite flexible with respect to timing constraints, and slow enough to be managed by a software microcontroller, however such an implementation requires frequent activity on the part of the microcontroller.
This IP presents a simple register interface and state-machine to manage the corresponding I/O pins directly using a byte-formatted programming model.

## Compatibility

This IP block should be compatible with any target device covered by the [I2C specification (rev. 6)](https://web.archive.org/web/20210813122132/https://www.nxp.com/docs/en/user-guide/UM10204.pdf), operating at speeds up to 1 Mbaud.
This IP in the host mode issues addresses in 7-bit encoding, and in the target mode, receives addresses in 7-bit encoding.
(It remains the obligation of system designers to ensure that devices remain in a 7-bit address space.)
This IP also supports clock-stretching, should that be required by target devices.
