# Mailbox Technical Specification

## Overview

The mailbox IP block in the OpenTitan Integrated design implements a request-response channel that the host System-on-Chip (SoC) may use to request security services of the Root Of Trust (RoT).
Communication is via message-passing with neither party requiring direct access to the memory address space or bus fabric of the other party.

## Features

The IP block has the following features:

- Interrupt-based signaling to the RoT when the full request message has been received from the SoC.
- Inbox and Outbox traffic is restricted to firmware-specified address ranges on the RoT side, allowing multiple instances of the IP block to share a single physical RAM co-operatively for reduced silicon area costs.
- Interrupt-based signaling to the host SoC when a response is available for collection.
- Configurable maximum request and response message lengths.
- Flow control/back-pressure mechanism prevents data loss in the event of one party having higher bus bandwidth.
- Automatic detection and reporting of error conditions.
- Software-controlled abort mechanisms that either party may use to reset and re-establish communications.

The [Theory of Operation](doc/theory_of_operation.md) covers the detailed design and implementation of the IP block.

## Description

The mailbox IP block provides a sequenced request-response communication from the SoC host to the RoT and back.

Once the mailbox IP block has been configured from the RoT side with a description of the address ranges to be used for the Inbox and the Outbox, communication is initiated from the SoC side by it writing a request into the Inbox.

The mailbox logic writes the request into the Inbox memory region and indicates to the RoT that there is a pending request.
When the request message has been collected by the RoT firmware a response is placed  into the Outbox memory region and the mailbox IP is instructed to make the response available for collection by the SoC host.

Once the SoC has retrieved the full response message from the RoT, the request-response sequence is regarded as complete and the mailbox resets for a subsequent request.

For further details on how to use the mailbox IP block from software, please consult the [Programmer's Guide](doc/programmers_guide.md).

## Compatibility

The mailbox implementation adopts the [PCIe specification defined Data Object Exchange (DOE)](https://members.pcisig.com/wg/PCI-SIG/document/18363) mailbox protocol.
