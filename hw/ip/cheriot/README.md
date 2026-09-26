# CHERIoT Memory Subsystem Technical Specification
<!-- BEGIN CMDGEN util/mdbook_regression_links.py --hjson hw/ip/cheriot/data/cheriot.hjson --top earlgrey -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`cheriot`](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/dashboard.html) | 1.0.0 | D0, V0 | ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/cheriot/test.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/cheriot/passing.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/cheriot/functional.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/cheriot/code.svg) |

<!-- END CMDGEN -->

# Overview

This document specifies the CHERIoT memory subsystem.
The subsystem sits between the CHERIoT-capable Ibex core and the main crossbar and follows the
[Comportability Specification](../../../doc/contributing/hw/comportability/README.md).

A CHERIoT capability is 65 bits in size: 32 bits pointer, 32 bits of metadata for the pointer, and a single validity tag bit.
OpenTitan keeps a 32-bit interconnect, so capabilities are transferred in two consecutive
32-bit accesses, and the tag is carried on a sideband signal, which shares the handshakes,
next to the TL-UL structs.
The subsystem is responsible for handling and storing the validity tag bit. It splits a data access
of Ibex into the data access towards the interconnect and a tag access towards a dedicated and guarded meta SRAM.

The capability validity tags for main SRAM and NVM, and the revocation bitmap for the heap stored in the main
SRAM are stored using a `sram_ctrl`.

## Features

- Splits Ibex data accesses into a data access towards the interconnect and a capability tag access
  towards the meta SRAM, and joins their responses.
- Read-modify-write access to implement bit-granular access to capability bits.
- Clears any capability tag of any location written by a non-capability store.
- Exposes the revocation bitmap into the core's address map and serves the core's TRVK filter.
- A background revocation engine that sweeps a range of capabilities within the tagged SRAM range
  and clears the tag of every capability whose base is revoked.
- Per-port access checking: each of the four requesters may only reach the meta SRAM region it owns,
  with word-granular accesses only.
- Fatal alert on a CSR bus integrity fault, a meta SRAM response integrity fault, a meta SRAM
  device error, or an error the revocation engine reports.

## Description

The CHERIoT HWIP has four requesters towards the meta SRAM and arbitrates between them:

- The *RMW filter*, which performs the bit-granular tag update for the core's *tag filter* and for
  the revocation engine's tag filter.
- The core's TRVK filter, which reads the revocation bitmap on every capability load.
- The revocation engine's TRVK filter, which reads the revocation bitmap for every capability it
  sweeps.
- The system, which reads and writes the revocation bitmap through the `revbm` memory window.

Each requester passes an *access checker* module that confirms the address falls in the region
that the requester owns and that the operation is a full-word read or write.
Invalid accesses receive a TL-UL error response.
Because the capability tag regions are not reachable from the `revbm` window, software can neither
read nor write capability tags.

Requests that the subsystem generates or rewrites get command and data integrity, so end-to-end bus
integrity is intended to hold from the Ibex lockstep through the CHERIoT HWIP domain to the storage
cells; this relies on lockstep operation of the CHERIoT subsystem, which is not implemented yet.
An integrity fault raises the `fatal_fault` alert.


See the [Theory of Operation](doc/theory_of_operation.md) for the datapath, the meta SRAM address
map, and the access-check rules.
