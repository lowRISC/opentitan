# CHERIoT Memory Subsystem Technical Specification
<!-- BEGIN CMDGEN util/mdbook_regression_links.py --hjson hw/ip/cheriot/data/cheriot.hjson --top earlgrey -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`cheriot`](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/dashboard.html) | 1.0.0 | D1, V0 | ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/cheriot/test.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/cheriot/passing.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/cheriot/functional.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/cheriot/code.svg) |

<!-- END CMDGEN -->

# Overview

This document specifies the CHERIoT memory subsystem.
The subsystem sits between the CHERIoT-capable Ibex core and the main crossbar and follows the
[Comportability Specification](../../../doc/contributing/hw/comportability/README.md).

A CHERIoT capability is 65 bits in size: 32 bits pointer, 32 bits meta data do the pointer, and a single validity tag bit.
OpenTitan keeps a 32-bit interconnect, so a capabilities are transferred in two consecutive 32-bit
accesses, and the tag is carried on a sideband signal, which shares the handshakes, next to the TL-UL structs
.
The subsystem is responsible for handling and storing the validity tag bit. It splits a data access
of Ibex into the data access towards the interconnect and a tag access towards a dedicated and guarded meta SRAM.

The capability validity tags for main SRAM and NVM, and the revocation bitmap for the heap stored in the main 
SRAM are stored using a `sram_ctrl`.

## Features

- Splits Ibex data accesses into a data access towards the interconnect and a capability tag access
  towards the meta SRAM, and joins their responses.
- Read-modify-write access to implement bit-granular access to capability bits.
- Clears any capability tag of any location written by a non-capability store.
- Exposes the revocation bitmap in to core's address map and serves the core's TRVK filter.exit
- Per-port access checking: each of the three requesters may only reach the meta SRAM region it owns,
  with word-granular accesses only.
- Fatal alert on a meta SRAM response integrity fault or a hardened FIFO pointer error.

## Description

The CHERIoT HWIP has three requesters towards the meta SRAM and arbitrates between them:

- The *tag filter* folled by the *RMW filter* which perform the bit-granular tag update.
- The core's TRVK filter, which reads the revocation bitmap on every capability load.
- The system, which reads and writes the revocation bitmap through the `revbm` memory window.

Each requester passes an *access checker* module that confirms the address falls in the region that
requester owns and that the operation is a full-word read or write.
Invalid acccesses receive a TL-UL error response.
Because the capability tag regions are not reachable from the `revbm` window, software can neither
read nor write capability tags.

Requests that the subsystem generates or rewrites get command and data integrity, so end-to-end bus 
integrity holds from the Ibex lockstep through the CHERIoT HWIP domain to the storage cells. 
An integrity fault raises the `fatal_fault` alert.


See the [Theory of Operation](doc/theory_of_operation.md) for the datapath, the meta SRAM address
map, and the access-check rules.

