# Key Manager DPE HWIP Technical Specification
<!-- BEGIN CMDGEN util/mdbook_regression_links.py --hjson hw/ip/keymgr_dpe/data/keymgr_dpe.hjson --top darjeeling -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`keymgr_dpe`](https://dashboard.reports.lowrisc.org/opentitan/darjeeling/dashboard.html) | 2.0.0 | D0, V0 | ![](https://dashboard.reports.lowrisc.org/opentitan/darjeeling/badge/keymgr_dpe/test.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/darjeeling/badge/keymgr_dpe/passing.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/darjeeling/badge/keymgr_dpe/functional.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/darjeeling/badge/keymgr_dpe/code.svg) |

<!-- END CMDGEN -->

> Keymgr DPE is currently under development according to [this RFC](https://docs.google.com/document/d/1iF0EWyJkSEtRL9d057imLo4s6DWNrZ6Mpt0QKD8OMMc/).
> This is indicated by the development stages (see [`keymgr_dpe.hjson`](https://github.com/lowRISC/opentitan/blob/master/hw/ip/keymgr_dpe/data/keymgr_dpe.hjson) and [here](https://opentitan.org/book/doc/project_governance/development_stages.html)).
> As a result, the documentation can slightly differ from the current RTL implementation.

# Overview

This document specifies the functionality of the OpenTitan key manager DPE which implements the [DICE Protected Environment (DPE)](https://trustedcomputinggroup.org/wp-content/uploads/TCG-DICE-Protection-Environment-Specification_14february2023-1.pdf).

## Features

- Multiple key slots, each holding one DICE context whose secret is hidden from software.
- One-way key derivation, computed by KMAC over hardware- and software-supplied inputs.
- Software-controlled DICE hierarchy: any valid slot can act as the parent of a newly derived child slot.
- Per-slot policies that constrain whether children may be derived and whether the parent is retained.
- Version controlled key generation, bounded by a per-slot maximum key version.
- Key generation for both software consumption and hardware sideload (AES, KMAC, OTBN and HMAC).
- Support for DICE open profile and for the DICE Protection Environment (DPE).

## Description

The Keymgr DPE implements the hardware component of the [identities and root keys](../../../doc/security/specs/identities_and_root_keys/) strategy of OpenTitan.

It enables the system to shield critical assets from software directly and provides a simple model for software to use derived key outputs, which software uses in turn to construct DICE identities and certificates.
Keymgr DPE holds `NumInstHwSlot` key slots (configurable up to `NumMaxHwSlot`, currently 8), each storing an independent DICE context.
Software selects the source and the destination slot of every operation, so several DICE contexts can coexist and be arranged into a hierarchy instead of a single chain.

See the [Theory of Operation](doc/theory_of_operation.md) for the derivation scheme, the working state machine and the peripheral connections, and the [Programmer's Guide](doc/programmers_guide.md) for the register sequences that drive each operation.
