# Key Manager HWIP Technical Specification

This IP has been taped out in Earl Grey 1.0.0. The corresponding documentation and regression results can be found [here](https://opentitan.org/earlgrey_1.0.0/book/hw/ip/keymgr/index.html).

# Overview

This IP is deprecated and replaced by the [Key Manager DPE](../keymgr_dpe/README.md).

## Features

- One-way key and identity (working) state hidden from software.
- Version controlled identity and key generation.
- Key generation for both software consumption and hardware sideload.
- Support for DICE open profile.


## Description

The key manager implements the hardware component of the [identities and root keys](../../../doc/security/specs/identities_and_root_keys/) strategy of OpenTitan.

It enables the system to shield critical assets from software directly and provides a simple model for software to use derived key and identity outputs.
