# Key Manager HWIP Technical Specification

{{#block-dashboard keymgr}}

# Overview

This document specifies the functionality of the OpenTitan key manager.

## Features

- One-way key and identity (working) state hidden from software.
- Version controlled identity and key generation.
- Key generation for both software consumption and hardware sideload.
- Support for DICE open profile.


## Description

The key manager implements the hardware component of the [identities and root keys](https://docs.opentitan.org/doc/security/specs/identities_and_root_keys/) strategy of OpenTitan.

It enables the system to shield critical assets from software directly and provides a simple model for software to use derived key and identity outputs.
