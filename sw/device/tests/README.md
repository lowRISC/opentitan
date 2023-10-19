# Chip-Level Tests

## Overview

This subtree contains three types of chip-level tests that are capable of running across all OpenTitan verification targets, using the [on-device test framework](../lib/testing/test_framework/README.md).
These targets include: DV simulation, Verilator simulation, FPGA, and eventually silicon.

## Test Types
- **Chip-level Tests** - A collection of software level tests that run on OpenTitan hardware, whose main purpose is pre-silicon verification and post-silicon bringup.
These tests consist of: smoke, IP integration, and system-level tests.
While most of these tests are top-level agnostic, some are not.
  - **Smoke Tests** - A software level test, written in C using DIFs, that performs a minimal set of operations on a given IP block to verify that it is alive and functioning.
  - **IP Integration Tests** - A software level test, written in C, that exercises some specific functionality specific to a given IP and toplevel.
  - **System-level Scenario Test** - A software level test, written in C, that mimics complex system level use case scenarios.
  Such a test is designed to encompass multiple pieces of functionality tested by the IP integration tests.

## Organization and Style Guide

### File Naming Conventions
*   Smoke tests: **{IP name}\_smoketest.c**
*   IP Integration tests: **{IP name}[\_{feature}]\_test.c**
*   System-level tests: **{use case}\_systemtest.c**

## Subfoldering Rules
*   Smoke tests will be placed in (one per IP):
    *   (generic) **sw/device/tests/**
    *   (earlgrey-specific) **sw/device/tests/earlgrey/**
    *   ({toplevel}-specific) **sw/device/tests/{toplevel}/**
*   IP Integration tests will be placed in the same folders as above.
*   System-level tests will be placed in the same folders as above.
*   IP Integration Test data (some tests, e.g. OTBN, load data files): **sw/device/tests/{IP}\_data/**
*   Target-specific tests will be subfoldered by target (see below).

#### Subfoldering Target-Specific Tests
Ideally all smoke, IP integration, and system-level tests should be target agnostic.
However, some tests require emulation of host capabilities, such as an external SPI or I2C host, an external host to encrypt/decrypt data, or an external host that toggles GPIO pins.
Eventually, host-side test initiation tools and the [on-device test framework](../lib/testing/test_framework/README.md) will make host emulation opaque to each chip-level test.
However, until then, host emulation depends on the target (e.g., DV vs. Verilator simulation).
Therefore, chip-level tests that require external stimulation from the host, will be subfoldered by target, under the appropriate toplevel folder above.
One example of such a test is the [`sw/device/tests/sim_dv/gpio_test.c`](https://github.com/lowRISC/opentitan/blob/master/sw/device/tests/sim_dv/gpio_test.c), which is subfoldered under `../sim_dv/` to indicate it is a target-specific test.

## Writing a Chip-Level Test
For instructions on how to write a chip-level test, refer to the [on-device test framework](../lib/testing/test_framework/README.md) page.

## Read More

* [Build & Test Rules](../../../rules/opentitan/README.md)
* [On-Device Test Framework (OTTF)](../lib//testing/test_framework/README.md)
* [OTP Build and Test Infrastructure](../../../hw/ip/otp_ctrl/data/README.md)
* [FPGA Bitstreams](../../../hw/bitstream/README.md)
