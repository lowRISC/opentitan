---
title: "Memory Protection Module"
---

<p style="color: red; text-align: right;">
  Status: Draft
</p>

# Objective

The overall goal of the Memory Protection Module is to minimize risk of unverified code execution through the use of Ibex's enhanced Physical Memory Protection (ePMP) mechanism during secure boot.

# Requirements

There are four types of memory mapped to address spaces in OpenTitan:

 * Read-Only Memory (ROM)
 * Random Access Memory (RAM)
 * Flash Memory (eFLASH)
 * Memory Mapped I/O (MMIO)

For the purposes of the mask ROM there are only two regions within these address spaces that need to be executable: the executable code for the mask ROM itself (ROM text) and - after successful signature verification - the executable code for the ROM extension (`ROM_EXT` text) that resides in eFlash.
The ePMP feature should be used to block execution of code in all other memory regions in order to minimize the chances that unverified code could be executed.

The mask ROM requires read-only access to the other parts of the ROM and eFlash.
It also requires read-write access to RAM and memory mapped I/O so that the mask ROM can interact with memory and peripherals as needed.

Assuming it completes successfully the mask ROM must not permanently lock any PMP configuration or address registers.
Later boot stages and/or other software running on the device such as an operating system kernel will need to be able to use all of the PMP entries.
This flexibility also means that the ROM extension is free to use a different PMP schema to the mask ROM if required, decoupling the two boot stages.

# Implementation

Ibex's [enhanced Physical Memory Protection (ePMP)](https://ibex-core.readthedocs.io/en/latest/03_reference/pmp.html) feature consists of 16 PMP entries each of which may be individually configured to allow or disallow different types of access (read, write and/or execute) to a specified memory region.
The entry with the lowest index that matches any part of an access is solely responsible for determining whether that access succeeds or not.
A Machine Security Configuration (`mseccfg`) register is also provided that exposes some additional configuration options that apply to all of the PMP entries.

The implementation strategy is based on the Rule Locking Bypass (RLB) and Machine Mode Whitelist Policy (MMWP) modes being enabled.
RLB allows the reuse of PMP entries with `L` bit set, which otherwise would be inaccessible until the next system reset.
MMWP makes the default behavior when no entries match an access to deny that access.

All entries configured by the mask ROM must have the `L` bit set otherwise they will not apply in machine mode.

Once initially configured the PMP configuration is expected to remain static throughout the execution of the mask ROM with the exception of the `ROM_EXT` text entry which will be configured after signature verification.

## PMP Entry Allocation

Each memory region the mask ROM is concerned with has its own dedicated PMP entry.
The allocation here is arbitrary except that overlapping regions are placed next to one another with the smaller more specific region given a higher priority entry.
For example, the ROM TEXT entry precedes the more general ROM entry of which it is a sub region.

The entry allocation is shown here:

| Entry | Description                   | Permissions | Addressing Mode |
|-------|-------------------------------|-------------|-----------------|
| 0     |                               |             | OFF\*           |
| 1     | ROM TEXT                      | RX          | TOR             |
| 2     | ROM                           | R           | NAPOT           |
| 3     |                               |             | OFF\*           |
| 4     | `ROM_EXT` TEXT                | RX          | TOR             |
| 5     | eFlash                        | R           | NAPOT           |
| 6     | \<Reserved - see test plan\>  |             | OFF             |
| 7     |                               |             | OFF             |
| 8     |                               |             | OFF             |
| 9     |                               |             | OFF             |
| 10    |                               |             | OFF\*           |
| 11    | MMIO (includes retention RAM) | RW          | TOR             |
| 12    |                               |             | OFF             |
| 13    |                               |             | OFF             |
| 14    | Stack Guard (4 bytes)         | \<none\>    | NA4             |
| 15    | RAM                           | RW          | NAPOT           |

Entries that use the Top-Of-Range (TOR) addressing mode use the address register of the preceding entry, effectively requiring two entries.
Entries that are OFF but for which the address register is in use are marked with a \*.

## Initial Configuration

| Entry | Description                   | Permissions | Addressing Mode |
|-------|-------------------------------|-------------|-----------------|
| 1     | ROM TEXT                      | RX          | TOR             |
| 2     | ROM                           | R           | NAPOT           |
| 5     | eFlash                        | R           | NAPOT           |
| 11    | MMIO (includes retention RAM) | RW          | TOR             |
| 14    | Stack Guard (4 bytes)         | \<none\>    | NA4             |
| 15    | RAM                           | RW          | NAPOT           |

## Unlocked Configuration

Once signature verification is complete the `ROM_EXT` text section can be made executable.
It is critical that the memory region that is unlocked matches the memory region specified in the verified manifest.
The unlock address space module will provide an API for unlocking the `ROM_EXT` text section based on a memory region provided to it.
In case the address translation is enabled, indicated by the `address_translation` field of the manifest, a read-only section will be added
for the `ROM_EXT` virtual address.

| Entry | Description                   | Permissions | Addressing Mode |
|-------|-------------------------------|-------------|-----------------|
| 1     | ROM TEXT                      | RX          | TOR             |
| 2     | ROM                           | R           | NAPOT           |
| **4** | **`ROM_EXT` TEXT**            | **RX**      | **TOR**         |
| 5     | eFlash                        | R           | NAPOT           |
| **6** | **`ROM_EXT` section**         | **R**       | **NAPOT**       |
| 11    | MMIO (includes retention RAM) | RW          | TOR             |
| 14    | Stack Guard (4 bytes)         | \<none\>    | NA4             |
| 15    | RAM                           | RW          | NAPOT           |

## Verification

The mask ROM must verify that the ePMP configuration matches the expected configuration.
This is done by maintaining a copy of the ePMP configuration in RAM and comparing it to the actual ePMP configuration.
The unlock address space module will provide an API for doing this but exactly when and how often the ePMP configuration is verified is left as an integration task as it will need to be tightly coupled with other critical code.

# API

The API will be split into two main parts: the mask ROM specific code and more general purpose code for tracking ePMP state that could potentially be reused by other silicon creator code (i.e. the ROM extension).

## Mask ROM Memory Protection API

The mask ROM specific code has an assembly API for initially configuring the PMP entries before C code can be executed and the C API that is responsible for unlocking the ROM extension for execution.

 * Assembly API (TBD)
 * C API (TBD)

## Silicon Creator ePMP Library API

 * C API (TBD)

# Test Plan

## On-device Tests

On device tests require the DV address space be writable so that the test result can be reported.
PMP entry 6 should be used for this purpose.

| Entry | Description                   | Permissions | Addressing Mode |
|-------|-------------------------------|-------------|-----------------|
| 6     | DV                            | RW          | NA4             |

### Functional Test (Simulation/FPGA Only)

The functional test will be a simplified ROM image linked against the same ePMP setup code as the mask ROM.
The test will verify that the execution permissions specified are applied correctly to each memory region by attempting to execute code in that region.

The functional test will also check that the function that unlocks the `ROM_EXT` for execution unlocks exactly the region specified.

### ROM Extension Entry State Test

The state of the ePMP CSRs at the end of the mask ROM boot stage is fixed (known at compile time) with the exception of the address registers associated with the `ROM_EXT` executable region that resides within the flash bank the location of which is read from the `ROM_EXT` manifest.

The simplest on-device test consists of a `ROM_EXT` binary image, compiled so that it can run in either flash bank (two binaries could be used if position independent code is not possible).
Upon entry the test binary will compare the PMP CSRs against the expected state.

## Unit tests

Unit tests can make use of the existing CSR unit test framework.
The focus of these tests will be on making sure that the verification functionality in the mask ROM validates the PMP configuration correctly.

There may be other unit tests added as the implementation is hardened and there are additional checks to test.

## Error handling tests

The Memory Protection module is not responsible for testing the state of the ePMP CSRs when the boot sequence is aborted.
The Shutdown module tests must ensure that the ePMP CSRs are locked down correctly when an error occurs.
