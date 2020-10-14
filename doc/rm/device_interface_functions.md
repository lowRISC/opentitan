---
title: "Device Interface Functions (DIFs)"
---

## Motivation

Every hardware peripheral needs some form of higher-level software to actuate it to perform its intended function.
Device Interface Functions (DIFs) aim to make it easy to use hardware for its intended purposes while making it difficult, or impossible, to misuse.
DIFs can be seen as a living best-practices document for interacting with a given piece of hardware.

## Objectives

DIFs provide extensively reviewed APIs for actuating hardware for three separate use cases: design verification, FPGA + post-silicon validation, and reference firmware including end-consumer applications.

## Requirements

### Common Requirements

#### Language

DIFs **must** be written in C, specifically [C11 (with a few allowed extensions)]({{< relref "doc/rm/c_cpp_coding_style.md#c-style-guide" >}}).
DIFs **must** conform to the style guide in [`sw/device/lib/dif/README.md`]({{< relref "sw/device/lib/dif/README.md" >}}).

DIFs **must** only depend on:

*   the [freestanding C library headers]({{< relref "sw/device/lib/base/freestanding/README.md" >}}),
*   compiler runtime libraries (e.g. libgcc and compiler-rt),
*   the bitfield library for manipulating bits in binary values (`sw/device/lib/base/bitfield.h`),
*   the mmio library for interacting with memory-mapped registers (`sw/device/lib/base/mmio.h`),
*   the memory library for interacting with non-volatile memory (`sw/device/lib/base/memory.h`), and
*   any IP-specific register definition files.

DIFs **must not** depend on DIFs for other IP blocks, or other external libraries.

This decision is motivated by the requirement that DIFs must be extremely flexible in their possible execution environments, including being hosted in bare metal, or being called from other languages such as Rust through Foreign Function Interface.

#### Runtime Independence

DIFs **must not** depend on runtime services provided by an operating system.
If functions must be called in response to system stimulus such as interrupts then the DIF must make these requirements explicit in their documentation.
This decision makes DIFs appropriate for execution environments without OS support such as DV.

### Architecture Independence

DIFs **should not** depend on architecture-specific constructs such as inline assembly or platform-defined registers, except where a peripheral is integrated into the core in a way making them unavoidable.
As a concrete example: a SPI DIF must not depend on a pinmux or clock control DIF in order to be operated.
This highlights a clear separation of concern: making a pin on the package driven from the SPI block involves multiple systems.
By design, a DIF cannot coordinate cross-functional control.

#### Coverage Requirements

DIFs *must* actuate all of the specification-required functionality of the hardware that they are written for, and no more.
A DIF cannot be declared complete until it provides an API for accessing all of the functionality that is expected of the hardware.
This is distinct from mandating that a DIF be required to cover all of the functionality of a given piece of hardware.

## Details

### Verification Stage Allowances

DV, FPGA, and early silicon validation have unique requirements in their use of hardware.
They might actuate hardware on vastly different timescales, use verification-specific registers, or otherwise manipulate aspects of the hardware that "production"-level code would not (or cannot) do.
To this end, verification-only functionality may be added to a DIF **only** in modules that are included in verification.
This functionality **must not** be made accessible outside of verification environments, and is enforced by not including DV-specific code in non-DV builds.

### Separation of Concerns and Stateful Information

In addition to the interface functions themselves, DIFs are expected to usually take the form of a structure that contains instance-specific information such as base register addresses and non-hardware-backed state required to actuate the hardware.
DIFs **should not** track hardware-backed state in their own state machine.

A DIF instance is expressly an instance of a hardware block, so DIFs **must not** intrinsically know the location of the hardware blocks they're associated with in memory.
That is:

```c
dif_timer_init_result_t dif_timer_init(dif_timer_t *timer,
                                       const timer_config_t *config,
                                       uintptr_t base_address);
```

allows the system initialization code to instantiate timers at specific locations, whereas:

```c
// Don't do this:
bool dif_timer_init(timer_t *timer, enum timer_num num);
```

suggests that the timer DIF knows about the number and placement of timers in the system.

DIFs **must not** store or provide information in their implementation or state that is outside of their area of concern.
The number of timers in a system is the concern of the system, not the timer DIF.

### Naming

All DIF functions **must** have clear direct objects and verbs, be written in the imperative mood, and follow the format of `dif_<object>_<verb_phrase>`.
The object in the name must be common to the DIF it appears it, and unique among DIFs.

Consider the following examples of good names:

*   `dif_timer_init`,
*   `dif_timer_reset`,
*   `dif_timer_set_time_remaining`,
*   `dif_timer_get_time_remaining`.

The following are bad names:

*   `dif_clear_timer` (wrong object/verb-phrase ordering),
*   `dif_timer_gets_reset` (passive voice not imperative),
*   `timer_init` (not correctly prefixed for C).

Prefer common names: `init` is more commonly written than `initialize`, but `reset` is more commonly written than `rst`, for example.
This is a subjective call on the DIF author and reviewers' parts, so common agreement will be more useful than strict prescription.

### Documentation

All DIF exported types and functions **must** have associated API documentation.
All function parameters **must** be documented.
All function semantics **must** be documented, no matter how obvious one suspects the function to be.
The documentation should be exhaustive enough that the implementation can reasonably be inferred from it and the IP specification.

It is important that the DIFs are documented alongside the hardware IP that they are written for.
Each hardware IP block also contains a "programmers' guide" section, which tells programmers how to use the hardware interfaces correctly, using prose descriptions and relevant diagrams.
The prose descriptions should include references to relevant DIF functions.

Programmers' guides **should** primarily refer to the [Software API Documentation]({{< relref "/sw#opentitan-software-api-documentation" >}}).
Programmers' guides **should not** contain standalone examples that do not match how we implement DIFs and can become out of date.
The software API documentation includes full source code of the respective DIFs, should extra clarity be needed to explain how a hardware interface should be used.

The programmers' guide must also include a list of DIF functions which relate to it, along with a brief description of each, and a link to further API documentation.

### Source Layout

DIFs **must** live in the `sw/device/lib/dif` folder.
They **must** comprise at least one header unique to the hardware in question, and **may** contain more than one C file providing the implementation, if the complexity of the implementation warrants it (this is subjective).
Any files for a given IP should have a filename starting `dif_<IP name>`.

Verification-specific extensions and logic **must not** live in `sw/device/lib/dif`.
This code must be placed in the directory belonging to the verification domain which the extension is applicable to.
Verification-specific extensions must not be built and included in production firmware builds.

### Testing

Tests **must** live in the `sw/device/tests/dif` folder.

DIFs **must** have unit tests, which cover all their specification-required functionality.
These unit tests use a mocking system which allows the test to control all hardware reads and writes, without requiring complex management of the hardware.
These unit tests are written using [googletest](https://github.com/google/googletest), and may be run on a non-RISC-V host.

DIFs **should** also have other tests, including standalone C sanity tests---which can quickly diagnose major issues between the DIF and the hardware but are not required to test all device functionality.

DIFs are also being used by DV for chip-level tests, which should help catch any issues with the DIFs not corresponding to the hardware implementation exactly.
These tests may not live in `sw/device/tests/dif`.

### DIF Development Stages

As part of the DIF Standardisation process, we've decided to establish more concrete DIF lifecycle stages.
These are documented with the [Development Stages]({{< relref "doc/project/development_stages.md" >}}).

In the hardware world, there are checklists for establishing that each stage is complete and the next stage can be moved to.

In software, we don't have to follow the same stability guarantees, because software is much more modifiable.
It makes sense to have some kind of review process, but this should be much more lightweight in the early stages and not significantly burdensome to the associated HW designer.

The current proposal only covers a DIF being written against a single version of its respective hardware IP block.
This specifically excludes how to disambiguate DIFs in the repository that are written against different versions of the same IP block, or writing a single DIF that is compatible with multiple versions of an IP block.

### Signoff Review

The DIF lead author is expected to participate in the hardware IP block's L2 signoff review.
This review can only happen once hardware design and verification are complete, and the DIF itself has reached stage S3.
