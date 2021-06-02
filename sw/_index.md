---
title: "OpenTitan Software"
---

This is the landing spot for software documentation within the OpenTitan project.
More description and information can be found within the [Reference Manual]({{< relref "doc/rm" >}}) and [User Guide]({{< relref "doc/ug" >}}) areas.

There are three major parts to the OpenTitan software stack:

*   The _device_ software, which runs on the primary core within the OpenTitan platform chip.
*   The _otbn_ software, which runs on the OTBN cryptographic co-processor within the OpenTitan platform chip.
*   The _host_ software, which is run on a host device and interacts with an OpenTitan device.

We use the term "image" to denote a complete, standalone executable which has been prepared for the OpenTitan platform chip.
This is to differentiate from a "library", which is a collection of functions that are not complete enough to run on their own.

# Device Software

This software runs on the primary core within the OpenTitian platform chip itself.
You can find all the device software in the `sw/device` directory of the repository.

The device software is split into two parts:
*   The reference firmware images, which is the project's reference implementation of the Secure Boot system.
    Not all OpenTitan chips will use exactly the same firmware images.
*   The firmware libraries, which can be used by any software built for the device.

Device software must be written in C, Assembly, or Rust.

# OTBN Software

This software runs on the OTBN cryptographic co-processor within the OpenTitan platform chip.
You can find all the OTBN software in the `sw/otbn` directory of the repository.

This software consists of a number of hand-written assembly routines which can be run on the OTBN co-processor.

Normally, this software can not be run on its own, and the main processor has to set up the data and instructions for the OTBN co-processor before it triggers the start of execution.

OTBN Software must only be written in Assembly.

# Host Software

This software is for host-side use, either in preparing images or interacting with a running OpenTitan platform chip.
You can find all the device software in the `sw/host` directory of the repository.

Host software must be written in C++ or Rust.

## Testing-only Utilities

There are some host-side utilities, which are only used for testing.
*   `sw/host/spiflash` is a tool that can flash a testing image over SPI onto a chip that uses `sw/device/boot_rom` for its reset boot stage.

# Other Documentation

## OpenTitan Software API Documentation {#sw-api-docs}

The [OpenTitan Software API Documentation](/sw/apis/) contains automatically generated documentation for the public software APIs.
This includes the Device Interface Functions (DIFs).

All DIFs are also documented on their respective [Hardware IP Specification]({{< relref "hw" >}})

## Vendored in Code see [Vendor Tool User Guide]({{< relref "doc/ug/vendor_hw.md" >}})

* [CoreMark](https://github.com/eembc/coremark)
* [RISC-V Compliance](https://github.com/riscv/riscv-compliance)
* [GoogleTest](https://github.com/google/googletest)
* [Cryptoc](https://chromium.googlesource.com/chromiumos/third_party/cryptoc/)
* [MPSSE from Chromium](https://chromium.googlesource.com/chromiumos/platform2/+/master/trunks/ftdi)
* [LLVM's Compiler-RT Coverage Profiling Library](https://github.com/llvm/llvm-project/tree/master/compiler-rt)
