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

## Reference Firmware Images

The OpenTitan Reference Firmware Images together make up the Opentitan Reference Firmware Stack.
Different images are used for different boot stages.

The Reference Firmware Images are, in boot order:
1.  The [Mask ROM]({{< relref "sw/device/mask_rom/docs" >}}) (in `sw/device/mask_rom`), executed at chip reset;
2.  The ROM_EXT (in `sw/device/rom_exts`), the second stage Silicon Creator code, executed from flash; and
3.  The [Tock Image]({{< relref "sw/device/tock/README.md" >}}) (in `sw/device/tock`), the Silicon Owner code, also executed from flash.

### Testing-only Images

There are also some other standalone firmware images in the repository, which are only used for testing.

*   [`sw/device/tests`]({{< relref "sw/device/tests/README.md" >}}) contains many standalone smoke test images.
    This directory also contains unit tests for software modules, which are executed on host (not device) systems using [GoogleTest](https://github.com/google/googletest).

*   [`sw/device/benchmarks/coremark`]({{< relref "sw/device/benchmarks/coremark/README.md" >}}) contains infrastructure for running the [CoreMark](https://github.com/eembc/coremark) benchmark suite on the OpenTitan device.
*   `sw/device/riscv_compliance_support` contains infrastructure so we can run the [RISC-V Compliance](https://github.com/riscv/riscv-compliance) tests on the OpenTitan core.
*   `sw/device/sca` contains on-device software used for Side-Channel Analysis.
*   `sw/device/prebuilt` contains pre-built Tock images, which may not be up-to-date.
*   `sw/device/examples` contains example images, including a simple [Hello World]({{< relref "sw/device/examples/hello_world/README.md" >}}).

There are also prototype versions of some of the boot stages, now only used for testing:
*   [`sw/device/boot_rom`]({{< relref "sw/device/boot_rom/README.md" >}}) is a previous, testing-only version of the Mask ROM.
*   `sw/device/exts` contains software for our prototype second boot stage images.

## Firmware Libraries


The OpenTitan repository also contains device libraries which are used within our Reference Firmware Images, and can (and should) be used by other OpenTitan device software.

These are organised into the `sw/device/lib` directory.

*   [`sw/device/lib/base`]({{< relref "sw/device/lib/base/README.md" >}}) contains the Base Libraries, including [freestanding C library headers]({{< relref "sw/device/lib/base/freestanding/README.md" >}}).
    The Base Libraries are simple libraries that can be used by any other OpenTitan device software libraries.
*   [`sw/device/lib/dif`]({{< relref "sw/device/lib/dif/README.md" >}}) contains the [Device Interface Functions]({{< relref "doc/rm/device_interface_functions.md" >}}).
*   [`sw/device/lib/arch`]({{< relref "sw/device/lib/arch/README.md" >}}) contains the libraries to be used on specific device configurations (for instance FPGA, Simulation, etc.).
*   [`sw/device/lib/runtime`]({{< relref "sw/device/lib/runtime/README.md" >}}) contains general libraries for more advanced on-device functionality (including logging, printing, and interacting with the RISC-V core).

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
