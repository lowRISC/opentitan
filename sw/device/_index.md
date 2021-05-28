---
title: "OpenTitan Device Software"
---

## Reference Firmware Images

The OpenTitan Reference Firmware Images together make up the Opentitan Reference Firmware Stack.
Different images are used for different boot stages.

The Reference Firmware Images are, in boot order:

1.  The [Mask ROM]({{< relref "sw/device/silicon_creator/mask_rom/docs" >}}) (in `sw/device/mask_rom`), executed at chip reset;
2.  The ROM_EXT (in `sw/device/silicon_creator/rom_exts`), the second stage Silicon Creator code, executed from flash; and
3.  The [Tock Image]({{< relref "sw/device/tock/README.md" >}}) (in `sw/device/tock`), the Silicon Owner code, also executed from flash.

### Testing-only Images

There are also some other standalone firmware images in the repository, which are only used for testing.

- [`sw/device/tests`]({{< relref "sw/device/tests/README.md" >}}) contains many standalone smoke test images.
  This directory also contains unit tests for software modules, which are executed on host (not device) systems using [GoogleTest](https://github.com/google/googletest).

- [`sw/device/benchmarks/coremark`]({{< relref "sw/device/benchmarks/coremark/README.md" >}}) contains infrastructure for running the [CoreMark](https://github.com/eembc/coremark) benchmark suite on the OpenTitan device.
- `sw/device/riscv_compliance_support` contains infrastructure so we can run the [RISC-V Compliance](https://github.com/riscv/riscv-compliance) tests on the OpenTitan core.
- `sw/device/sca` contains on-device software used for Side-Channel Analysis.
- `sw/device/prebuilt` contains pre-built Tock images, which may not be up-to-date.
- `sw/device/examples` contains example images, including a simple [Hello World]({{< relref "sw/device/examples/hello_world/README.md" >}}).

There are also prototype versions of some of the boot stages, now only used for testing:

- [`sw/device/boot_rom`]({{< relref "sw/device/boot_rom/README.md" >}}) is a previous, testing-only version of the Mask ROM.
- `sw/device/exts` contains software for our prototype second boot stage images.

## Documentation Index

{{% sectionContent %}}
