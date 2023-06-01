# Device Software

## Reference Firmware Images

The OpenTitan Reference Firmware Images together make up the Opentitan Reference Firmware Stack.
Different images are used for different boot stages.

The Reference Firmware Images are, in boot order:

1.  The [ROM](./silicon_creator/rom/README.md) (in `sw/device/silicon_creator/rom`), executed at chip reset;
2.  The ROM_EXT (in `sw/device/silicon_creator/rom_ext`), the second stage Silicon Creator code, executed from flash; and

### Testing-only Images

There are also some other standalone firmware images in the repository, which are only used for testing.

- [`sw/device/tests`](./tests/README.md) contains several categories of chip-level tests, including smoke, IP integration, and system-level (use case) tests.

- [`sw/vendor/eembc_coremark`](https://github.com/lowRISC/opentitan/tree/master/sw/vendor/eembc_coremark) contains infrastructure for running the [CoreMark](https://github.com/eembc/coremark) benchmark suite on the OpenTitan device.
- `sw/device/riscv_compliance_support` contains infrastructure so we can run the [RISC-V Compliance](https://github.com/riscv/riscv-compliance) tests on the OpenTitan core.
- `sw/device/sca` contains on-device software used for Side-Channel Analysis.
- `sw/device/prebuilt` contains pre-built Tock images, which may not be up-to-date.
- `sw/device/examples` contains example images, including a simple [Hello World](https://github.com/lowRISC/opentitan/tree/master/sw/device/examples/hello_world).

There are also prototype versions of some of the boot stages, now only used for testing:

- [`sw/device/lib/testing/test_rom`](https://github.com/lowRISC/opentitan/tree/master/sw/device/lib/testing/test_rom) is a previous, testing-only version of the ROM.
- `sw/device/exts` contains software for our prototype second boot stage images.
