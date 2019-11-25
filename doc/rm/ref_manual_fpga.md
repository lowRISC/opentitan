---
title: "FPGA Reference Manual"
---

This manual provides additional usage details about the FPGA.
Specifically, it provides instructions on SW development flows and testing procedures.


## Usage Options

There are two ways to use OpenTitan on the FPGA.
- The first is to build the design from scratch using Vivado.
  Refer to the [Getting Started FPGA]({{< relref "doc/ug/getting_started_fpga" >}}) guide for more information.
- The second is to program the FPGA with a released bitfile using storage devices.
  Refer to the [Quickstart Guide]({{< relref "doc/ug/quickstart" >}}) guide for instructions on this approach.

## FPGA SW Development Flow

The FPGA is meant for both boot ROM and general software development.
The flow for each is different, as the boot ROM is meant to be fairly static while general software can change very frequently.

### Boot ROM development

The FPGA bitstream is built after compiling whatever code is sitting in `sw/device/boot_rom`.
This binary is used to initialize internal FPGA memory and is part of the bitstream directly.

To update this content without rebuilding the FPGA, a flow is required to splice a new boot ROM binary into the bitstream.
There are two prerequisites in order for this flow to work:
* The boot ROM during the build process must be correctly inferred by the tool.
  * See [prim_rom](https://github.com/lowRISC/opentitan/blob/master/hw/ip/prim_xilinx/rtl/prim_xilinx_rom.sv).
* The boot ROM's physical location must be fixed.
  * See [placement.xdc](https://github.com/lowRISC/opentitan/blob/master/hw/top_earlgrey/data/placement.xdc).

With these steps in place, a script can be invoked to take a new binary and push its contents into an existing bitfile.
For details, please see the [`splice_nexysvideo.sh` script](https://github.com/lowRISC/opentitan/blob/master/util/fpga/splice_nexysvideo.sh).

See example below:

```console
$ cd $REPO_TOP
$ ./util/fpga/splice_nexysvideo.sh
$ fusesoc --cores-root . pgm lowrisc:systems:top_earlgrey_nexysvideo
```

The script assumes that there is an existing bitfile `build/lowrisc_systems_top_earlgrey_nexysvideo_0.1/synth-vivado/lowrisc_systems_top_earlgrey_nexysvideo_0.1.bit` (this is created after following the steps in [getting_started_fpga]({{< relref "doc/ug/getting_started_fpga" >}})).

The script rebuilds the contents in `sw/devices/boot_rom` and then creates a new bitfile of the same name at the same location.
The original input bitfile is moved to `build/lowrisc_systems_top_earlgrey_nexysvideo_0.1/synth-vivado/lowrisc_systems_top_earlgrey_nexysvideo_0.1.bit.orig`.

The fusesoc command can then be directly invoked to flash the FPGA.

### General Software Development

After building, the FPGA bitstream contains only the boot ROM.
Using this boot ROM, the FPGA is able to load additional software to the emulated flash, such as software in the `sw/device/benchmark`, `sw/device/examples` and `sw/device/tests` directories.
To load additional software, a custom load tool named [spiflash]({{< relref "sw/host/spiflash/README.md" >}}) is required.

Once the tool is built, also build the binary you wish to load.
For the purpose of this demonstration, we will use `sw/device/examples/hello_world`, but it applies to any software image that is able to fit in the emulated flash space.
The example below builds the `hello_world` image and loads it onto the FPGA.
The loading output is also shown.

```console
$ cd ${REPO_TOP}
$ ./meson_init.sh
$ ninja -C build-out/sw/fpga all
$ build-bin/sw/host/spiflash/spiflash \ 
    --input build-bin/sw/device/fpga/examples/hello_world/hello_world.bin

Running SPI flash update.
Image divided into 6 frames.
frame: 0x00000000 to offset: 0x00000000
frame: 0x00000001 to offset: 0x000003d8
frame: 0x00000002 to offset: 0x000007b0
frame: 0x00000003 to offset: 0x00000b88
frame: 0x00000004 to offset: 0x00000f60
frame: 0x80000005 to offset: 0x00001338
```

For more details on the exact operation of the loading flow and how the boot ROM processes incoming data, please refer to the [boot ROM readme]({{< relref "sw/device/boot_rom/README.md" >}}).

## FPGA Testing

To sanity check FPGA functionality, there is a [test script](https://github.com/lowRISC/opentitan/blob/master/test/fpga_manual_test.sh) that can be invoked.
The test script checks the following:
    * FPGA is built without issues.
      * There are no timing violations.
      * There are no resource issues.
      * There is no ROM inference or initialization issue (critical warning synth 8-4445)
      * The ROM splicing script is able to correctly locate the ROM and perform updates
    * Existing sanity tests pass without failures.
      * All current tests under `sw/device/tests`.


In the future, this process will be enhanced to check for the following:
    * RISCV compliance test-suite.
    * Additional self contained tests.

If the user does not wish to build and program the FPGA (for example the quick start flow), the test can also be invoked to assume the FPGA is already programmed.

See sample usage below for a successful test.
`${test}` represents a single test under `sw/device/tests` diretory.

```console
$ cd $REPO_TOP
$ ./test/fpga_manual_test.sh -h

Usage: ./test/fpga_manual_test.sh -u <UART PORT ATTACHED> -n -p.
Example : ./test/fpga_manual_test.sh /dev/ttyUSB0"
-n Controls whether a new fpga bitfile is built
-p Controls whether the existing bitfile at build/lowrisc_systems_top_earlgrey_nexysvideo_0.1
is programmed.

...

$ ./test/fpga_manual_test.sh -u /dev/ttyUSB0 -n -p

Compiling ROM - this is needed in order for the build step below to correctly infer ROM

...

Building FPGA.

...

Splice latest boot ROM and program FPGA

...


Build spiflash tool.

...

Building ${test} binaries

...

Flashing binaries onto FPGA for tests.

...

TESTS PASS!

```
