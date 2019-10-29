# SPI Flash

`spiflash` is a tool used to update the firmware stored in OpenTitan's embedded flash.
The tool resets OpenTitan and signals the boot ROM to enter bootstrap mode
before sending the update payload.

Currently, the tool supports both Verilator and FPGA targets.

## Build instructions for spiflash tool

`spiflash` is written in C++14.

Required packages:

```console
$ sudo apt-get install libssl-dev libftdi1-dev
```

Build command for tool:

```console
$ cd ${REPO_TOP}
$ ./meson-init.sh -r
$ ninja -C build-fpga sw/host/spiflash/spiflash
```

## Setup instructions for Verilator and FPGA
Please refer to [verilator](../../../doc/ug/getting_started_verilator.md) and [fpga](../../../doc/ug/getting_started_verilator.md) docs for more information.

## Build boot ROM and demo program

_If building for verilator, build in `build-verilator` instead._

Build `boot_rom`:
```console
$ cd ${REPO_TOP}
$ ninja -C build-fpga sw/boot_rom/boot_rom.vmem
```

Build the `hello_world` program:
```console
$ cd ${REPO_TOP}
$ ninja -C build-fpga sw/examples/hello_world/hello_world.bin
```

## Run the tool in Verilator

Run Verilator with boot_rom enabled:

```console
$ cd ${REPO_TOP}
$ build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator \
  --rominit=build-verilator/sw/boot_rom/boot_rom.vmem
```

Run spiflash. In this example we use SPI device `/dev/pts/3` as an example.
After the transmission is complete, you should be able to see the hello_world output in the UART console.

```console
$ cd ${REPO_TOP}
$ build-verilator/sw/host/spiflash/spiflash \
  --input=build-verilator/sw/examples/hello_world/hello_world.bin \
  --verilator=/dev/pts/3
```

## Run the tool in FPGA

To run spiflash for an FPGA, the instructions are similar.
There is no requirement to enable the FPGA with ROM.
Note, for FPGA, the tool simply searches for a valid interface to attach.
If there are two FPGAs or multiple valid targets attached at the same time, it is possible for the tool to connect to the incorrect device.

```console
$ cd ${REPO_TOP}
$ build-fpga/sw/host/spiflash/spiflash \
  --input=build-fpga/sw/examples/hello_world/hello_world.bin
```
