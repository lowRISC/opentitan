---
title: "FPGA Setup"
aliases:
    - /doc/ug/getting_started_fpga
---

_Before following this guide, make sure you've followed the [dependency installation and software build instructions]({{< relref "getting_started" >}})._

Do you want to try out OpenTitan, but don't have a couple thousand or million dollars ready for an ASIC tapeout?
Running OpenTitan on an FPGA board can be the answer!

<!-- TODO: Switch all calls to fusesoc and the Verilated system to refer to Meson, once it supports fusesoc. -->

## Prerequisites

To use the OpenTitan on an FPGA you need two things:

* A supported FPGA board
* A tool from the FPGA vendor

Depending on the design/target combination that you want to synthesize you will need different tools and boards.
Refer to the design documentation for information what exactly is needed.

* [Obtain an FPGA board]({{< relref "fpga_boards.md" >}})

## Obtain an FPGA bitstream

To run OpenTitan on an FPGA, you will need an FPGA bitstream.
You can either download the latest bitstream for the ChipWhisperer CW310 board or build it yourself.

### Download a Pre-built Bitstream

If you are using the ChipWhisperer CW310 board with the Xilinx Kintex 7 XC7K410T FPGA, you can download the latest passing [pre-built bitstream](http://storage.googleapis.com/opentitan-bitstreams/master/bitstream-latest.tar.gz). 

For example, to download and unpack the bitstream, run the following:

```console
$ cd $REPO_TOP
$ mkdir -p build-bin/hw/top_earlgrey
$ cd build-bin/hw/top_earlgrey
$ curl https://storage.googleapis.com/opentitan-bitstreams/master/bitstream-latest.tar.gz -o bitstream-latest.tar.gz
$ tar -xvf bitstream-latest.tar.gz
```

By default, the bitstream is built with a version of the boot ROM used for testing (called the _test ROM_; pulled from `sw/device/lib/testing/test_rom`).
There is also a version of the boot ROM used in production (called the _mask ROM_; pulled from `sw/device/silicon_creator/mask_rom`).
This can be spliced into the bitstream to overwrite the testing boot ROM as described in the [FPGA Reference Manual]({{< relref "ref_manual_fpga.md#boot-rom-development" >}}).
However, if you do not want to do the splicing yourself, both versions of the bitstream are available in the download as `*.bit.orig` and `*.bit.splice` (containing the test ROM and the mask ROM respectively).
The metadata for the latest bitstream (the approximate creation time and the associated commit hash) is also available as a text file and can be [downloaded separately](https://storage.googleapis.com/opentitan-bitstreams/master/latest/latest.txt).

### Create an FPGA bitstream

Synthesizing a design for an FPGA board is done with the following commands.

The FPGA build will pull in a program to act as the boot ROM.
This must be built before running the FPGA build.
This is pulled in from the `sw/device/lib/testing/test_rom` directory (see the `parameters:` section of the `hw/top_earlgrey/chip_earlgrey_cw310.core` file).

To build it:
```console
$ cd $REPO_TOP
$ ./meson_init.sh
$ ninja -C build-out all
```

Only the ChipWhisperer CW310 board with the Xilinx Kintex 7 XC7K410T FPGA can fit the whole Earl Grey design.
When working with the Nexys Video FPGA board, the Earl Grey design has to be modified to reduce its size using a script.
```console
$ cd $REPO_TOP
$ ./hw/top_earlgrey/util/top_earlgrey_reduce.py --build
```
The `--build` argument is optional and ensures that the boot ROM is rebuilt for the reduced design.
Alternatively, the boot ROM can be manually regenerated using the previous command.

Next, the actual FPGA implementation can be started.
In the following example we synthesize the Earl Grey design for the ChipWhisperer CW310 board using Xilinx Vivado {{< tool_version "vivado" >}}.
To target the Nexys Video board, replace `cw310` by `nexysvideo` in the instructions below.

```console
$ . /tools/Xilinx/Vivado/{{< tool_version "vivado" >}}/settings64.sh
$ cd $REPO_TOP
$ ./meson_init.sh
$ ninja -C build-out all
$ fusesoc --cores-root . run --flag=fileset_top --target=synth lowrisc:systems:chip_earlgrey_cw310
```
The `fileset_top` flag used above is specific to the OpenTitan project to select the correct fileset.

The resulting bitstream is located at `build/lowrisc_systems_chip_earlgrey_cw310_0.1/synth-vivado/lowrisc_systems_chip_earlgrey_cw310_0.1.bit`.
See the [reference manual]({{< relref "ref_manual_fpga.md" >}}) for more information.

#### Dealing with FPGA Congestion Issues

The default Vivado tool placement may sometimes result in congested FPGA floorplans.
When this happens, the implemenation time and results become unpredictable.
It may become necessary for the user to manually adjust certain placement.
See [this comment](https://github.com/lowRISC/opentitan/pull/8138#issuecomment-916696830) for a thorough analysis of one such situation and what changes were made to improve congestion.

## Connecting the ChipWhisperer CW310 board

The ChipWhisperer CW310 board supports different power options.
It is recommended to power the board via the included DC power adapter.
To this end:
1. Set the *SW2* switch (to the right of the barrel connector) up to the *5V Regulator* option.
1. Set the switch below the barrel connector to the right towards the *Barrel* option.
1. Set the *Control Power* switch (bottom left corner, *SW7*) to the right.
1. Ensure the *Tgt Power* switch (above the fan, *S1*) is set to the right towards the *Auto* option.
1. Plug the DC power adapter into the barrel jack (*J11*) in the top left corner of the board.
1. Use a USB-C cable to connect your PC with the *USB-C Data* connector (*J8*) in the lower left corner on the board.

You can now use `dmesg` to determine which serial ports have been assigned.
They should be named `'/dev/ttyACM*'`, e.g. `/dev/ttyACM1`.
To ensure that you have sufficient access permissions, set up the udev rules as explained in the [Vivado installation instructions]({{< relref "install_vivado" >}}).

## Connecting the Nexys Video board

* Use a Micro USB cable to connect the PC with the *PROG*-labeled connector on the board.
* Use a second Micro USB cable to connect the PC with the *UART*-labled connector on the board.
* After connecting the UART, use `dmesg` to determine which serial port was assigned.
  It should be named `/dev/ttyUSB*`, e.g. `/dev/ttyUSB0`.
* To ensure that you have sufficient access permissions, set up the udev rules as explained in the [Vivado installation instructions]({{< relref "install_vivado" >}}).

## Flash the bitstream onto the FPGA

To flash the bitstream onto the FPGA you need to use either the command line or the Vivado GUI (Nexys Video board only).
Depending on the FPGA device, the flashing itself may take several seconds.
After completion, a message like this should be visible from the UART:

```
Version:    opentitan-snapshot-20191101-1-366-gca61d28
Build Date: 2019-12-13, 13:15:48
Bootstrap requested, initialising HW...
HW initialisation completed, waiting for SPI input...
```

### Using the command line for the ChipWhisperer CW310 board

Use the following command to program the FPGA with the `cw310_loader` tool.

```console
$ cd $REPO_TOP

# If you downloaded the bitstream:
$ ./util/fpga/cw310_loader.py --bitstream build-bin/hw/top_earlgrey/lowrisc_systems_chip_earlgrey_cw310_0.1.bit
# If you built the bitstream yourself:
$ ./util/fpga/cw310_loader.py --bitstream build/lowrisc_systems_chip_earlgrey_cw310_0.1/synth-vivado/lowrisc_systems_chip_earlgrey_cw310_0.1.bit
```

### Using the command line for the Nexys Video board

Use the following command to program the FPGA.

```console
$ . /tools/Xilinx/Vivado/{{< tool_version "vivado" >}}/settings64.sh
$ cd $REPO_TOP
$ util/opentitan-pgm-fpga/opentitan-pgm-fpga xc7a200tsbg484-1 build/lowrisc_systems_chip_earlgrey_nexysvideo/synth-vivado/lowrisc_systems_chip_earlgrey_nexysvideo_0.1.bit
```

If you have having trouble with programming using the command line, try the GUI.

### Using the Vivado GUI for the Nexys Video board

```console
$ . /tools/Xilinx/Vivado/{{< tool_version "vivado" >}}/settings64.sh
$ cd $REPO_TOP
$ make -C build/lowrisc_systems_chip_earlgrey_nexysvideo_0.1/synth-vivado build-gui
```

Now the Vivado GUI opens and loads the project.

* Connect the FPGA board to the PC and turn it on.
* In the navigation on the left, click on *PROGRAM AND DEBUG* > *Open Hardware Manager* > *Open Target* > *Auto Connect*.
* Vivado now enumerates all boards and connects to it.
* Click on *Program Device* in the menu on the left (or at the top of the screen).
* A dialog titled *Program Device* pops up. Select the file `lowrisc_systems_chip_earlgrey_nexysvideo_0.1.bit` as *Bitstream file*, and leave the *Debug probes file* empty.
* Click on *Program* to flash the FPGA with the bitstream.
* The FPGA is ready as soon as the programming finishes.

## Testing the demo design

The `hello_world` demo software shows off some capabilities of the design.
Depending on the FPGA board, a slightly different set of tools and commands is used for running applications.

### Running on the ChipWhisperer CW310 board

To load `hello_world` into the FPGA on the ChipWhisperer CW310 board follow the steps shown below.

1. Generate the bitstream and flash it to the FPGA as described above.
1. Open a serial console (use the device file determined before) and connect.
   Settings: 115200 baud, 8 bits per byte, no software flow-control for sending and receiving data.
   ```console
   $ screen /dev/ttyACM1 115200,cs8,-ixon,-ixoff
   ```
1. Run the loading tool.
   ```console
   $ cd ${REPO_TOP}
   $ ./util/fpga/cw310_loader.py --firmware build-bin/sw/device/examples/hello_world/hello_world_fpga_cw310.bin --set-pll-defaults
   ```

   This should report how the binary is split into frames:
   ```
   CW310 Loader: Attemping to find CW310 FPGA Board:
       No bitstream specified
   Board found, setting PLL2 to 100 MHz
   INFO: Programming firmware file: build-bin/sw/device/examples/hello_world/hello_world_fpga_cw310.bin
   Programming OpenTitan with "build-bin/sw/device/examples/hello_world/hello_world_fpga_cw310.bin"...
   Transferring frame 0x00000000 @ 0x00000000.
   Transferring frame 0x00000001 @ 0x000007D8.
   Transferring frame 0x00000002 @ 0x00000FB0.
   Transferring frame 0x00000003 @ 0x00001788.
   Transferring frame 0x00000004 @ 0x00001F60.
   Transferring frame 0x00000005 @ 0x00002738.
   Transferring frame 0x00000006 @ 0x00002F10.
   Transferring frame 0x80000007 @ 0x000036E8.
   Loading done.
   ```

   and then output like this should appear from the UART:
   ```
   Version:    opentitan-snapshot-20191101-1-4549-g504534121
   Build Date: 2021-03-02, 18:15:49
   Bootstrap requested, initialising HW...
   HW initialisation completed, waiting for SPI input...
   Processing frame #0, expecting #0
   Processing frame #1, expecting #1
   Processing frame #2, expecting #2
   Processing frame #3, expecting #3
   Processing frame #4, expecting #4
   Processing frame #5, expecting #5
   Processing frame #6, expecting #6
   Processing frame #7, expecting #7
   Bootstrap: DONE!
   Boot ROM initialisation has completed, jump into flash!
   Hello World!
   Built at: May 17 2021, 18:44:21
   Watch the LEDs!
   Try out the switches on the board
   or type anything into the console window.
   The LEDs show the ASCII code of the last character.
   GPIO switch #0 changed to 1
   GPIO switch #1 changed to 1
   GPIO switch #2 changed to 1
   GPIO switch #3 changed to 1
   GPIO switch #4 changed to 1
   GPIO switch #5 changed to 1
   GPIO switch #6 changed to 1
   GPIO switch #7 changed to 1
   FTDI control changed. Enable JTAG.
   ```

1. Observe the output both on the board and the serial console. Type any text into the console window.
1. Exit `screen` by pressing CTRL-a k, and confirm with y.

#### Troubleshooting

If the firmware load fails with a message like `Error transferring frame: 0x00000000`, try pressing the "USB RST" button before loading the bitstream.

### Running on the Nexys Video board

In order to load `hello_world` into the FPGA on the Nexys Video board, both the binary and the [loading tool]({{< relref "/sw/host/spiflash/README.md" >}}) must be compiled.
Please follow the steps shown below.

* Generate the bitstream and flash it to the FPGA as described above.
* Open a serial console (use the device file determined before) and connect.
  Settings: 115200 baud, 8N1, no hardware or software flow control.
  ```console
  $ screen /dev/ttyUSB0 115200
  ```
  Note that the Nexsys Video demo program that comes installed on the board runs the UART at 115200 baud as well;
  expect to see different output if that is running.
  This can happen if you connect the serial console before using Vivado to program your new bitstream or you press the *PROG* button that causes the FPGA to reprogram from the code in the on-board SPI flash.
* On the Nexys Video board, press the red button labeled *CPU_RESET*.
* You should see the ROM code report its commit ID and build date.
* Run the loading tool.
  ```console
  $ cd ${REPO_TOP}
  $ ./meson_init.sh
  $ ninja -C build-out sw/device/examples/hello_world/hello_world_export_fpga_nexysvideo
  $ ninja -C build-out sw/host/spiflash/spiflash_export
  $ build-bin/sw/host/spiflash/spiflash --input build-bin/sw/device/examples/hello_world/hello_world_fpga_nexysvideo.bin
  ```

  which should report how the binary is split into frames:

  ```
   Running SPI flash update.
   Image divided into 6 frames.
   frame: 0x00000000 to offset: 0x00000000
   frame: 0x00000001 to offset: 0x000003d8
   frame: 0x00000002 to offset: 0x000007b0
   frame: 0x00000003 to offset: 0x00000b88
   frame: 0x00000004 to offset: 0x00000f60
   frame: 0x80000005 to offset: 0x00001338
   ```

  and then output like this should appear from the UART:
  ```
  Processing frame no: 00000000 exp no: 00000000
  Processing frame no: 00000001 exp no: 00000001
  Processing frame no: 00000002 exp no: 00000002
  Processing frame no: 00000003 exp no: 00000003
  Processing frame no: 00000004 exp no: 00000004
  Processing frame no: 80000005 exp no: 00000005
  bootstrap: DONE!
  INFO: Boot ROM initialisation has completed, jump into flash!
  Hello World! Dec 13 2019 15:06:29
  Watch the LEDs!
  Try out the switches on the board
  or type anything into the console window.
  The LEDs show the ASCII code of the last character.
  GPIO: Switch 7 changed to 1
  FTDI control changed. Enable JTAG
  ```

* Observe the output both on the board and the serial console. Type any text into the console window.
* Exit `screen` by pressing CTRL-a k, and confirm with y.

## Develop with the Vivado GUI

Sometimes it is helpful to use the Vivado GUI to debug a design.
fusesoc makes that easy, with one small caveat: by default fusesoc copies all source files into a staging directory before the synthesis process starts.
This behavior is helpful to create reproducible builds and avoids Vivado modifying checked-in source files.
But during debugging this behavior is not helpful.
The `--no-export` option of fusesoc disables copying the source files into the staging area, and `--setup` instructs fusesoc to not start the synthesis process.

```console
$ # only create Vivado project directory
$ cd $REPO_TOP
$ fusesoc --cores-root . run --flag=fileset_top --target=synth --no-export --setup lowrisc:systems:chip_earlgrey_cw310
```

You can then navigate to the created project directory, and open Vivado
```console
$ . /tools/Xilinx/Vivado/{{< tool_version "vivado" >}}/settings64.sh
$ cd $REPO_TOP/build/lowrisc_systems_chip_earlgrey_cw310_0.1/synth-vivado/
$ vivado
```

Finally, using the tcl console, you can kick off the project setup with
```console
$ source lowrisc_systems_chip_earlgrey_cw310_0.1.tcl
```

## Connect with OpenOCD and debug

To connect the Nexys Video FPGA board with OpenOCD, run the following command

```console
$ cd $REPO_TOP
$ openocd -s util/openocd -f board/lowrisc-earlgrey-nexysvideo.cfg
```

See the [install instructions]({{< relref "install_openocd" >}}) for guidance on installing OpenOCD.

To actually debug through OpenOCD, it must either be connected through telnet or GDB.

### Debug with OpenOCD

The following is an example for using telnet

```console
$ telnet localhost 4444 // or whatever port that is specificed by the openocd command above
$ mdw 0x8000 0x10 // read 16 bytes at address 0x8000
```

### Debug with GDB

An example connection with GDB, which prints the registers after the connection to OpenOCD is established

```console
$ cd $REPO_TOP
$ /tools/riscv/bin/riscv32-unknown-elf-gdb -ex "target extended-remote :3333" -ex "info reg" build-bin/sw/device/lib/testing/test_rom/test_rom_fpga_cw310.elf
```

#### Common operations with GDB

Examine 16 memory words in the hex format starting at 0x200005c0

```console
(gdb) x/16xw 0x200005c0
```

Press enter again to print the next 16 words.
Use `help x` to get a description of the command.

If the memory content contains program text it can be disassembled

```console
(gdb) disassemble 0x200005c0,0x200005c0+16*4
```

Displaying the memory content can also be delegated to OpenOCD

```console
(gdb) monitor mdw 0x200005c0 16
```

Use `monitor help` to get a list of supported commands.

To single-step use `stepi` or `step`

```console
(gdb) stepi
```

`stepi` single-steps an instruction, `step` single-steps a line of source code.
When testing debugging against the hello_world binary it is likely you will break into a delay loop.
Here the `step` command will seem to hang as it will attempt to step over the whole delay loop with a sequence of single-step instructions which may take quite some time!

To change the program which is debugged the `file` command can be used.
This will update the symbols which are used to get information about the program.
It is especially useful in the context of our `rom.elf`, which resides in the ROM region, which will eventually jump to a different executable as part of the flash region.

```console
(gdb) file sw/device/examples/hello_world/sw.elf
(gdb) disassemble 0x200005c0,0x200005c0+16*4
```

The output of the disassemble should now contain additional information.
