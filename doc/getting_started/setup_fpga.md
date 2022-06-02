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
Refer to the design documentation for information on what exactly is needed.

* [Obtain an FPGA board]({{< relref "fpga_boards.md" >}})

## Obtain an FPGA bitstream

To run OpenTitan on an FPGA, you will need an FPGA bitstream.
You can either download the latest bitstream for the ChipWhisperer CW310 board or build it yourself.

### Download a Pre-built Bitstream

If you are using the ChipWhisperer CW310 board with the Xilinx Kintex 7 XC7K410T FPGA, you can download the latest passing [pre-built bitstream](http://storage.googleapis.com/opentitan-bitstreams/master/bitstream-latest.tar.gz).

For example, to download and unpack the bitstream, run the following:

```console
mkdir -p /tmp/bitstream-latest
cd /tmp/bitstream-latest
curl https://storage.googleapis.com/opentitan-bitstreams/master/bitstream-latest.tar.gz -o bitstream-latest.tar.gz
tar -xvf bitstream-latest.tar.gz
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
cd $REPO_TOP
./meson_init.sh
ninja -C build-out all
```

Next, the actual FPGA implementation can be started.
In the following example we synthesize the Earl Grey design for the ChipWhisperer CW310 board using Xilinx Vivado {{< tool_version "vivado" >}}.

```console
. /tools/Xilinx/Vivado/{{< tool_version "vivado" >}}/settings64.sh
cd $REPO_TOP
./meson_init.sh
ninja -C build-out all
fusesoc --verbose --cores-root . run --flag=fileset_top --target=synth lowrisc:systems:chip_earlgrey_cw310
```
The `fileset_top` flag used above is specific to the OpenTitan project to select the correct fileset.

The resulting bitstream is located at `build/lowrisc_systems_chip_earlgrey_cw310_0.1/synth-vivado/lowrisc_systems_chip_earlgrey_cw310_0.1.bit`.
See the [reference manual]({{< relref "ref_manual_fpga.md" >}}) for more information.

#### Dealing with FPGA Congestion Issues

The default Vivado tool placement may sometimes result in congested FPGA floorplans.
When this happens, the implemenation time and results become unpredictable.
It may become necessary for the user to manually adjust certain placement.
See [this comment](https://github.com/lowRISC/opentitan/pull/8138#issuecomment-916696830) for a thorough analysis of one such situation and what changes were made to improve congestion.

#### Opening existing project with the Vivado GUI

Sometimes, it may be desirable to open the generated project in the Vivado GUI for inspection.
To this end, run:

```console
. /tools/Xilinx/Vivado/{{< tool_version "vivado" >}}/settings64.sh
cd $REPO_TOP
make -C build/lowrisc_systems_chip_earlgrey_cw310_0.1/synth-vivado build-gui
```

Now the Vivado GUI opens and loads the project.

#### Develop with the Vivado GUI

Sometimes it is helpful to use the Vivado GUI to debug a design.
fusesoc makes that easy, with one small caveat: by default fusesoc copies all source files into a staging directory before the synthesis process starts.
This behavior is helpful to create reproducible builds and avoids Vivado modifying checked-in source files.
But during debugging this behavior is not helpful.
The `--no-export` option of fusesoc disables copying the source files into the staging area, and `--setup` instructs fusesoc to not start the synthesis process.

```console
# only create Vivado project directory
cd $REPO_TOP
fusesoc --cores-root . run --flag=fileset_top --target=synth --no-export --setup lowrisc:systems:chip_earlgrey_cw310
```

You can then navigate to the created project directory, and open Vivado
```console
. /tools/Xilinx/Vivado/{{< tool_version "vivado" >}}/settings64.sh
cd $REPO_TOP/build/lowrisc_systems_chip_earlgrey_cw310_0.1/synth-vivado/
vivado
```

Finally, using the tcl console, you can kick off the project setup with
```console
source lowrisc_systems_chip_earlgrey_cw310_0.1.tcl
```

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

You can now use the following to monitor output from dmesg:
```console
sudo dmesg -Hw
```
This should show which serial ports have been assigned, or if the board is having trouble connecting to USB.
If `dmesg` reports a problem you can trigger a *USB_RST* with *SW5*.
When properly connected, `dmesg` should identify the board, not show any errors, and the status light should flash.
They should be named `'/dev/ttyACM*'`, e.g. `/dev/ttyACM1`.
To ensure that you have sufficient access permissions, set up the udev rules as explained in the [Vivado installation instructions]({{< relref "install_vivado" >}}).

## Flash the bitstream onto the FPGA

Note: The following examples assume that you have a `~/.config/opentitantool/config` with the proper `--interface` and `--conf` options.
For CW310, its contents would look like:
```
--interface=cw310
--conf=<ABS_PATH_TO_YOUR_CLONE>/sw/host/opentitantool/config/opentitan_cw310.json
```

To flash the bitstream onto the FPGA using `opentitantool`, use the following command:

```console
cd $REPO_TOP

# If you downloaded the bitstream:
bazel run //sw/host/opentitantool load-bitstream /tmp/bitstream-latest/lowrisc_systems_chip_earlgrey_cw310_0.1.bit.orig
# If you built the bitstream yourself:
bazel run //sw/host/opentitantool load-bitstream $(ci/scripts/target-location.sh //hw/bitstream/vivado:fpga_cw310_test_rom)
```

Depending on the FPGA device, the flashing itself may take several seconds.
After completion, a message like this should be visible from the UART:

```
I00000 test_rom.c:81] Version: earlgrey_silver_release_v5-5886-gde4cb1bb9, Build Date: 2022-06-13 09:17:56
I00001 test_rom.c:87] TestROM:6b2ca9a1
I00002 test_rom.c:118] Test ROM complete, jumping to flash!
```

## Testing the demo design

The `hello_world` demo software shows off some capabilities of the design.
To load `hello_world` into the FPGA on the ChipWhisperer CW310 board follow the steps shown below.

1. Generate the bitstream and flash it to the FPGA as described above.
1. Open a serial console (use the device file determined before) and connect.
   Settings: 115200 baud, 8 bits per byte, no software flow-control for sending and receiving data.
   ```console
   screen /dev/ttyACM1 115200,cs8,-ixon,-ixoff
   ```
1. Run `opentitantool`.
   ```console
   cd ${REPO_TOP}
   bazel run //sw/host/opentitantool set-pll # This needs to be done only once.
   bazel build //sw/device/examples/hello_world:hello_world_fpga_cw310_bin
   bazel run //sw/host/opentitantool bootstrap $(ci/scripts/target-location.sh //sw/device/examples/hello_world:hello_world_fpga_cw310_bin)
   ```

   and then output like this should appear from the UART:
   ```
   I00000 test_rom.c:81] Version: earlgrey_silver_release_v5-5886-gde4cb1bb9, Build Date: 2022-06-13 09:17:56
   I00001 test_rom.c:87] TestROM:6b2ca9a1
   I00000 test_rom.c:81] Version: earlgrey_silver_release_v5-5886-gde4cb1bb9, Build Date: 2022-06-13 09:17:56
   I00001 test_rom.c:87] TestROM:6b2ca9a1
   I00002 test_rom.c:118] Test ROM complete, jumping to flash!
   I00000 hello_world.c:66] Hello World!
   I00001 hello_world.c:67] Built at: Jun 13 2022, 14:16:59
   I00002 demos.c:18] Watch the LEDs!
   I00003 hello_world.c:74] Try out the switches on the board
   I00004 hello_world.c:75] or type anything into the console window.
   I00005 hello_world.c:76] The LEDs show the ASCII code of the last character.
   ```

1. Observe the output both on the board and the serial console. Type any text into the console window.
1. Exit `screen` by pressing CTRL-a k, and confirm with y.

### Troubleshooting

If the firmware load fails, try pressing the "USB RST" button before loading the bitstream.

## Connect with OpenOCD and debug

To connect the ChipWhisperer CW310 FPGA board with OpenOCD, run the following command

```console
cd $REPO_TOP
openocd -s util/openocd -f board/lowrisc-earlgrey-cw310.cfg
```

See the [install instructions]({{< relref "install_openocd" >}}) for guidance on installing OpenOCD.

To actually debug through OpenOCD, it must either be connected through telnet or GDB.

### Debug with OpenOCD

The following is an example for using telnet

```console
telnet localhost 4444 // or whatever port that is specificed by the openocd command above
mdw 0x8000 0x10 // read 16 bytes at address 0x8000
```

### Debug with GDB

An example connection with GDB, which prints the registers after the connection to OpenOCD is established

```console
cd $REPO_TOP
/tools/riscv/bin/riscv32-unknown-elf-gdb -ex "target extended-remote :3333" -ex "info reg" build-bin/sw/device/lib/testing/test_rom/test_rom_fpga_cw310.elf
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
