# Getting started on FPGAs

Do you want to try out the lowRISC chip designs, but don't have a couple thousand or million dollars ready for an ASIC tapeout?
Running lowRISC designs on an FPGA board can be the answer!

## Prerequisites

To use the lowRISC Comportable designs on an FPGA you need two things:

* A supported FPGA board
* A tool from the FPGA vendor

Depending on the design/target combination that you want to synthesize you will need different tools and boards.
Refer to the design documentation for information what exactly is needed.

* [Obtain an FPGA board](fpga_boards.html)

Follow the install instructions to [prepare the system](install_instructions.md#system-preparation) and to install the [software development tools](install_instructions.md#software-development) and [Xilinx Vivado](install_instructions.md#xilinx-vivado).

## Create an FPGA bitstream

Synthesizing a design for a FPGA board is done with the following commands.

The FPGA build will pull in a program to act as the boot ROM.
This is pulled in from the `sw/device/boot_rom` directory (see the `parameters:` section of the `hw/top_earlgrey/top_earlgrey_nexysvideo.core` file).
At the moment there is no check that the `rom.vmem` file is up to date, so it is best to follow the instructions to [Build software](getting_started_sw.md) and understand the FPGA's overall software flow

In the following example we synthesize the Earl Grey design for the Nexys Video board using Xilinx Vivado 2018.3.

```console
$ . /tools/xilinx/Vivado/2018.3/settings64.sh
$ cd $REPO_TOP
$ fusesoc --cores-root . build lowrisc:systems:top_earlgrey_nexysvideo
```

The resulting bitstream is located at `build/lowrisc_systems_top_earlgrey_nexysvideo_0.1/synth-vivado/lowrisc_systems_top_earlgrey_nexysvideo_0.1.bit`.
See the [reference manual](ref_manual_fpga.md) for more information.


## Flash the bitstream onto the FPGA

To flash the bitstream onto the FPGA you need to use either the Vivado GUI or the command line.

### Using the command line

Use the following command to program the FPGA with fusesoc.

```console
$ . /tools/xilinx/Vivado/2018.3/settings64.sh
$ cd $REPO_TOP
$ fusesoc --cores-root . pgm lowrisc:systems:top_earlgrey_nexysvideo:0.1
```

Note: `fusesoc pgm` is broken for edalize versions up to (and including) v0.1.3.
You can check the version you're using with `pip3 show edalize`.

### Using the Vivado GUI

```console
$ . /tools/xilinx/Vivado/2018.3/settings64.sh
$ cd $REPO_TOP
$ make -C build/lowrisc_systems_top_earlgrey_nexysvideo_0.1/synth-vivado build-gui
```

Now the Vivado GUI opens and loads the project.

* Connect the FPGA board to the PC and turn it on.
* In the navigation on the left, click on *PROGRAM AND DEBUG* > *Open Hardware Manager* > *Open Target* > *Auto Connect*.
* Vivado now enumerates all boards and connects to it. (Note on Vivado 2018.1 you may get an error the first time and have to do auto connect twice.)
* Click on *Program Device* in the menu on the left (or at the top of the screen).
* A dialog titled *Program Device" pops up. Select the file *lowrisc_systems_top_earlgrey_nexysvideo_0.1.bit* as *Bitstream file*, and leave the *Debug probes file* empty.
* Click on *Program* to flash the FPGA with the bitstream.
* The FPGA is ready as soon as the programming finishes.


## Testing the demo design

The `hello_world` demo software shows off some capabilities of the design.
In order to load `hello_world` into the FPGA, both the binary and the [loading tool](../../sw/host/spiflash) must be compiled.
Please follow the steps below.

```console
$ cd ${REPO_TOP}
$ make -C sw/device SW_DIR=examples/hello_world SW_BUILD_DIR=out clean all
$ make -C sw/host/spiflash clean all
$ ./sw/host/spiflash/spiflash --input=sw/device/out/sw.bin

Running SPI flash update.
Image divided into 6 frames.
frame: 0x00000000 to offset: 0x00000000
frame: 0x00000001 to offset: 0x000003d8
frame: 0x00000002 to offset: 0x000007b0
frame: 0x00000003 to offset: 0x00000b88
frame: 0x00000004 to offset: 0x00000f60
frame: 0x80000005 to offset: 0x00001338
```



* Use a Micro USB cable to connect the PC with the *PROG*-labeled connector on the board.
* Use a second Micro USB cable to connect the PC with the *UART*-labled connector on the board.
* After connecting the UART, use `dmesg` to determine which serial port was assigned. It should be named `/dev/ttyUSB*`, e.g. `/dev/ttyUSB0`.
* Ensure that you have sufficient access permissions to the device, check `ls -l /dev/ttyUSB*`. The udev rules given in the Vivado installation instructions ensure this.
* Generate the bitstream and flash it to the FPGA as described above.
* Open a serial console (use the device file determined before) and connect.
  Settings: 230400 baud, 8N1, no hardware or software flow control.
  ```console
  screen /dev/ttyUSB0 230400
  ```
  Note that the Nexsys Video demo program that comes installed on the
  board runs the UART at 115200 baud so expect to see garbage
  characters if that is running (e.g. you connect the serial console
  before using Vivado to program your new bitstream or you press the
  *PROG* button that causes the FPGA to reprogram from the code in
  the on-board SPI flash)

* On the Nexys Video board, press the red button labeled *CPU_RESET*.
* Observe the output both on the board and the serial console. Type any text into the console window.
* Exit `screen` by pressing CTRL-a k, and confirm with y.

## Develop with the Vivado GUI

Sometimes it is helpful to use the Vivado GUI to debug a design.
fusesoc makes that easy, with one small caveat: by default fusesoc copies all source files into a staging directory before the synthesis process starts.
This behavior is helpful to create reproducible builds and avoids Vivado modifying checked-in source files.
But during debugging this behavior is not helpful.
The `--no-export` option of fusesoc disables copying the source files into the staging area, and `--setup` instructs fusesoc to only create a project file, but not to run the synthesis process.

```console
$ # only create Vivado project file
$ fusesoc --cores-root . build --no-export --setup lowrisc:systems:top_earlgrey_nexysvideo
```

## Connect with OpenOCD and debug

To connect the FPGA with OpenOCD, run the following command

```console
$ cd $REPO_TOP
$ /tools/openocd/bin/openocd -s util/openocd -f board/lowrisc-earlgrey-nexysvideo.cfg
```

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
$ riscv32-unknown-elf-gdb -ex "target extended-remote :3333" -ex "info reg" sw/device/boot_rom/boot_rom.elf
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

To change the program which is debugged the `file` command can be used.
This will update the symbols which are used to get information about the program.
It is especially useful in the context of our `boot_rom.elf`, which resides in the ROM region, which will eventually jump to a different executable as part of the flash region.

```console
(gdb) file sw/device/examples/hello_world/hello_world.elf
(gdb) disassemble 0x200005c0,0x200005c0+16*4
```

The output of the disassemble should now contain additional information.
