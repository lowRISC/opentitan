# Getting started on FPGAs

Do you want to try out the lowRISC chip designs, but don't have a couple thousand or million dollars ready for an ASIC tapeout?
Running lowRISC designs on an FPGA board can be the answer!

{{% toc 3 }}

## Prerequisites

To use the lowRISC Comportable designs on an FPGA you need two things:

* A supported [FPGA board](fpga_boards.md)
* A tool from the FPGA vendor OR a storage device such as a USB stick or MicroSD card

The FPGA vendor tools are required if you intend to build the FPGA bitstream.
The storage device is required if you do not intend to build the FPGA bitstream and simply want to download a released bitfile.

To build the [FPGA bitstream](#create-an-fpga-bitstream), you will need different tools and boards depending on the design/target combinations
Refer to the design documentation for information what exactly is needed.
Follow the install instructions to [prepare the system](install_instructions.md#system-preparation) and to install the [software development tools](install_instructions.md#software-development) and [Xilinx Vivado](install_instructions.md#xilinx-vivado).

To work directly with a [released bitstream](#booting-the-fpga-with-a-storage-device), you will not need any vendors tools other than a compatible storage device and FPGA


## Create an FPGA bitstream

There are two ways to create an FPGA bitstream.

One is to deploy the FPGA auto-build script, and the other is to follow the same steps manually.
The manual process is described below, and the [auto-build script](#fpga-auto-build) is linked after

### Manually Create FPGA bistream

Synthesizing a design for a FPGA board is done with the following commands.

The FPGA build will pull in a program to act as the boot_rom.
This is pulled in from the `sw/boot_rom` directory (see the `parameters:` section of the `top_earlgrey_nexysvideo.core` file)
At the moment there is no check that the `rom.vmem` is up to date, so it is best to follow the instructions to [Build software](getting_started_sw.md) and understand the FPGA's overall software flow

In the following example we synthesize the design for the Nexys Video board using Xilinx Vivado 2018.3.

```console
$ /tools/Xilinx/Vivado/2018.3/settings64.sh
$ cd $REPO_TOP
$ make -C sw SW_DIR=boot_rom clean all
$ fusesoc --cores-root . build lowrisc:systems:top_earlgrey_nexysvideo
```

The resulting bitstream is located at `build/lowrisc_systems_top_earlgrey_nexysvideo_0.1/synth-vivado/lowrisc_systems_top_earlgrey_nexysvideo_0.1.bit`.

### FPGA Auto Build
You can also build an FPGA bitstream by invoking the auto-build process used by the release process.
The auto build script checks for common FPGA errors such as
* The absence of a rom.vmem
* Timing errors

If the build is successful, The resulting bitstream is in the same location.

```console
$ cd $REPO_TOP
$ ./util/fpga/fpga_release.sh arg0
```

## Updating an FPGA bitstream with new ROM

When creating an FPGA bitstream, the existing `rom.vmem` is used to construct the FPGA ROM.
To expedite rom developement however, it is possible to update ROM contents without building another bitstream from scratch.
To do so, the FPGA splice flow is used to load new boot rom contents into FPGA BRAMs and create an embedded FPGA bitstream.
The script assumes there is a pre-generated FPGA bitstream in the build directory at `build/lowrisc_systems_top_earlgrey_nexysvideo_0.1/synth-vivado/lowrisc_systems_top_earlgrey_nexysvideo_0.1.bit`.
The updated `rom.vmem` file is auto generated as part of this flow.

* Usage:
```console
$ cd $REPO_TOP
$ ./util/fpga/splice_nexysvideo.sh
```

The resulting updated bitfile is located at the same place as raw Vivado bitfile with the string `splice.bit` appended.
For example, `build/lowrisc_systems_top_earlgrey_nexysvideo_0.1/synth-vivado/lowrisc_systems_top_earlgrey_nexysvideo_0.1.splice.bit`

## Flash the bitstream onto the FPGA

To flash the bitstream onto the FPGA you need to use either the Vivado GUI or the command line.

### Using the command line

Use the following command to program the FPGA with fusesoc.

```console
$ /tools/Xilinx/Vivado/2018.3/settings64.sh
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

## Booting the FPGA with a storage device

TBD, to be filled in

## Testing the demo design

By default, the FPGA bitstream is built with only the boot rom.
Using this boot rom, the FPGA is able to downloading additional software to the emulated flash, such as the software in the `sw/examples/` and `sw/tests/` directories.
To download additional software, a custom download tool named [spiflash](../../sw/host/spiflash/README.md) is required.
Please follow the linked instructions and build the tool.

Once the tool is built, also build the binary you wish to download.
For the purpose of this demonstration, we will use `sw/examples/hello_world`.
The example below builds the `hello_world` image and flashes it onto the FPGA

```shell
$ cd ${REPO_TOP}
$ make -C sw SW_DIR=examples/hello_world SW_BUILD_DIR=out
$ ./util/spiflash --input=out/sw.bin
$ Show example output
```

The demo hello_world software shows off some capabilities of the design.
See the hello_world [README](../../sw/examples/hello_world/README.md) for more details.

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
$ riscv32-unknown-elf-gdb -ex "target extended-remote :3333" -ex "info reg" sw/boot_rom/boot_rom.elf
```

#### Common operations with GDB

Examine 16 memory words in the hex format starting at 0x200005c0

```console
$ (gdb) x/16xw 0x200005c0
```

Press enter again to print the next 16 words.
Use `help x` to get a description of the command.

If the memory content contains program text it can be disassembled

```console
$ (gdb) disassemble 0x200005c0,0x200005c0+16*4
```

Displaying the memory content can also be delegated to OpenOCD

```console
$ (gdb) monitor mdw 0x200005c0 16
```

Use `monitor help` to get a list of supported commands.

To change the program which is debugged the `file` command can be used.
This will update the symbols which are used to get information about the program.
It is especially useful in the context of our `boot_rom.elf`, which resides in the ROM region, which will eventually jump to a different executable as part of the flash region.

```console
$ (gdb) file sw/examples/hello_world/sw.elf
$ (gdb) disassemble 0x200005c0,0x200005c0+16*4
```

The output of the disassemble should now contain additional information.

## FPGA Bitfile Release and Validation

It is understood that not all users of FPGA wish to install Vivado tools and build a bistream from scratch.
As such, the project will periodically release known-good bitstream files through GitHub tags that users can directly deploy via a [storage device](#booting-the-fpga-with-a-storage-device)

To confirm whether a particular repository state is healthy for release, we invoke an fpga release validation flow.
The validation flow is automated and performs the following steps in order:
* Compile the latest boot_rom and create `rom.vmem`
* Compile the FPGA bistream using the current repository
  * Checks for syntax errors as well as design issues such as combinational loops
  * Checks for FPGA timing issues
  * Checks for any memory initialization failures
* Checks the compiled bitstream is able to [update ROM contents without rebuild](#updating-an-fpga-bitstream-with-new-rom)
* Flashes a connected FPGA with the resulting bitstream
* Invokes the PyTest framework and check FPGA functoinality
  * All tests under `sw/tests` are run
  * All tests under `sw/vendor/riscv_compliance` are run

If the above steps all succeed, the validation flow outputs the current short git ID hash along with a success message.
This hash can either be associated with a release bitfile, or merged into the PR to indicate that a user has run the validation flow.

```console
$ cd $REPO_TOP
$ ./util/fpga/fpga_release.sh arg0 arg1
$ Show sample output
```
