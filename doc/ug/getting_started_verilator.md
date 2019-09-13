# Getting started with Verilator

## About Verilator

Verilator is a cycle-accurate simulation tool.
It translates synthesizable Verilog code into a simulation program in C++, which is then compiled and executed.

## Prerequisites

_Make sure you followed the install instructions to [prepare the system](install_instructions.md#system-preparation) and to install the [software development tools](install_instructions.md#software-development) and [Verilator](install_instructions.md#verilator)._

## Simulating a design with Verilator

First the simulation needs to built itself.

```console
$ cd $REPO_TOP
$ fusesoc --cores-root . sim --build-only lowrisc:systems:top_earlgrey_verilator
```

Then we need to build software to run on the simulated system.
There are 3 memory types: ROM, RAM and Flash.
By default, the system will first execute out of ROM and then jump to flash.
A program needs to be built for each until ROM functionality for code download is ready

For that purpose compile the demo program with "simulation" settings, which adjusts the frequencies to better match the simulation speed.

```console
$ cd $REPO_TOP/sw/boot_rom
$ make clean && make SIM=1
$ cd $REPO_TOP/sw/hello_world
$ make clean && make SIM=1
```

Now the simulation can be run.
The program listed after `--rominit` and `--flashinit` are loaded into the system's respective memories and start executing immediately.

```console
$ cd $REPO_TOP
$ build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator \
  --rominit=sw/boot_rom/boot_rom.vmem \
  --flashinit=sw/tests/hello_world/hello_world.vmem
```

To stop the simulation press CTRL-c.

## Interacting with the simulated UART

The simulation contains code to create a virtual UART port.
When starting the simulation you should see a message like

```console
UART: Created /dev/pts/11 for uart0. Connect to it with any terminal program, e.g.
$ screen /dev/pts/11
```

Use any terminal program, e.g. `screen` to connect to the simulation.
If you only want to see the program output you can use `cat` instead.

```console
$ # to only see the program output
$ cat /dev/pts/11

$ # to interact with the simulation
$ screen /dev/pts/11
```

You can exit `screen` (in the default configuration) by pressing `CTRL-a k` and confirm with `y`.

## See GPIO output

The simulation includes a DPI module to send all GPIO outputs to a POSIX FIFO file.
The changing output can be observed with

```console
$ cat gpio0
```

Passing input is currently not supported.

## Connect with OpenOCD to the JTAG port

The simulation includes a "virtual JTAG" port to which OpenOCD can connect using its `remote_bitbang` driver.
All necessary configuration files are included in this repository.

Run the simulation, then connect with OpenOCD using the following command.

```console
$ cd $REPO_TOP
$ /tools/openocd/bin/openocd -s util/openocd -f board/lowrisc-earlgrey-verilator.cfg
```

You can also run the debug compliance test suite built into OpenOCD.

```console
$ cd $REPO_TOP
$ /tools/openocd/bin/openocd -s util/openocd -f board/lowrisc-earlgrey-verilator.cfg -c 'init; riscv test_compliance; shutdown'
```
## SPI device test interface

The simulation contains code to monitor the SPI bus and provide a master interface to allow interaction with the `spi_device`.
When starting the simulation you should see a message like

```console
SPI: Created /dev/pts/4 for spi0. Connect to it with any terminal program, e.g.
$ screen /dev/pts/4
NOTE: a SPI transaction is run for every 4 characters entered.
SPI: Monitor output file created at /auto/homes/mdh10/github/opentitan/spi0.log. Works well with tail:
$ tail -f /auto/homes/mdh10/github/opentitan/spi0.log
```

Use any terminal program, e.g. `screen` or `microcom` to connect to the simulation.

```console
$ screen /dev/pts/4
```

Microcom seems less likely to send unexpected control codes when starting:
```console
$ microcom -p /dev/pts/4
```

The terminal will accept (but not echo) characters.
After 4 characters are received a 4-byte SPI packet is sent containing the characters.
The four characters received from the SPI transaction are echoed to the terminal.
The `hello_world` code will print out the bytes received from the SPI port (substituting _ for non-printable characters).
The `hello_world` code initially sets the SPI transmitter to return `SPI!` (so that should echo after the four characters are typed) and when bytes are received it will invert their bottom bit and set them for transmission in the next transfer (thus the Nth set of four characters typed should have an echo of the N-1th set with bottom bit inverted).

The SPI monitor output is written to a file.
It may be monitored with `tail -f` which conveniently notices when the file is truncated on a new run, so does not need restarting between simulations.
The output consists of a textual "waveform" representing the SPI signals.

## USB device test interface


The simulation contains code to exercise and monitor the USB bus and provide a host interface to allow interaction with the `usbdev` and `usbuart` modules.
When starting the simulation you should see a message like

```console
USB: FIFO pipe created at /auto/homes/mdh10/github/opentitan/usb0. Run
$ cat /auto/homes/mdh10/github/opentitan/usb0
to observe the output.
```

The test code currently acts as a host to generate the basic USB control transactions to setup the interface (set the Device ID, read the Device Descriptor), send regular (but not at 1ms spacing) Start-of-Frame packets with incrementing frame number, do an IN bulk transfer from endpoint 1 and occasionally an OUT bulk transfer to endpoint 1.
The code will finish the simulation after a small number of USB Frames if tracing is enabled and a large number if tracing is not enabled.
The test code is written directly in the `usbdpi.c` main loop and is fragile with regards to timing. (See [Issue #NNN](https://github.com/lowRISC/opentitan/issues/NNN))

The test code is sufficient to work with the `usbuart` and `hello_world` program and will display the output characters as they arrive in USB packets and send the string `Hi!` to the simulation, which will be echoed and cause the GPIOs to change.

The test code is sufficient to work with the `usbdev` and `hello_usbdev` program and will configure the interface and send the string `Hi!` to the simulation, which will be written to the UART.

The USB mointor can be configured (in the dpi) to output low level bit events from the USB bus, but by default will display higher level packet information. It outputs to a named pipe like the GPIO.

It can be convenient to monitor both the GPIO and USB outputs in the same terminal window.

```console
$ cd $REPO_TOP
$ cat gpio0 & cat usb0
```

Or:

```console
$ cd $REPO_TOP
$ tail -f gpio0 usb0
```

Because the setup process (connect terminal program to `/dev/pts/` for UART, start monitoring the GPIO and USB named pipes) can take some time the `usbdpi` code has a 7 second sleep (with countdown) when it is called for simulation cycle 0.
This delay starts after all the ptys/pipes/files have been opened but before any action and gives enough time for the correct commands to be started in other terminal windows.

## DPI Source

The I/O interfaces described above are implemented using the DPI interface to Verilator.
The code for these is stored in the repo at `hw/dv/dpi` with a sub-directory for each module.
There should be a fusesoc `.core` file in each sub-directory.

## Generating waveforms

With the `--trace` argument the simulation generates a FST signal trace which can be viewed with Gtkwave (only).
Tracing slows down the simulation by roughly factor of 1000.

```console
$ cd $REPO_TOP
$ build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator --meminit=sw/hello_world/hello_world.vmem --trace
$ gtkwave sim.fst
```
