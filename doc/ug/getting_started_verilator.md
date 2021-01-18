---
title: Getting started with Verilator
---

## About Verilator

Verilator is a cycle-accurate simulation tool.
It translates synthesizable Verilog code into a simulation program in C++, which is then compiled and executed.

<!-- TODO: Switch all calls to fusesoc and the Verilated system to refer to Meson, once it supports fusesoc. -->

## Prerequisites

_Make sure you followed the install instructions to [prepare the system]({{< relref "install_instructions#system-preparation" >}}) and to install the [software development tools]({{< relref "doc/ug/install_instructions#software-development" >}}) and [Verilator]({{< relref "install_instructions#verilator" >}})._

## Simulating a design with Verilator

First the simulation needs to built itself.

```console
$ cd $REPO_TOP
$ fusesoc --cores-root . run --flag=fileset_top --target=sim --setup --build lowrisc:systems:top_earlgrey_verilator
```
The fsel_top flag used above is specific to the OpenTitan project to select the correct fileset.


Then we need to build software to run on the simulated system.
There are 3 memory types: ROM, RAM and Flash.
By default, the system will first execute out of ROM and then jump to flash.
A program needs to be built for each until ROM functionality for code download is ready.

For that purpose compile the demo program with "simulation" settings, which adjusts the frequencies to better match the simulation speed.
For more information on building software targets refer to the [Software Getting Started Guide]({{< relref "getting_started_sw.md" >}}).

```console
$ cd $REPO_TOP
$ ./meson_init.sh
$ ninja -C build-out all
```

Now the simulation can be run.
The programs listed after `--meminit` are loaded into the system's specified memory and execution is started immediately.

```console
$ cd $REPO_TOP
$ build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator \
  --meminit=rom,build-bin/sw/device/boot_rom/boot_rom_sim_verilator.elf \
  --meminit=flash,build-bin/sw/device/examples/hello_world/hello_world_sim_verilator.elf
```

To stop the simulation press CTRL-c.

## Interact with the simulated UART

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

Note that `screen` will only show output that has been generated after `screen` starts, whilst `cat` will show output that was produced before `cat` started.

You can exit `screen` (in the default configuration) by pressing `CTRL-a k` and confirm with `y`.

If everything is working correctly you should expect to see text like the following from the virtual UART (replacing `/dev/pts/11` with the reported device):

```console
$ cat /dev/pts/11
I00000 boot_rom.c:35] Version:    opentitan-snapshot-20191101-1-1182-g2aedf641
Build Date: 2020-05-13, 15:04:09

I00001 boot_rom.c:44] Boot ROM initialisation has completed, jump into flash!
I00000 hello_world.c:30] Hello World!
I00001 hello_world.c:31] Built at: May 13 2020, 15:27:31
I00002 demos.c:17] Watch the LEDs!
I00003 hello_world.c:44] Try out the switches on the board
I00004 hello_world.c:45] or type anything into the console window.
I00005 hello_world.c:46] The LEDs show the ASCII code of the last character.
```

Instead of interacting with the UART through a pseudo-terminal, the UART output can be written to a log file, or to STDOUT.
This is done by passing the `UARTDPI_LOG_uart0` plus argument ("plusarg") to the verilated simulation at runtime.
To write all UART output to STDOUT, pass `+UARTDPI_LOG_uart0=-` to the simulation.
To write all UART output to a file called `your-log-file.log`, pass `+UARTDPI_LOG_uart0=your-log-file.log`.

A full command-line invocation of the simulation could then look like that:
```console
$ cd $REPO_TOP
$ build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator \
  --meminit=rom,build-bin/sw/device/boot_rom/boot_rom_sim_verilator.elf \
  --meminit=flash,build-bin/sw/device/examples/hello_world/hello_world_sim_verilator.elf \
  +UARTDPI_LOG_uart0=-
```

## Interact with GPIO

The simulation includes a DPI module to map general-purpose I/O (GPIO) pins to two POSIX FIFO files: one for input, and one for output.
Observe the `gpio0-read` file for outputs:

```console
$ cat gpio0-read
```

To drive input pins write to the `gpio0-write` file.
A command consists of the desired state: `h` for high, and `l` for low, and the decimal pin number.
Multiple commands can be issued by separating them with a single space.

```console
$ echo 'h09 l31' > gpio0-write  # Pull the pin 9 high, and pin 31 low.
```


## Connect with OpenOCD to the JTAG port and use GDB

The simulation includes a "virtual JTAG" port to which OpenOCD can connect using its `remote_bitbang` driver.
All necessary configuration files are included in this repository.

Run the simulation, then connect with OpenOCD using the following command.

```console
$ cd $REPO_TOP
$ /tools/openocd/bin/openocd -s util/openocd -f board/lowrisc-earlgrey-verilator.cfg
```

To connect GDB use the following command (noting it needs to be altered to point to the sw binary in use).

```console
$ riscv32-unknown-elf-gdb -ex "target extended-remote :3333" -ex "info reg" \
  build-bin/sw/device/examples/hello_world/hello_world_sim_verilator.elf
```

You can also run the debug compliance test suite built into OpenOCD.

```console
$ cd $REPO_TOP
$ /tools/openocd/bin/openocd -s util/openocd -f board/lowrisc-earlgrey-verilator.cfg -c 'init; riscv test_compliance; shutdown'
```

## SPI device test interface

The simulation contains code to monitor the SPI bus and provide a host interface to allow interaction with the `spi_device`.
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

## Software execution traces

All executed instructions in the loaded software are logged to the file `trace_core_00000000.log`.
The columns in this file are tab separated; change the tab width in your editor if the columns don't appear clearly, or open the file in a spreadsheet application.

## Generating waveforms

With the `--trace` argument the simulation generates a FST signal trace which can be viewed with Gtkwave (only).
Tracing slows down the simulation by roughly factor of 1000.

```console
$ cd $REPO_TOP
$ build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator \
  --meminit=rom,build-bin/sw/device/boot_rom/boot_rom_sim_verilator.elf \
  --meminit=flash,build-bin/sw/device/examples/hello_world/hello_world_sim_verilator.elf \
  --trace
$ gtkwave sim.fst
```
