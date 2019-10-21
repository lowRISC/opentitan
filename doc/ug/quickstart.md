# Quickstart

The environment variable `$REPO_TOP` is the top-level of the git source tree.

## Simulation with Verilator

_Make sure you followed the install instructions to [prepare the system](install_instructions.md#system-preparation) and to install the [software development tools](install_instructions.md#software-development) and [Verilator](install_instructions.md#verilator)._

Build the simulator and the software and then run the simulation

```console
$ cd $REPO_TOP
$ fusesoc --cores-root . sim --build-only lowrisc:systems:top_earlgrey_verilator
$ make -C sw SIM=1 SW_DIR=boot_rom clean all
$ make -C sw SIM=1 SW_DIR=examples/hello_world clean all
$ build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator --meminit=rom,sw/boot_rom/rom.elf \
$ --meminit=flash,sw/examples/hello_world/sw.elf
```

See the [getting started](getting_started_verilator.md) for a complete guide.

## Running on an FPGA

This description assumes the usage of the Nexys Video board.

_Make sure you followed the install instructions to [prepare the system](install_instructions.md#system-preparation) and to install the [software development tools](install_instructions.md#software-development) and [Xilinx Vivado](install_instructions.md#xilinx-vivado)._

Build the software and the bitstream and then program the board

```console
$ cd $REPO_TOP
$ make -C sw SW_DIR=boot_rom clean all
$ make -C sw SW_DIR=examples/hello_world clean all
$ . /tools/xilinx/Vivado/2018.3/settings64.sh
$ fusesoc --cores-root . build lowrisc:systems:top_earlgrey_nexysvideo
$ fusesoc --cores-root . pgm lowrisc:systems:top_earlgrey_nexysvideo:0.1
```

See the [getting started](getting_started_fpga.md) for a complete guide.
